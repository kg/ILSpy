// Copyright (c) 2011 Kevin Gadd
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy of this
// software and associated documentation files (the "Software"), to deal in the Software
// without restriction, including without limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons
// to whom the Software is furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all copies or
// substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
// INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
// PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE
// FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

using ICSharpCode.Decompiler.FlowAnalysis;
using Mono.Cecil;

namespace ICSharpCode.Decompiler.ILAst
{
	public class SwitchDeoptimizer
	{
	    protected class Candidate {
            public readonly List<ILLabel> CaseLabels = new List<ILLabel>();
            public ILVariable SwitchVariable, IndexVariable;
            public ILLabel DefaultLabel, ExitLabel;
            public ILNode NullCheck, IndexCheck;
            public LookupDict LookupDict;
            public ILExpression SwitchInstruction;
	    }

	    protected class LookupDict {
            public FieldDefinition Field;
            public ILLabel SkipLabel;
            public readonly HashSet<ILNode> Initializer = new HashSet<ILNode>();
        }

        readonly Dictionary<FieldDefinition, LookupDict> lookupDicts = new Dictionary<FieldDefinition,LookupDict>(); 
	    readonly Dictionary<ILVariable, Candidate> candidates = new Dictionary<ILVariable, Candidate>();
        readonly Dictionary<ILVariable, ILVariable> indexToSwitch = new Dictionary<ILVariable, ILVariable>(); 
	    readonly DecompilerContext context;
		
		public SwitchDeoptimizer(DecompilerContext context) {
			this.context = context;
		}

        protected LookupDict GetLookupDict (FieldDefinition field) {
            LookupDict result;
            if (!lookupDicts.TryGetValue(field, out result))
                result = lookupDicts[field] = new LookupDict {
                    Field = field
                };

            return result;
        }

	    protected Candidate GetCandidate (ILVariable switchVariable) {
            Candidate result;
            if (!candidates.TryGetValue(switchVariable, out result))
                result = candidates[switchVariable] = new Candidate {
                    SwitchVariable = switchVariable
                };

            return result;
        }

	    public void DeoptimizeSwitches(ILBlock block) {
	        if (block.Body.Count <= 0)
	            return;

	        var candidatesToProcess = new HashSet<Candidate>();
	        LookupDict currentLookupDict = null;

	        foreach (var _ in block.Body) {
	            var bb = _ as ILBasicBlock;
	            if (bb == null)
	                continue;

	            foreach (var ilNode in bb.Body) {
	                if (currentLookupDict != null) {
	                    if (currentLookupDict.SkipLabel == ilNode)
	                        currentLookupDict = null;
	                    else
	                        currentLookupDict.Initializer.Add(ilNode);
	                }

	                var ile = ilNode as ILExpression;
	                if (ile == null)
	                    continue;

	                if (ile.Code == ILCode.Brtrue) {
	                    var branchTarget = ile.Operand as ILLabel;
	                    if (branchTarget == null)
	                        continue;

	                    var condition = ile.Arguments.FirstOrDefault();
	                    if (condition == null)
	                        continue;

	                    if (condition.Code == ILCode.LogicNot) {
	                        // Detect the initial if (switchExpression == null) goto
	                        // Also detect the TryGetValue invocation
	                        var invertedExpression = condition.Arguments.FirstOrDefault();
	                        if (invertedExpression == null)
	                            continue;

	                        if (invertedExpression.Code == ILCode.Ldloc) {
	                            var switchVariable = invertedExpression.Operand as ILVariable;
	                            var candidate = GetCandidate(switchVariable);

	                            if (candidate.DefaultLabel == null) {
	                                candidate.DefaultLabel = branchTarget;
	                                candidate.NullCheck = ilNode;
	                            }
	                        }
	                        else if (invertedExpression.Code == ILCode.Call) {
	                            var method = invertedExpression.Operand as MethodReference;
	                            if (method == null)
	                                continue;
	                            if (method.Name != "TryGetValue")
	                                continue;
	                            if (method.DeclaringType.Name != "Dictionary`2")
	                                continue;
	                            if (invertedExpression.Arguments.Count < 3)
	                                continue;

	                            var thisExpr = invertedExpression.Arguments[0];
	                            if (thisExpr.Code != ILCode.Ldsfld)
	                                continue;
	                            var thisField = thisExpr.Operand as FieldDefinition;
	                            var lookupDict = GetLookupDict(thisField);
	                            if (lookupDict.SkipLabel == null)
	                                continue;

	                            var keyExpr = invertedExpression.Arguments[1];
                                if (keyExpr.Code != ILCode.Ldloc)
                                    continue;
                                var keyVariable = keyExpr.Operand as ILVariable;
                                if (keyVariable == null)
                                    continue;

                                var candidate = GetCandidate(keyVariable);
                                if (candidate.DefaultLabel == null)
                                    continue;

	                            var resultExpr = invertedExpression.Arguments[2];
                                if (resultExpr.Code != ILCode.Ldloca)
                                    continue;
                                var resultVariable = resultExpr.Operand as ILVariable;
                                if (resultVariable == null)
                                    continue;

                                if ((candidate.DefaultLabel == null) || (candidate.DefaultLabel == branchTarget)) {
                                    candidate.DefaultLabel = branchTarget;
                                    candidate.IndexCheck = ilNode;
                                    candidate.LookupDict = lookupDict;
                                    candidate.IndexVariable = resultVariable;
                                    indexToSwitch[resultVariable] = keyVariable;
                                }
	                        }
	                    } else if (condition.Code == ILCode.Ldsfld) {
	                        // Detect the if (lookupDictionary != null) goto
	                        var prefix = condition.Prefixes.FirstOrDefault();
	                        if ((prefix == null) || (prefix.Code != ILCode.Volatile))
	                            continue;

	                        var lookupDictField = condition.Operand as FieldDefinition;
	                        if (lookupDictField == null)
	                            continue;

	                        currentLookupDict = GetLookupDict(lookupDictField);
	                        currentLookupDict.SkipLabel = branchTarget;
	                        currentLookupDict.Initializer.Add(ilNode);
	                    }
	                } else if (ile.Code == ILCode.Switch) {
                        if (ile.Arguments.Count < 1)
                            continue;

                        var switchExpr = ile.Arguments[0];
                        if (switchExpr.Code != ILCode.Ldloc)
                            continue;
                        var indexVariable = switchExpr.Operand as ILVariable;
                        if (indexVariable == null)
                            continue;

                        ILVariable switchVariable;
                        if (!indexToSwitch.TryGetValue(indexVariable, out switchVariable))
                            continue;

                        var candidate = GetCandidate(switchVariable);
                        candidate.SwitchInstruction = ile;

                        foreach (var l in (ILLabel[]) ile.Operand)
                            candidate.CaseLabels.Add(l);

                        candidatesToProcess.Add(candidate);
	                } else if (ile.Code == ILCode.Br) {
                        // Detect exit branches
                        if (ile == bb.Body[bb.Body.Count - 1]) {
                            var blockLabel = bb.Body[0] as ILLabel;
                            if (blockLabel == null)
                                continue;

                            var candidate = (
                                from c in candidates.Values where 
                                    (c.DefaultLabel == blockLabel) ||
                                    c.CaseLabels.Contains(blockLabel)
                                    select c
                            ).FirstOrDefault();
                            if (candidate == null)
                                continue;

                            var exitLabel = (ILLabel)ile.Operand;

                            if (candidate.ExitLabel == null)
                                candidate.ExitLabel = exitLabel;
                            else if (candidate.ExitLabel != exitLabel)
                                throw new InvalidOperationException();
                        }
	                }
	            }
	        }

            if (candidatesToProcess.Count > 0) {
                foreach (var ctp in candidatesToProcess)
                    DeoptimizeSwitch(block, ctp);
            }
	    }

        protected void DeoptimizeSwitch (ILBlock block, Candidate candidate) {
            var newSwitch = new ILSwitch {
                Condition = new ILExpression(
                    ILCode.Ldloca, candidate.SwitchVariable
                )
            };
            var caseValues = new Dictionary<ILLabel, ILExpression>();

            for (int i = 0, c = block.Body.Count; i < c; i++) {
                var bb = block.Body[i] as ILBasicBlock;
                if (bb == null)
                    continue;

                var blockLabel = bb.Body[0] as ILLabel;
                if (blockLabel == null)
                    continue;

                bool isCase = candidate.CaseLabels.Contains(blockLabel);
                bool isDefault = candidate.DefaultLabel == blockLabel;

                if (isCase || isDefault) {
                    var newBlock = new ILBasicBlock();
                    newBlock.Body.Add(blockLabel);
                    for (int k = 1; k < bb.Body.Count - 1; k++)
                        newBlock.Body.Add(bb.Body[k]);
                    newBlock.Body.Add(new ILExpression(ILCode.LoopOrSwitchBreak, null));

                    var body = new List<ILNode>();
                    body.Add(newBlock);

                    List<ILExpression> values = null;
                    if (isCase) {
                        values = new List<ILExpression>();
                        values.Add(caseValues[blockLabel]);
                    }

                    var entryGoto = new ILExpression(ILCode.Br, blockLabel);

                    newSwitch.CaseBlocks.Add(new ILSwitch.CaseBlock {
                        Body = body,
                        ExtendedValues = values,
                        EntryGoto = entryGoto,
                    });

                    block.Body.RemoveAt(i);
                    i--;
                    c--;
                }

                for (int j = 1, bc = bb.Body.Count; j < bc; j++) {
                    bool remove = false;
                    ILNode replacement = null;
                    var node = bb.Body[j];
                    var expression = node as ILExpression;

                    remove |= (node == candidate.NullCheck);
                    remove |= (node == candidate.IndexCheck);
                    
                    // Remove specific gotos
                    if (
                        (expression != null) &&
                        (expression.Code == ILCode.Br)
                    ) {
                        var branchTarget = expression.Operand as ILLabel;
                        if (candidate.CaseLabels.Contains(branchTarget))
                            remove = true;
                        else if (candidate.DefaultLabel == branchTarget)
                            remove = true;
                    }

                    // Remove initializer instructions for the lookup dictionary
                    if (candidate.LookupDict.Initializer.Contains(node)) {
                        remove = true;

                        // If it's a dict.Add() call we need to capture the arguments
                        var ile = node as ILExpression;
                        if (
                            (ile != null) && 
                            (ile.Code == ILCode.Call) &&
                            (ile.Arguments.Count == 3) &&
                            (((MethodReference)ile.Operand).Name == "Add")
                        ) {
                            var key = ile.Arguments[1];
                            var caseIndex = Convert.ToInt32(ile.Arguments[2].Operand);
                            var caseLabel = candidate.CaseLabels[caseIndex];

                            caseValues[caseLabel] = key;
                        }
                    }

                    // Replace the original switch instruction with the ILSwitch node
                    //  that we're constructing
                    if (candidate.SwitchInstruction == node) {
                        remove = true;
                        replacement = newSwitch;
                    }

                    if (remove) {
                        if (replacement != null) {
                            bb.Body[j] = replacement;
                        } else if (j == bc) {
                            if (candidate.ExitLabel == null)
                                throw new InvalidOperationException();

                            bb.Body[j] = new ILExpression(ILCode.Br, candidate.ExitLabel);
                        } else {
                            bb.Body.RemoveAt(j);
                            j--;
                            bc--;
                        }
                    }
                }
            }
        }
	}
}
