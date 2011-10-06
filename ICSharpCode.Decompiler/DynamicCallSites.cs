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

using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using ICSharpCode.Decompiler.FlowAnalysis;
using Mono.Cecil;

namespace ICSharpCode.Decompiler.ILAst {
    public class DynamicCallSites {
        public readonly DecompilerContext Context;

        public DynamicCallSites (DecompilerContext context) {
            Context = context;
        }

        public static bool IsCallSite (TypeReference type) {
            if (type.FullName.Contains("Runtime.CompilerServices.CallSite"))
                return true;

            return false;
        }

        public static bool IsCallSiteBinder (TypeReference type) {
            if (type.FullName.Contains("Runtime.CompilerServices.CallSiteBinder"))
                return true;

            return false;
        }

        public static bool IsCallSiteTarget (TypeReference type) {
            var declaringType = type as IGenericInstance;

            if (
                (declaringType != null) &&
                (declaringType.GenericArguments.Count > 1) &&
                IsCallSite(declaringType.GenericArguments[0])
            ) {
                return true;
            }

            return false;
        }

        public static bool IsCallSiteStorage (FieldReference field) {
            var declaringType = field.DeclaringType;

            if (
                field.Name.Contains("__Site") &&
                declaringType.FullName.Contains("__SiteContainer")
            ) {
                return true;
            }

            return false;
        }

        /// <summary>
        /// Finds individual instructions within the block that represent higher level concepts related to dynamic call sites.
        /// This enables FindDynamicCallSites to locate and transform call sites in a single pass.
        /// </summary>
        public bool AnalyzeInstructions(List<ILNode> body, ILExpression expr, int pos) {
            bool result = false;

            var newInstruction = AnalyzeInstruction(expr, ref result);
            if (newInstruction != expr)
                body[pos] = newInstruction;

            return result;
        }

        protected ILExpression AnalyzeInstruction (ILExpression expr, ref bool modified) {
            var result = expr;

            switch (expr.Code) {
                case ILCode.Ldsfld: {
                    var field = expr.Operand as FieldReference;
                    if (IsCallSiteStorage(field)) {
                        result = new ILExpression(
                            ILCode.GetCallSite, expr.Operand, expr.Arguments
                        );
                        modified = true;
                    }

                    break;
                }
                case ILCode.Stsfld: {
                    var field = expr.Operand as FieldReference;
                    if (
                        (expr.Arguments[0].Code == ILCode.Call) &&
                        IsCallSiteStorage(field)
                    ) {
                        var method = expr.Arguments[0].Operand as MethodReference;
                        if (IsCallSite(method.DeclaringType) && (method.Name == "Create")) {
                            result = new ILExpression(
                                ILCode.CreateCallSite, expr.Operand, expr.Arguments
                            );
                            modified = true;
                        }
                    }

                    break;
                }
                case ILCode.Call: {
                    var method = expr.Operand as MethodReference;
                    if (IsCallSiteBinder(method.ReturnType)) {
                        result = new ILExpression(
                            ILCode.GetCallSiteBinder, expr.Operand, expr.Arguments
                        );
                        modified = true;
                    }

                    break;
                }
                case ILCode.Callvirt: {
                    // Detect SiteContainer.callSite.Target.Invoke(callSite, ...)
                    var method = expr.Operand as MethodReference;
                    if (IsCallSiteTarget(method.DeclaringType)) {
                        result = new ILExpression(
                            ILCode.InvokeCallSiteTarget, expr.Operand, expr.Arguments
                        );
                        modified = true;
                    }

                    break;
                }
            }

            for (int i = 0, c = result.Arguments.Count; i < c; i++) {
                var arg = result.Arguments[i];
                var newArg = AnalyzeInstruction(arg, ref modified);

                if (newArg != arg)
                    result.Arguments[i] = newArg;
            }

            return result;
        }
    }
}
