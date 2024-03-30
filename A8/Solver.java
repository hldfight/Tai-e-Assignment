/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if(!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().forEach(stmt -> {
                StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(csManager.getCSObj(heapContext, obj)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(csManager.getStaticField(stmt.getFieldRef().resolve()),  csManager.getCSVar(context, stmt.getLValue()));
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                dealCallSite(stmt, null, null, context);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            if(!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            PointsToSet taint = taintAnalysis.propagate(entry.pointer(), entry.pointsToSet());
            delta.addAll(taint);

            if(entry.pointer() instanceof CSVar varPtr) {
                delta.forEach(obj -> {
                    Var var = varPtr.getVar();
                    var.getLoadFields().forEach(loadField -> addPFGEdge(csManager.getInstanceField(obj, loadField.getFieldRef().resolve()), csManager.getCSVar(varPtr.getContext(), loadField.getLValue())));
                    var.getStoreFields().forEach(storeField -> addPFGEdge(csManager.getCSVar(varPtr.getContext(), storeField.getRValue()), csManager.getInstanceField(obj, storeField.getFieldRef().resolve())));
                    var.getLoadArrays().forEach(loadArray -> addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(varPtr.getContext(), loadArray.getLValue())));
                    var.getStoreArrays().forEach(storeArray -> addPFGEdge(csManager.getCSVar(varPtr.getContext(), storeArray.getRValue()), csManager.getArrayIndex(obj)));
                    processCall(varPtr, obj);
                });
            }
        }
        System.out.println('s');
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pts) {
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet ptn = pointer.getPointsToSet();
        if(!pts.isEmpty()) {
            pts.objects().filter(obj -> !ptn.contains(obj)).forEach(obj -> {
                ptn.addObject(obj);
                delta.addObject(obj);
            });
        }
        if(!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(succPointer -> workList.addEntry(succPointer, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        Var var = recv.getVar();
        Context c = recv.getContext();
        var.getInvokes().forEach(callSite -> {
            dealCallSite(callSite, recv, recvObj, c);
        });
    }

    private void dealCallSite(Invoke callSite, CSVar recv, CSObj recvObj, Context c) {

        JMethod jMethod = resolveCallee(recvObj, callSite);
        if(jMethod != null) {
            CSCallSite csCallSite = csManager.getCSCallSite(c, callSite);
            Context ct;
            if(recvObj == null) {
                ct = contextSelector.selectContext(csCallSite, jMethod);
            } else {
                ct = contextSelector.selectContext(csCallSite, recvObj, jMethod);
                workList.addEntry(csManager.getCSVar(ct, jMethod.getIR().getThis()), PointsToSetFactory.make(recvObj));
            }
            CSMethod csMethod = csManager.getCSMethod(ct, jMethod);

            if(!callGraph.getCalleesOf(csCallSite).contains(csMethod)) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), csCallSite, csMethod));
                addReachable(csMethod);

                List<Var> args = callSite.getInvokeExp().getArgs();
                List<Var> params = jMethod.getIR().getParams();
                for (int i=0; i<args.size(); i++) {
                    addPFGEdge(csManager.getCSVar(c, args.get(i)), csManager.getCSVar(ct, params.get(i)));
                }

                List<Var> returnVars = jMethod.getIR().getReturnVars();
                Var lValue = callSite.getLValue();
                if(lValue != null) {
                    for (Var returnVar : returnVars) {
                        addPFGEdge(csManager.getCSVar(ct, returnVar), csManager.getCSVar(c, lValue));
                    }
                    PointsToSet pts = taintAnalysis.dealSource(callSite, jMethod);
                    if(pts != null) {
                        workList.addEntry(csManager.getCSVar(c, lValue), pts);
                    }
                }

                taintAnalysis.dealTaintTransfer(csCallSite, jMethod, recv);
                taintAnalysis.dealSinkCallSite(csCallSite, jMethod);

            }
        }
    }

    public void addWorkList(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
