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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private Queue<Stmt> reachableStmts = new ArrayDeque<>();

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if(!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            method.getIR().forEach(stmt -> {
                reachableStmts.add(stmt);
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                List<Var> args = stmt.getInvokeExp().getArgs();
                JMethod m = resolveCallee(null, stmt);

                if(!callGraph.getCalleesOf(stmt).contains(m)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, m));
                    addReachable(m);

                    List<Var> params = m.getIR().getParams();
                    for (int i=0; i<args.size(); i++) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                    }

                    List<Var> returnVars = m.getIR().getReturnVars();
                    Var lValue = stmt.getLValue();
                    if(lValue != null) {
                        for (Var returnVar : returnVars) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(lValue));
                        }
                    }
                }

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
            pointerFlowGraph.getPointers().forEach(pointer -> {
                if(pointer == source) {
                    if(!pointer.getPointsToSet().isEmpty()) {
                        workList.addEntry(target, pointer.getPointsToSet());
                    }
                }
            });
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());

            if(entry.pointer() instanceof VarPtr varPtr) {
                delta.forEach(obj -> {
                    Var var = varPtr.getVar();
                    var.getLoadFields().forEach(loadField -> addPFGEdge(pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(loadField.getLValue())));
                    var.getStoreFields().forEach(storeField -> addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve())));
                    var.getLoadArrays().forEach(loadArray -> addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(loadArray.getLValue())));
                    var.getStoreArrays().forEach(storeArray -> addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()), pointerFlowGraph.getArrayIndex(obj)));
                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pts) {
        PointsToSet delta = new PointsToSet();
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(callSite -> {
            JMethod m = resolveCallee(recv, callSite);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));
            if(!callGraph.getCalleesOf(callSite).contains(m)) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, m));
                addReachable(m);

                List<Var> args = callSite.getInvokeExp().getArgs();
                JMethod jMethod = resolveCallee(recv, callSite);

                List<Var> params = jMethod.getIR().getParams();
                for (int i=0; i<args.size(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                }

                List<Var> returnVars = jMethod.getIR().getReturnVars();
                Var lValue = callSite.getLValue();
                if(lValue != null) {
                    for (Var returnVar : returnVars) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(lValue));
                    }
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
