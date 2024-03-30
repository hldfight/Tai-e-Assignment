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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.util.collection.SetQueue;
import soot.jimple.internal.AbstractNewArrayExpr;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;


    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        this.workList = new ArrayDeque<>();
    }

    public DataflowResult<Node, Fact> getResult() {
        return this.result;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        List<Node> entryNodes = icfg.entryMethods().map(icfg::getEntryOf).toList();
        for (Node node :
                icfg) {
            if(entryNodes.contains(node)) {
                result.setOutFact(node, analysis.newBoundaryFact(node));
            } else {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }

    }

    private void doSolve() {

        for(Node node : icfg) {
            workList.add(node);
        }
        Fact inFact, outFact;
        List<Node> entryNodes = icfg.entryMethods().map(icfg::getEntryOf).toList();

        while(!workList.isEmpty()) {
            Node node = workList.poll();

            if (!entryNodes.contains(node)) {
                outFact = result.getOutFact(node);
                inFact = result.getInFact(node);

                Set<ICFGEdge<Node>> inEdgesOf = icfg.getInEdgesOf(node);

                for (ICFGEdge<Node> edge : inEdgesOf) {
                    Fact f1 = result.getOutFact(edge.getSource());
                    Fact f2 = analysis.transferEdge(edge, f1);
                    analysis.meetInto(f2, inFact);
                }

                result.setInFact(node, inFact);
                boolean tmp = analysis.transferNode(node, inFact, outFact);
                result.setOutFact(node, outFact);

                if (tmp) {
                    for (ICFGEdge<Node> outEdge : icfg.getOutEdgesOf(node)) {
                        addWorkList(outEdge.getTarget());
                    }
                }

            }
        }
    }

    public void addWorkList(Node node) {
        workList.add(node);
    }
}
