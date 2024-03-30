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
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.ir.stmt.Return;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static polyglot.main.Report.cfg;

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

        workList.addAll(icfg.getNodes());
        Fact inFact, outFact;
        List<Node> entryNodes = icfg.entryMethods().map(icfg::getEntryOf).toList();

        while(!workList.isEmpty()) {
            Node node = workList.poll();

            if (!entryNodes.contains(node)) {
                outFact = result.getOutFact(node);
                inFact = result.getInFact(node);

                Set<ICFGEdge<Node>> inEdgesOf = icfg.getInEdgesOf(node);

                for (ICFGEdge<Node> edge : inEdgesOf) {
                    Fact aaa = result.getOutFact(edge.getSource());
                    Fact bbb = analysis.transferEdge(edge, aaa);
                    analysis.meetInto(bbb, inFact);
                }

                result.setInFact(node, inFact);
                boolean tmp = analysis.transferNode(node, inFact, outFact);
                result.setOutFact(node, outFact);

                if (tmp) {
                    for (ICFGEdge<Node> outEdge : icfg.getOutEdgesOf(node)) {
                        Node target = outEdge.getTarget();
                        if(!workList.contains(target)) {
                            workList.add(target);
                        }
                    }
                }

            }
        }
    }
}
