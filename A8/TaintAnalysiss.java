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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.*;

class TaintFlowGraph {

    private final MultiMap<Pointer, Pointer> successors = Maps.newMultiMap();

    boolean addEdge(Pointer source, Pointer target) {
        return successors.put(source, target);
    }

    Set<Pointer> getSuccsOf(Pointer pointer) {
        return successors.get(pointer);
    }
}

class SinkCallSite {
    CSCallSite callSite;
    Sink sink;

    public SinkCallSite(CSCallSite callSite, JMethod jMethod, Sink sink) {
        this.callSite = callSite;
        this.sink = sink;
    }
}


public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private TaintFlowGraph taintFlowGraph;

    private List<SinkCallSite> sinkCallSite;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        taintFlowGraph = new TaintFlowGraph();
        sinkCallSite = new ArrayList<>();
    }

    public PointsToSet dealSource(Invoke callSite, JMethod m) {
        for (Source source : config.getSources()) {
            if(source.method().getSignature().equals(m.getSignature())) {
                return PointsToSetFactory.make(csManager.getCSObj(emptyContext, manager.makeTaint(callSite, m.getReturnType())));
            }
        }
        return null;
    }

    public void dealSinkCallSite(CSCallSite csCallSite, JMethod jMethod) {
        for (Sink sink : config.getSinks()) {
            if(sink.method().getSignature().equals(jMethod.getSignature())) {
                sinkCallSite.add(new SinkCallSite(csCallSite, jMethod, sink));
            }
        }
    }

    private void addTFGEdge(Pointer source, Pointer target, Type type) {
        if(!taintFlowGraph.getSuccsOf(source).contains(target)) {
            taintFlowGraph.addEdge(source, target);

            source.getPointsToSet().forEach(csObj -> {
                Obj obj = csObj.getObject();
                if(manager.isTaint(obj)) {
                    solver.addWorkList(target, PointsToSetFactory.make(csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(obj), type))));
                }
            });
        }
    }

    public PointsToSet propagate(Pointer pointer, PointsToSet pts) {
        PointsToSet taint = PointsToSetFactory.make();
        pts.objects().filter(obj -> manager.isTaint(obj.getObject())).forEach(taint::addObject);
        if(!taint.isEmpty()) {
            taintFlowGraph.getSuccsOf(pointer).forEach(succPointer -> solver.addWorkList(succPointer, taint));
        }
        return taint;
    }

    public void dealTaintTransfer(CSCallSite csCallSite, JMethod jMethod, CSVar baseP) {
        Context c = csCallSite.getContext();
        for (TaintTransfer taintTransfer : config.getTransfers()) {
            if(taintTransfer.method().getSignature().equals(jMethod.getSignature())) {
                if(taintTransfer.from() == TaintTransfer.BASE && taintTransfer.to() == TaintTransfer.RESULT) {
                    Var lValue = csCallSite.getCallSite().getLValue();
                    addTFGEdge(baseP, csManager.getCSVar(c, lValue), jMethod.getReturnType());

                } else if(taintTransfer.from() >= 0 && taintTransfer.to() == TaintTransfer.BASE) {
                    List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
                    CSVar argP = csManager.getCSVar(c, args.get(taintTransfer.from()));
                    addTFGEdge(argP, baseP, jMethod.getReturnType());

                } else if(taintTransfer.from() >= 0 && taintTransfer.to() == TaintTransfer.RESULT) {
                    List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
                    CSVar argP = csManager.getCSVar(c, args.get(taintTransfer.from()));
                    Var lValue = csCallSite.getCallSite().getLValue();
                    addTFGEdge(argP, csManager.getCSVar(c, lValue), jMethod.getReturnType());
                }
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

//        result.getCSVars().forEach(csVar -> {
//            csVar.getPointsToSet().forEach(csObj -> {
//                if(manager.isTaint(csObj.getObject())) {
//                    taintFlowGraph.getSuccsOf(csVar).forEach(succPointer -> succPointer.getPointsToSet().addObject(csObj));
//                }
//            });
//        });

        sinkCallSite.forEach(scs -> {
            CSCallSite csCallSite = scs.callSite;
            Sink sink = scs.sink;

            List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();

            for (CSObj obj : result.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), args.get(sink.index())))) {
                if(manager.isTaint(obj.getObject())) {
                    taintFlows.add(new TaintFlow(manager.getSourceCall(obj.getObject()), csCallSite.getCallSite(), sink.index()));
                }
            }

        });

        return taintFlows;
    }
}
