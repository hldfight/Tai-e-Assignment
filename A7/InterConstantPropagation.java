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

import org.checkerframework.checker.units.qual.A;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import soot.util.Cons;

import java.util.*;
import java.util.concurrent.BrokenBarrierException;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Map<Var, HashSet<Var>> allVarAliases;

    private Map<JField, HashSet<StoreField>>  staticFieldStore;

    private Map<JField, HashSet<LoadField>>  staticFieldLoad;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);

        allVarAliases = new HashMap<>();

        for (Var base : pta.getVars()) {
            for(Var var : pta.getVars()) {
                for (Obj obj : pta.getPointsToSet(base)) {
                    if (pta.getPointsToSet(var).contains(obj)) {
                        HashSet<Var> baseAliases = allVarAliases.getOrDefault(base, new HashSet<>());
                        baseAliases.add(var);
                        allVarAliases.put(base, baseAliases);
                        break;
                    }
                }
            }
        }

        staticFieldStore = new HashMap<>();
        staticFieldLoad = new HashMap<>();
        icfg.forEach(stmt -> {
            if(stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField jField = storeField.getFieldRef().resolve();
                HashSet<StoreField> storeFields = staticFieldStore.getOrDefault(jField, new HashSet<>());
                storeFields.add(storeField);
                staticFieldStore.put(jField, storeFields);
            }
            if(stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField jField = loadField.getFieldRef().resolve();
                HashSet<LoadField> loadFields = staticFieldLoad.getOrDefault(jField, new HashSet<>());
                loadFields.add(loadField);
                staticFieldLoad.put(jField, loadFields);
            }
        });

    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if(stmt instanceof LoadField loadField && ConstantPropagation.canHoldInt(loadField.getLValue())) {
            Var lVar = loadField.getLValue();
            if(loadField.isStatic()) {
                JField resolve = loadField.getFieldRef().resolve();

                CPFact gen = new CPFact();
                CPFact inTmp = in.copy();

                HashSet<StoreField> storeFields = staticFieldStore.getOrDefault(resolve, new HashSet<>());
                DataflowResult<Stmt, CPFact> dataFlowResult = this.solver.getResult();
                Value resValue = null;
                for (StoreField storeField : storeFields) {
                    resValue = cp.meetValue(resValue, dataFlowResult.getOutFact(storeField).get(storeField.getRValue()));
                }

                if(resValue != null) {
                    gen.update(lVar, resValue);
                    inTmp.remove(lVar);
                }

                boolean isChange = out.copyFrom(gen);
                return out.copyFrom(inTmp) || isChange;

            } else {

                CPFact gen = new CPFact();
                CPFact inTmp = in.copy();

                Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
                JField loadFieldRef = loadField.getFieldRef().resolve();

                Value resValue = null;
                DataflowResult<Stmt, CPFact> dataFlowResult = this.solver.getResult();
                for (Var var : allVarAliases.getOrDefault(base, new HashSet<>())) {
                    for (StoreField storeField : var.getStoreFields()) {
                        if(storeField.getFieldRef().resolve() == loadFieldRef) {
                            resValue = cp.meetValue(resValue, dataFlowResult.getOutFact(storeField).get(storeField.getRValue()));
                        }
                    }
                }

                if(resValue != null) {
                    gen.update(lVar, resValue);
                    inTmp.remove(lVar);
                }

                boolean isChange = out.copyFrom(gen);
                return out.copyFrom(inTmp) || isChange;

            }
        } else if(stmt instanceof LoadArray loadArray && ConstantPropagation.canHoldInt(loadArray.getLValue())) {

            Var lVar = loadArray.getLValue();

            CPFact gen = new CPFact();
            CPFact inTmp = in.copy();

            Var base = loadArray.getArrayAccess().getBase();
            Value loadIndexValue = in.get(loadArray.getArrayAccess().getIndex());

            Value resValue = null;
            DataflowResult<Stmt, CPFact> dataFlowResult = this.solver.getResult();

            for(Var var : allVarAliases.getOrDefault(base, new HashSet<>())) {
                for (StoreArray storeArray : var.getStoreArrays()) {
                    Value storeIndexValue = dataFlowResult.getInFact(storeArray).get(storeArray.getArrayAccess().getIndex());
                    if((loadIndexValue.isConstant() && storeIndexValue.isConstant() && storeIndexValue.getConstant() == loadIndexValue.getConstant()) || (loadIndexValue.isConstant() && storeIndexValue.isNAC()) || (loadIndexValue.isNAC() && storeIndexValue.isConstant()) || (loadIndexValue.isNAC() && storeIndexValue.isNAC()) ) {
                        resValue = cp.meetValue(resValue, dataFlowResult.getOutFact(storeArray).get(storeArray.getRValue()));
                    }
                }
            }

            if(resValue != null) {
                gen.update(lVar, resValue);
                inTmp.remove(lVar);
            }

            boolean isChange = out.copyFrom(gen);
            return out.copyFrom(inTmp) || isChange;

        } else if(stmt instanceof StoreField storeField) {
            boolean isChange = cp.transferNode(stmt, in, out);
            if(!storeField.isStatic()) {
                if (isChange) {
                    Var base = ((InstanceFieldAccess) storeField.getFieldAccess()).getBase();
                    for (Var var : allVarAliases.getOrDefault(base, new HashSet<>())) {
                        for (LoadField loadField : var.getLoadFields()) {
                            this.solver.addWorkList(loadField);
                        }
                    }
                }
            } else {
                // 不重要
                if (isChange) {
                    HashSet<LoadField> loadFields = staticFieldLoad.getOrDefault(storeField.getFieldRef().resolve(), new HashSet<>());
                    for (LoadField loadField : loadFields) {
                        this.solver.addWorkList(loadField);
                    }
                }
            }
            return isChange;
        } else if(stmt instanceof StoreArray storeArray) {
            boolean isChange = cp.transferNode(stmt, in, out);
            if(isChange) {
                Var base = storeArray.getArrayAccess().getBase();
                for (Var var : allVarAliases.getOrDefault(base, new HashSet<>())) {
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        this.solver.addWorkList(loadArray);
                    }
                }
            }
            return isChange;
        }
        else {
            return cp.transferNode(stmt, in, out);
        }

    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact outTmp = out.copy();
        Optional<LValue> def = edge.getSource().getDef();
        if(def.isPresent()) {
            if(def.get() instanceof Var var) {
                outTmp.remove(var);
            }
        }

        return outTmp;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact outTmp = callSiteOut.copy();
        CPFact cpFact = new CPFact();

        List<Var> params = edge.getCallee().getIR().getParams();
        if(edge.getSource() instanceof Invoke invokeStmt) {
            List<Var> args = invokeStmt.getInvokeExp().getArgs();
            for (int i = 0; i<params.size(); i++) {
                cpFact.update(params.get(i), outTmp.get(args.get(i)));
            }
        }
        return cpFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact cpFact = new CPFact();

        Collection<Var> returnVars = edge.getReturnVars();
        List<Value> values = returnVars.stream().map(returnOut::get).toList();
        if(values.size() > 0) {
            Value resultValue = values.get(0);
            for(int i=1; i<values.size(); i++) {
                resultValue = cp.meetValue(resultValue, values.get(i));
            }

            Optional<LValue> def = edge.getCallSite().getDef();
            if(def.isPresent() && def.get() instanceof Var sourceValue) {
                cpFact.update(sourceValue, resultValue);
            }
        }

        return cpFact;
    }
}
