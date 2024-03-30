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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        LValue lValue;
        RValue rValue;
        If ifStmt;
        SwitchStmt switchStmt;
        Edge.Kind deadEdgeKind;
        Var switchVar;
        for(Stmt stmt : cfg) {
            if(deadCode.contains(stmt)) {
                continue;
            }
            if(stmt != cfg.getEntry() && cfg.getPredsOf(stmt).size() == 0) {
                getAllDeadCodeSucc(cfg, stmt, deadCode);
            } else if(stmt instanceof AssignStmt) {
                lValue = ((AssignStmt) stmt).getLValue();
                rValue = ((AssignStmt) stmt).getRValue();
                if (lValue instanceof Var && !liveVars.getResult(stmt).contains((Var) lValue) && hasNoSideEffect(rValue)) {
                    deadCode.add(stmt);
                }
            } else if(stmt instanceof If) {
                ifStmt = (If) stmt;
                Value evaluate = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(stmt));
                if(evaluate.isConstant()) {
                    if(evaluate.getConstant() == 1) {
                        deadEdgeKind = Edge.Kind.IF_FALSE;
                    } else {
                        deadEdgeKind = Edge.Kind.IF_TRUE;
                    }
                    Set<Edge<Stmt>> outEdgesOf = cfg.getOutEdgesOf(stmt);
                    for (Edge<Stmt> edge : outEdgesOf){
                        if(edge.getKind() == deadEdgeKind) {
                            getAllDeadCodeSucc(cfg, edge.getTarget(), deadCode);
                            break;
                        }
                    }
                }
            } else if(stmt instanceof SwitchStmt) {
                switchStmt = (SwitchStmt) stmt;
                switchVar = switchStmt.getVar();

                if(constants.getResult(stmt).get(switchVar).isConstant()) {
                    int switchConst = constants.getResult(stmt).get(switchVar).getConstant();
                    List<Pair<Integer, Stmt>> caseTargets = switchStmt.getCaseTargets();
                    for (Pair<Integer, Stmt> pair : caseTargets) {
                        if(pair.first() != switchConst) {
                            getAllDeadCodeSucc(cfg, pair.second(), deadCode);
                        }
                    }

                    if(switchStmt.getCaseValues().contains(switchConst)) {
                        Stmt defaultTarget = switchStmt.getDefaultTarget();
                        getAllDeadCodeSucc(cfg, defaultTarget, deadCode);
                    }
                }
            }
        }

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }


    private void getAllDeadCodeSucc(CFG<Stmt> cfg, Stmt stmt, Set<Stmt> deadCode) {
        if(stmt != cfg.getEntry() && stmt != cfg.getExit()) {
            Set<Stmt> succsOf = cfg.getSuccsOf(stmt);
            Set<Stmt> predsOf = cfg.getPredsOf(stmt);
            if (predsOf.size() == 1 || deadCode.containsAll(predsOf)) {
                deadCode.add(stmt);
                for (Stmt succStmt : succsOf) {
                    getAllDeadCodeSucc(cfg, succStmt, deadCode);
                }
            }
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
