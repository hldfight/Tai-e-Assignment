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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.Assignment;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import polyglot.ast.Assign;
import polyglot.ast.Expr;
import polyglot.ast.Initializer;
import polyglot.ast.Variable;
import soot.JastAddJ.MethodAccess;
import soot.jimple.IfStmt;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static pascal.taie.ir.exp.ArithmeticExp.*;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        List<Var> params = cfg.getIR().getParams();
        CPFact cpFact = new CPFact();
        for (Var var : params) {
            if(canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> factVars = fact.keySet();
        Set<Var> targetVars = target.keySet();
        if(!factVars.isEmpty()) {
            Set<Var> sameVars = factVars.stream().filter(targetVars::contains).collect(Collectors.toSet());
            Iterator<Map.Entry<Var, Value>> iterator = fact.entries().iterator();
            Var key;
            while(iterator.hasNext()) {
                key = iterator.next().getKey();
                if(sameVars.contains(key)) {
                    target.update(key, meetValue(fact.get(key), target.get(key)));
                } else {
                    target.copyFrom(fact);
                }
            }
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if(v1.isUndef()) {
            return v2;
        }
        if(v2.isUndef()) {
            return v1;
        }
        if(v1 == v2) {
            return v1;
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact gen = new CPFact();
        CPFact inTmp = in.copy();
        if(stmt instanceof DefinitionStmt) {
            DefinitionStmt assign = (DefinitionStmt) stmt;
            LValue lValue = assign.getLValue();
            RValue rValue = assign.getRValue();
            if(lValue instanceof Var && canHoldInt((Var) lValue)) {
                if(rValue instanceof IntLiteral) {
                    gen.update((Var)lValue, Value.makeConstant(((IntLiteral) rValue).getValue()));
                } else if(rValue instanceof Var) {
                    gen.update((Var)lValue, in.get((Var)rValue));
                } else if(rValue instanceof BinaryExp) {
                    gen.update((Var)lValue, evaluate(rValue, in));
                } else {
                    gen.update((Var)lValue, Value.getNAC());
                }
                inTmp.remove((Var)lValue);
            }
            boolean isChange = out.copyFrom(gen);
            return out.copyFrom(inTmp) || isChange;
        } else {
            return out.copyFrom(inTmp);
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        Value v1 = in.get(((BinaryExp) exp).getOperand1());
        Value v2 = in.get(((BinaryExp) exp).getOperand2());
        BinaryExp.Op operator = ((BinaryExp) exp).getOperator();
        int count = 0;
        if(exp instanceof ArithmeticExp && v2.isConstant() && (((ArithmeticExp.Op) operator).ordinal() == 3 || ((ArithmeticExp.Op) operator).ordinal() == 4) && v2.getConstant() == 0) {
            return Value.getUndef();
        }
        if(v1.isConstant() && v2.isConstant()) {
            int i1 = v1.getConstant();
            int i2 = v2.getConstant();
            if (exp instanceof ArithmeticExp) {
                if((((ArithmeticExp.Op) operator).ordinal() == 3 || ((ArithmeticExp.Op) operator).ordinal() == 4) && i2 == 0) {
                    return Value.getUndef();
                }
                count = switch (((ArithmeticExp.Op) operator).ordinal()) {
                    case 0 -> i1 + i2;
                    case 1 -> i1 - i2;
                    case 2 -> i1 * i2;
                    case 3 -> i1 / i2;
                    case 4 -> i1 % i2;
                    default -> count;
                };
            }
            if (exp instanceof ShiftExp) {
                count = switch (((ShiftExp.Op) operator).ordinal()) {
                    case 0 -> i1 << i2;
                    case 1 -> i1 >> i2;
                    case 2 -> i1 >>> i2;
                    default -> count;
                };
            }
            if (exp instanceof BitwiseExp) {
                count = switch (((BitwiseExp.Op) operator).ordinal()) {
                    case 0 -> i1 | i2;
                    case 1 -> i1 & i2;
                    case 2 -> i1 ^ i2;
                    default -> count;
                };
            }
            return Value.makeConstant(count);
        } else if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else {
            return Value.getUndef();
        }
    }
}
