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

package pascal.taie.analysis.graph.callgraph;


import pascal.taie.World;

import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;


/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while(!workList.isEmpty()) {
            JMethod m = workList.poll();
            if(!callGraph.reachableMethods.contains(m)) {
                callGraph.addReachableMethod(m);
                List<Stmt> stmts = m.getIR().getStmts();
                for (Stmt stmt : stmts) {
                    if(stmt instanceof Invoke callSite) {
                        Set<JMethod> callees = resolve(callSite);
                        for (JMethod callee : callees) {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
                            if (!callGraph.reachableMethods.contains(callee)) {
                                workList.add(callee);
                            }
                        }
                    }
                }
//                callGraph.callSitesIn(m).forEach(callSite -> {
//                    Set<JMethod> callees = resolve(callSite);
//                    for (JMethod callee: callees) {
//                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
//                        if(!callGraph.reachableMethods.contains(callee)) {
//                            workList.add(callee);
//                        }
//                    }
//                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> callees = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        if(callKind == CallKind.STATIC) {
            callees.add(declaringClass.getDeclaredMethod(subsignature));
        } else if(callKind == CallKind.SPECIAL) {
            JMethod dispatch = dispatch(declaringClass, subsignature);
            if(dispatch != null) {
                callees.add(dispatch);
            }
        } else if(callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            Set<JClass> subinterfaces = new HashSet<>();
            subinterfaces.add(declaringClass);
            getAllSubinterfacesOf(declaringClass, subinterfaces);

            Set<JClass> implementors = new HashSet<>(subinterfaces);
            for (JClass subinterface :
                    subinterfaces) {
                getAllImplementorsOf(subinterface, implementors);
            }

            Set<JClass> subclasses = new HashSet<>(implementors);
            for (JClass implementor : implementors) {
                getAllSubclassesOf(implementor, subclasses);
            }

            for (JClass subclass : subclasses) {
                JMethod dispatch = dispatch(subclass, subsignature);
                if(dispatch != null) {
                    callees.add(dispatch);
                }
            }
        }
        return callees;
    }

    private void getAllSubclassesOf(JClass superClass, Set<JClass> subclasses) {
        Collection<JClass> directSubclassesOf = hierarchy.getDirectSubclassesOf(superClass);
        subclasses.addAll(directSubclassesOf);
        for (JClass subclass :  directSubclassesOf) {
            getAllSubclassesOf(subclass, subclasses);
        }
    }

    private void getAllSubinterfacesOf(JClass superInterface, Set<JClass> subinterfaces) {
        Collection<JClass> directSubinterfacesOf = hierarchy.getDirectSubinterfacesOf(superInterface);
        subinterfaces.addAll(directSubinterfacesOf);
        for (JClass subinterface :  directSubinterfacesOf) {
            getAllSubinterfacesOf(subinterface, subinterfaces);
        }
    }

    private void getAllImplementorsOf(JClass superInterface, Set<JClass> implementors) {
        Collection<JClass> directImplementorsOf = hierarchy.getDirectImplementorsOf(superInterface);
        implementors.addAll(directImplementorsOf);
        for (JClass subclass :  directImplementorsOf) {
            getAllImplementorsOf(subclass, implementors);
        }
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        if(declaredMethod != null && !declaredMethod.isAbstract()) {
            return declaredMethod;
        }
        JClass superClass = jclass.getSuperClass();
        if(superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}