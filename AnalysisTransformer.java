import java.util.*;
import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;


public class AnalysisTransformer extends BodyTransformer {
    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
        SootMethod method = body.getMethod();
        System.out.println("\n====================================");
        System.out.println("Method: " + method.getSignature());

        UnitGraph cfg = new ExceptionalUnitGraph(body);

        Map<Unit, FlowState> IN = new HashMap<>();
        Map<Unit, FlowState> OUT = new HashMap<>();

        Queue<Unit> workList = new LinkedList<>();

        for (Unit u : cfg) {
            // System.out.println("Unit: " + u.toString());

            // List<Unit> predecessors = cfg.getPredsOf(u);
            // if (predecessors.isEmpty()) {
            //     System.out.println("  -> Predecessors: [None / Entry Point]");
            // } else {
            //     System.out.println("  -> Predecessors: " + formatUnits(predecessors));
            // }

            // List<Unit> successors = cfg.getSuccsOf(u);
            // if (successors.isEmpty()) {
            //     System.out.println("  -> Successors: [None / Exit Point]");
            // } else {
            //     System.out.println("  -> Successors: " + formatUnits(successors));
            // }

            // System.out.println();

            IN.put(u, new FlowState());
            OUT.put(u, new FlowState());
            workList.offer(u);
        }

        while (!workList.isEmpty()) {
            Unit u = workList.poll();
            FlowState inState = new FlowState();

            List<Unit> preds = cfg.getPredsOf(u);
            if (!preds.isEmpty()) {
                boolean first = true;
                for (Unit pred : preds) {
                    FlowState predOut = OUT.get(pred);
                    if (first) {
                        inState = predOut.copy();
                        first = false;
                    } else {
                        inState = merge(inState, predOut);
                    }
                }
            }

            IN.put(u, inState);

            FlowState oldOut = OUT.get(u);
            FlowState newOut = flow(u, inState, body);
            
            if (!newOut.equals(oldOut)) {
                OUT.put(u, newOut);
                for (Unit succ : cfg.getSuccsOf(u)) {
                    workList.offer(succ);
                }
            }

            System.out.println("--------------------------------------------------");
            System.out.println("Unit: " + u.toString());
            System.out.println("Line: " + u.getJavaSourceStartLineNumber());

            System.out.println("IN:");
            System.out.println(IN.get(u));

            System.out.println("OUT:");
            System.out.println(OUT.get(u));

        }
    }

    // private static String formatUnits(List<Unit> units) {
    //     StringBuilder sb = new StringBuilder("[");
    //     for (int i = 0; i < units.size(); i++) {
    //         sb.append(units.get(i).toString());
    //         if (i < units.size() - 1) sb.append(", ");
    //     }
    //     return sb.append("]").toString();
    // }

    private FlowState merge(FlowState s1, FlowState s2) {
        FlowState result = new FlowState();

        Set<Local> stackKeys = new HashSet<>();
        stackKeys.addAll(s1.stackMap.keySet());
        stackKeys.addAll(s2.stackMap.keySet());

        for (Local stackVar : stackKeys) {
            Set<String> objUnion = new HashSet<>();

            if (s1.stackMap.containsKey(stackVar)) {
                objUnion.addAll(s1.stackMap.get(stackVar));
            }
            if (s2.stackMap.containsKey(stackVar)) {
                objUnion.addAll(s2.stackMap.get(stackVar));
            }

            result.stackMap.put(stackVar, objUnion);
        }

        Set<ObjFieldPair> heapKeys = new HashSet<>();
        heapKeys.addAll(s1.heapMap.keySet());
        heapKeys.addAll(s2.heapMap.keySet());

        for (ObjFieldPair ofp : heapKeys) {
            Set<String> objUnion = new HashSet<>();

            if (s1.heapMap.containsKey(ofp)) {
                objUnion.addAll(s1.heapMap.get(ofp));
            }
            if (s2.heapMap.containsKey(ofp)) {
                objUnion.addAll(s2.heapMap.get(ofp));
            }

            result.heapMap.put(ofp, objUnion);
        }

        Set<ObjFieldPair> commonAvailKeys = new HashSet<>(s1.availMap.keySet());
        commonAvailKeys.retainAll(s2.availMap.keySet());
        
        for (ObjFieldPair ofp : commonAvailKeys) {
            LinkedHashSet<Local> localsOfS1 = s1.availMap.get(ofp);
            LinkedHashSet<Local> localsOfS2 = s2.availMap.get(ofp);

            LinkedHashSet<Local> commonLocals = new LinkedHashSet<>(localsOfS1);
            commonLocals.retainAll(localsOfS2);

            if (!commonLocals.isEmpty()) {
                result.availMap.put(ofp, commonLocals);
            }
        }

        return result;
    }

    private FlowState flow(Unit u, FlowState in, Body body) {
        FlowState out = in.copy();

        // Handle function calls
        if (u instanceof InvokeStmt
                || (u instanceof AssignStmt 
                        && ((AssignStmt) u).getRightOp() instanceof InvokeExpr)) {

            InvokeExpr invoke;

            if (u instanceof InvokeStmt) {
                invoke = ((InvokeStmt) u).getInvokeExpr();
            } else {
                invoke = (InvokeExpr) ((AssignStmt) u).getRightOp();
            }

            Set<String> reachableObjs = new HashSet<>();

            // find objects which are reachable from the base reference
            if (invoke instanceof InstanceInvokeExpr) {
                Local base = (Local) ((InstanceInvokeExpr) invoke).getBase();

                Set<String> baseObjs = in.stackMap.getOrDefault(
                    base,
                    new HashSet<>(Set.of("ANY"))
                );
                reachableObjs.addAll(baseObjs);
            }

            for (Value arg : invoke.getArgs()) {
                if  (arg instanceof Local) {
                    Set<String> argObjs = in.stackMap.getOrDefault(
                        (Local) arg,
                        new HashSet<>(Set.of("ANY"))
                    );
                    reachableObjs.addAll(argObjs);
                }
            }

            boolean killAll = reachableObjs.contains("ANY");

            Map<ObjFieldPair, Set<String>> newHeap = new HashMap<>(out.heapMap);
            for (ObjFieldPair ofp : out.heapMap.keySet()) {
                if (killAll || reachableObjs.contains(ofp.obj)) {
                    newHeap.put(ofp, new HashSet<>(Set.of("ANY")));
                }
            }

            out.heapMap = newHeap;

            Map<ObjFieldPair, LinkedHashSet<Local>> newAvail = new HashMap<>(out.availMap);
            for (ObjFieldPair ofp : out.availMap.keySet()) {
                if (killAll || reachableObjs.contains(ofp.obj)) {
                    newAvail.remove(ofp);
                }
            }

            out.availMap = newAvail;

            if (u instanceof AssignStmt) {
                Value lhs = ((AssignStmt) u).getLeftOp();
                if (lhs instanceof Local) {
                    out.stackMap.put((Local) lhs, new HashSet<>(Set.of("ANY")));
                }
            }

            return out;
        }

        if (!(u instanceof AssignStmt)) {
            return out;
        }

        AssignStmt stmt = (AssignStmt) u;

        Value lhs = stmt.getLeftOp();
        Value rhs = stmt.getRightOp();

        if ((lhs instanceof Local) && (rhs instanceof AnyNewExpr)) {
            // l = new ();
            Local l = (Local) lhs;
            int line = u.getJavaSourceStartLineNumber();
            String obj = "O" + line;
            out.stackMap.put(l, new HashSet<>(Set.of(obj)));

            killAvailability(out, l);

        } else if ((lhs instanceof Local) && (rhs instanceof Local)) {
            // a = b;
            Local l = (Local) lhs;
            Local r = (Local) rhs;
            out.stackMap.put(l, new HashSet<>(in.stackMap.getOrDefault(r, new HashSet<>(Set.of("ANY")))));

            killAvailability(out, l);

            // progagate availability of b to a
            for (Map.Entry<ObjFieldPair, LinkedHashSet<Local>> availEntry : out.availMap.entrySet()) {
                LinkedHashSet<Local> locals = availEntry.getValue();
                if (locals.contains(r)) {
                    locals.add(l);
                }
            }

        } else if ((lhs instanceof Local) && (rhs instanceof InstanceFieldRef)) {
            // a = b.f;
            Local l = (Local) lhs;
            InstanceFieldRef ref = (InstanceFieldRef) rhs;

            Local base = (Local) ref.getBase();
            SootField field = ref.getField();

            Set<String> resObjs = new HashSet<>();

            if (in.stackMap.containsKey(base)) {
                for (String sObj : in.stackMap.getOrDefault(base, new HashSet<>(Set.of("ANY")))) {
                    if (sObj.equals("ANY")) {
                        resObjs.add("ANY");
                        continue;
                    }

                    ObjFieldPair ofp = new ObjFieldPair(sObj, field);
                    if (in.heapMap.containsKey(ofp)) {
                        resObjs.addAll(in.heapMap.get(ofp));
                    } else {
                        resObjs.add("ANY");
                    }

                    if (!resObjs.contains("ANY") && in.availMap.containsKey(ofp)) {
                        Set<Local> availLocals = in.availMap.get(ofp);
                        Local firstLocal = availLocals.iterator().next();

                        System.out.println(">>> REDUNDANT LOAD detected at line "
                            + u.getJavaSourceStartLineNumber());
                        System.out.println("    " + u.toString());
                        System.out.println("    Replace with: "
                            + l.getName() + " = "
                            + firstLocal.getName());

                        String className = body.getMethod().getDeclaringClass().getName();
                        String methodName = body.getMethod().getName();
                        int line = u.getJavaSourceStartLineNumber();
                        String redundantString = ref.toString() + " " + firstLocal.getName();
                        RedundancyRepository.add(className, methodName, line, redundantString);
                    }
                    out.availMap.putIfAbsent(ofp, new LinkedHashSet<>());
                    out.availMap.get(ofp).add(l);
                }
            }

            if (!resObjs.isEmpty()) {
                out.stackMap.put(l, resObjs);
            }

        } else if ((lhs instanceof InstanceFieldRef) && (rhs instanceof Local)) {
            // a.f = b;
            InstanceFieldRef ref = (InstanceFieldRef) lhs;
            Local r = (Local) rhs;
            Local base = (Local) ref.getBase();
            SootField field = ref.getField();

            Set<String> baseObjs = in.stackMap.getOrDefault(base, new HashSet<>(Set.of("ANY")));
            Set<String> rhsObjs = in.stackMap.getOrDefault(r, new HashSet<>(Set.of("ANY")));
            boolean strongUpdate = baseObjs.size() == 1 && !baseObjs.contains("ANY");
            
            // if (in.stackMap.containsKey(base)) {
            for (String obj : baseObjs) {
                if (obj.equals("ANY")) continue;

                ObjFieldPair ofp = new ObjFieldPair(obj, field);
                // if (in.stackMap.containsKey(r)) {
                //     out.heapMap.put(ofp, new HashSet<>(in.stackMap.get(r)));
                // }
                if (strongUpdate) {
                    out.heapMap.put(ofp, new HashSet<>(rhsObjs));
                } else {
                    Set<String> old = out.heapMap.getOrDefault(ofp, new HashSet<>());
                    old.addAll(rhsObjs);
                    out.heapMap.put(ofp, old);
                }

                // kill old avail info
                out.availMap.remove(ofp);

                // suppose b holds availability of some field load
                // then that availability should be propagated to a.f
                for (LinkedHashSet<Local> locals : in.availMap.values()) {
                    if (locals.contains(r)) {
                        out.availMap.put(ofp, new LinkedHashSet<>(locals));
                        break;
                    }
                }
            }
            // }

        } else if ((lhs instanceof Local) && (rhs instanceof Constant)) {
            // a = constant
            Local l = (Local) lhs;
            String obj = "CONST_" + rhs.toString();
            out.stackMap.put(l, new HashSet<>(Set.of(obj)));

            killAvailability(out, l);

        } else if ((lhs instanceof InstanceFieldRef) && (rhs instanceof Constant)) {
            // a.f = constant
            InstanceFieldRef ref = (InstanceFieldRef) lhs;
            Local l = (Local) ref.getBase();
            SootField field = ref.getField();
            String obj = "CONST_" + rhs.toString();
            Set<String> baseObjs = in.stackMap.getOrDefault(l, new HashSet<>(Set.of("ANY")));

            for (String bObj : baseObjs) {
                if (bObj.equals("ANY")) continue;
                ObjFieldPair ofp = new ObjFieldPair(bObj, field);
                out.heapMap.put(ofp, new HashSet<>(Set.of(obj)));
                out.availMap.remove(ofp);
            }
            
        }
        
        // the below condition will never be triggered because jimple breaks this type of stmts into 2 stmts
        // else if ((lhs instanceof InstanceFieldRef) && (rhs instanceof InstanceFieldRef)) {
        //     // a.f = b.g
        //     InstanceFieldRef lRef = (InstanceFieldRef) lhs;
        //     InstanceFieldRef rRef = (InstanceFieldRef) rhs;

        //     Local lBase = (Local) lRef.getBase();
        //     Local rBase = (Local) rRef.getBase();

        //     SootField lField = lRef.getField();
        //     SootField rField = rRef.getField();

        //     if (in.stackMap.containsKey(lBase) && in.stackMap.containsKey(rBase)) {
        //         for (String lObj : in.stackMap.get(lBase)) {
        //             ObjFieldPair lOfp = new ObjFieldPair(lObj, lField);

        //             for (String rObj : in.stackMap.get(rBase)) {
        //                 ObjFieldPair rOfp = new ObjFieldPair(rObj, rField);

        //                 if (in.heapMap.containsKey(rOfp)) {
        //                     out.heapMap.put(lOfp, new HashSet<>(in.heapMap.get(rOfp)));
        //                 }
                        
        //                 if (in.availMap.containsKey(rOfp)) {
        //                     // rhs has availMap and is copied to lhs
        //                     // whatever replaces rhs, can also be used to replace lhs later

        //                     Set<Local> availLocals = in.availMap.get(rOfp);
        //                     Local firstLocal = availLocals.iterator().next();
    
        //                     System.out.println(">>> REDUNDANT LOAD detected at line "
        //                         + u.getJavaSourceStartLineNumber());
        //                     System.out.println("    " + u.toString());
        //                     System.out.println("    Replace with: "
        //                         + lBase.getName() + "." + lField.getName() + " = "
        //                         + firstLocal.getName());

        //                     out.availMap.put(lOfp, new LinkedHashSet<>(in.availMap.get(rOfp)));
        //                 } else {
        //                     // no availMap to be copied so just kill the availMap info of lhs
        //                     out.availMap.remove(lOfp);
        //                 }
        //             }
        //         }
        //     }
        // }

        return out;
    }

    // kills availability when local variables are changed
    private void killAvailability(FlowState s, Local l) {
        for (Set<Local> locals : s.availMap.values()) {
            locals.remove(l);
        }
        s.availMap.entrySet().removeIf(e -> e.getValue().isEmpty());
    }
}

class FlowState {
    Map<Local, Set<String>> stackMap;
    Map<ObjFieldPair, Set<String>> heapMap;
    Map<ObjFieldPair, LinkedHashSet<Local>> availMap;

    FlowState() {
        this.stackMap = new HashMap<Local, Set<String>>();
        this.heapMap = new HashMap<ObjFieldPair, Set<String>>();
        this.availMap = new HashMap<ObjFieldPair, LinkedHashSet<Local>>();
    }

    FlowState copy() {
        FlowState s = new FlowState();
        for (Map.Entry<Local, Set<String>> stackEntry : stackMap.entrySet()) {
            s.stackMap.put(stackEntry.getKey(), new HashSet<String>(stackEntry.getValue()));
        }
        for (Map.Entry<ObjFieldPair, Set<String>> heapEntry : heapMap.entrySet()) {
            s.heapMap.put(heapEntry.getKey(), new HashSet<String>(heapEntry.getValue()));
        }
        for (Map.Entry<ObjFieldPair, LinkedHashSet<Local>> availEntry : availMap.entrySet()) {
            s.availMap.put(availEntry.getKey(), new LinkedHashSet<Local>(availEntry.getValue()));
        }
        return s;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof FlowState)) return false;

        FlowState fs = (FlowState) o;
        return this.stackMap.equals(fs.stackMap)
            && this.heapMap.equals(fs.heapMap)
            && this.availMap.equals(fs.availMap);
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();

        sb.append("  STACK:\n");
        for (Local l : stackMap.keySet()) {
            sb.append("    ")
            .append(l.getName())
            .append(" -> ")
            .append(stackMap.get(l))
            .append("\n");
        }

        sb.append("  HEAP:\n");
        for (ObjFieldPair k : heapMap.keySet()) {
            sb.append("    (")
            .append(k.obj)
            .append(".")
            .append(k.field.getName())
            .append(") -> ")
            .append(heapMap.get(k))
            .append("\n");
        }

        sb.append("  AVAIL:\n");
        for (ObjFieldPair k : availMap.keySet()) {
            sb.append("    (")
            .append(k.obj)
            .append(".")
            .append(k.field.getName())
            .append(") -> ")
            .append(availMap.get(k))
            .append("\n");
        }

        return sb.toString();
    }
}

class ObjFieldPair {
    String obj;
    SootField field;

    ObjFieldPair(String obj, SootField field) {
        this.obj = obj;
        this.field = field;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ObjFieldPair)) {
            return false;
        }
        ObjFieldPair ofp = (ObjFieldPair) o;
        if (this.obj.equals(ofp.obj) && this.field.equals(ofp.field)) {
            return true;
        }
        return false;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 31 * hash + this.obj.hashCode();
        hash = 31 * hash + this.field.hashCode();
        return hash;
    }
}