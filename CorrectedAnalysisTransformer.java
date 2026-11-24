import java.util.*;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.*;

class AnalysisTransformer extends BodyTransformer {

    /*
     * All array elements of an abstract array are represented by this
     * single abstract field.
     *
     * Consequently, array stores must be weak updates: a[i] = x does
     * not imply that every a[j] now contains x.
     */
    public static final SootField ARRAY_FIELD =
            new SootField(
                    "[]",
                    RefType.v("java.lang.Object"),
                    Modifier.PUBLIC
            );

    private static final String ANY = "ANY";

    /*
     * One unique abstract object ID per allocation statement.
     *
     * IdentityHashMap is intentional: Unit identity, rather than
     * Unit.toString() or source line number, identifies an allocation.
     */
    private Map<Unit, String> allocationIds;

    /*
     * Finite universe used to initialize the must-analysis component.
     *
     * Each key is (abstract object, field).
     * Each value is the set of locals that could be available for it.
     */
    private Set<ObjFieldPair> availabilityUniverse;

    private Set<Local> methodLocals;

    @Override
    protected void internalTransform(
            Body body,
            String phaseName,
            Map<String, String> options) {

        SootMethod method = body.getMethod();

        System.out.println("\n====================================");
        System.out.println("Method: " + method.getSignature());

        UnitGraph cfg = new ExceptionalUnitGraph(body);

        /*
         * Step 1: Assign unique IDs to allocation statements.
         */
        buildAllocationIds(body);

        /*
         * Step 2: Collect the finite universe for availMap.
         */
        buildAvailabilityUniverse(body);

        /*
         * Step 3: Create the initial state.
         *
         * May components:
         *   stackMap = bottom (empty)
         *   heapMap  = bottom (empty)
         *
         * Must component:
         *   availMap = top (all possible availability facts)
         */
        FlowState initialState = makeInitialState();

        Map<Unit, FlowState> IN = new HashMap<>();
        Map<Unit, FlowState> OUT = new HashMap<>();

        Queue<Unit> workList = new ArrayDeque<>();

        /*
         * Initialize every node to the product-lattice initial state.
         */
        for (Unit u : cfg) {
            IN.put(u, initialState.copy());
            OUT.put(u, initialState.copy());
            workList.offer(u);
        }

        /*
         * Entry boundary:
         *
         * - Reference parameters and this are initially unknown.
         * - Heap information is empty.
         * - No availability facts are known at method entry.
         *
         * Missing locals are treated as ANY when queried.
         */
        FlowState entryState = makeEntryState(body);

        Set<Unit> heads = new HashSet<>(cfg.getHeads());

        /*
         * Step 4: Worklist algorithm.
         *
         * No redundancy is reported inside this loop. Intermediate
         * states are not necessarily final states.
         */
        while (!workList.isEmpty()) {

            Unit u = workList.poll();

            FlowState newIn;

            if (heads.contains(u)) {

                // Include the method-entry boundary.
                newIn = entryState.copy();

                // Also include any backedge predecessors.
                for (Unit pred : cfg.getPredsOf(u)) {
                    newIn = merge(newIn, OUT.get(pred));
                }

            } else {

                List<Unit> preds = cfg.getPredsOf(u);

                if (preds.isEmpty()) {
                    newIn = entryState.copy();
                } else {
                    newIn = OUT.get(preds.get(0)).copy();

                    for (int i = 1; i < preds.size(); i++) {
                        newIn = merge(newIn, OUT.get(preds.get(i)));
                    }
                }
            }

            IN.put(u, newIn);

            FlowState newOut = flow(u, newIn);

            FlowState oldOut = OUT.get(u);

            if (!newOut.equals(oldOut)) {

                OUT.put(u, newOut);

                for (Unit succ : cfg.getSuccsOf(u)) {
                    workList.offer(succ);
                }
            }
        }

        /*
         * Step 5: Print final states, after convergence.
         */
        for (Unit u : cfg) {

            System.out.println("--------------------------------------------------");
            System.out.println("Unit: " + u);
            System.out.println("Line: " + u.getJavaSourceStartLineNumber());

            System.out.println("IN:");
            System.out.println(IN.get(u));

            System.out.println("OUT:");
            System.out.println(OUT.get(u));
        }

        /*
         * Step 6: Report redundant loads using only final IN states.
         *
         * This avoids reporting a load as redundant based on an
         * intermediate state that may later be invalidated by a
         * loop backedge.
         */
        reportRedundantLoads(body, IN);
    }

    // ============================================================
    // Allocation-site IDs
    // ============================================================

    private void buildAllocationIds(Body body) {

        allocationIds = new IdentityHashMap<>();

        int allocationNumber = 0;

        for (Unit u : body.getUnits()) {

            if (!(u instanceof AssignStmt)) {
                continue;
            }

            AssignStmt stmt = (AssignStmt) u;

            if (stmt.getRightOp() instanceof AnyNewExpr) {

                allocationIds.put(
                        u,
                        "ALLOC_" + allocationNumber++
                );
            }
        }
    }

    private String getAllocationId(Unit u) {

        String id = allocationIds.get(u);

        if (id == null) {
            return ANY;
        }

        return id;
    }

    // ============================================================
    // Availability universe
    // ============================================================

    private void buildAvailabilityUniverse(Body body) {

        methodLocals = new LinkedHashSet<>();
        availabilityUniverse = new LinkedHashSet<>();

        methodLocals.addAll(body.getLocals());

        Set<SootField> accessedFields = new LinkedHashSet<>();

        /*
         * Collect fields accessed by instance-field and array
         * operations.
         */
        for (Unit u : body.getUnits()) {

            if (!(u instanceof Stmt)) {
                continue;
            }

            Stmt stmt = (Stmt) u;

            for (ValueBox box : stmt.getUseAndDefBoxes()) {

                Value value = box.getValue();

                if (value instanceof InstanceFieldRef) {

                    InstanceFieldRef ref = (InstanceFieldRef) value;
                    accessedFields.add(ref.getField());

                } else if (value instanceof ArrayRef) {

                    accessedFields.add(ARRAY_FIELD);
                }
            }
        }

        /*
         * Every allocation site is paired with every accessed field.
         *
         * This is a conservative finite universe. It may contain
         * combinations that are never actually accessed at runtime,
         * but those extra facts are harmless.
         */
        for (String obj : allocationIds.values()) {

            for (SootField field : accessedFields) {

                availabilityUniverse.add(
                        new ObjFieldPair(obj, field)
                );
            }
        }
    }

    // ============================================================
    // State initialization
    // ============================================================

    private FlowState makeInitialState() {

        FlowState state = new FlowState();

        /*
         * stackMap and heapMap are empty: bottom for may analysis.
         */

        /*
         * availMap is top for must analysis.
         *
         * For every (object, field), all locals are initially
         * considered possible representatives.
         */
        for (ObjFieldPair ofp : availabilityUniverse) {

            state.availMap.put(
                    ofp,
                    new LinkedHashSet<>(methodLocals)
            );
        }

        return state;
    }

    private FlowState makeEntryState(Body body) {

        FlowState state = new FlowState();

        /*
         * At method entry, no availability facts are guaranteed.
         */
        state.availMap.clear();

        /*
         * The receiver is unknown at method entry.
         */
        if (!body.getMethod().isStatic()) {

            Local thisLocal = body.getThisLocal();

            state.stackMap.put(
                    thisLocal,
                    singleton(ANY)
            );
        }

        /*
         * Method parameters are initially unknown.
         */
        for (int i = 0; i < body.getMethod().getParameterCount(); i++) {

            Local parameterLocal = body.getParameterLocal(i);

            state.stackMap.put(
                    parameterLocal,
                    singleton(ANY)
            );
        }

        return state;
    }

    // ============================================================
    // Merge
    // ============================================================

    private FlowState merge(FlowState s1, FlowState s2) {

        FlowState result = new FlowState();

        /*
         * STACK MAP: MAY analysis.
         *
         * Join = union.
         *
         * If a local is absent on one path, its value on that path
         * is unknown. Therefore, add ANY.
         */
        Set<Local> stackKeys = new HashSet<>();

        stackKeys.addAll(s1.stackMap.keySet());
        stackKeys.addAll(s2.stackMap.keySet());

        for (Local local : stackKeys) {

            Set<String> values = new HashSet<>();

            Set<String> values1 = s1.stackMap.get(local);
            Set<String> values2 = s2.stackMap.get(local);

            if (values1 == null) {
                values.add(ANY);
            } else {
                values.addAll(values1);
            }

            if (values2 == null) {
                values.add(ANY);
            } else {
                values.addAll(values2);
            }

            result.stackMap.put(local, values);
        }

        /*
         * HEAP MAP: MAY analysis.
         *
         * Join = union.
         *
         * If a heap key is absent on one path, its value on that
         * path is unknown. Add ANY.
         */
        Set<ObjFieldPair> heapKeys = new HashSet<>();

        heapKeys.addAll(s1.heapMap.keySet());
        heapKeys.addAll(s2.heapMap.keySet());

        for (ObjFieldPair ofp : heapKeys) {

            Set<String> values = new HashSet<>();

            Set<String> values1 = s1.heapMap.get(ofp);
            Set<String> values2 = s2.heapMap.get(ofp);

            if (values1 == null) {
                values.add(ANY);
            } else {
                values.addAll(values1);
            }

            if (values2 == null) {
                values.add(ANY);
            } else {
                values.addAll(values2);
            }

            result.heapMap.put(ofp, values);
        }

        /*
         * AVAILABILITY MAP: MUST analysis.
         *
         * Join = intersection.
         *
         * A local is available for (object, field) after a join only
         * if it is available along every incoming path.
         *
         * Missing key means empty availability set.
         */
        for (ObjFieldPair ofp : availabilityUniverse) {

            Set<Local> locals1 =
                    s1.availMap.getOrDefault(
                            ofp,
                            Collections.emptySet()
                    );

            Set<Local> locals2 =
                    s2.availMap.getOrDefault(
                            ofp,
                            Collections.emptySet()
                    );

            LinkedHashSet<Local> common =
                    new LinkedHashSet<>(locals1);

            common.retainAll(locals2);

            if (!common.isEmpty()) {
                result.availMap.put(ofp, common);
            }
        }

        return result;
    }

    // ============================================================
    // Transfer function
    // ============================================================

    private FlowState flow(Unit u, FlowState in) {

        FlowState out = in.copy();

        /*
         * Identity statements:
         *
         *   this := @this
         *   p := @parameter0
         *   e := @caughtexception
         *
         * These values are unknown to this analysis.
         */
        if (u instanceof IdentityStmt) {

            IdentityStmt stmt = (IdentityStmt) u;

            if (stmt.getLeftOp() instanceof Local) {

                Local lhs = (Local) stmt.getLeftOp();

                killAvailability(out, lhs);

                out.stackMap.put(lhs, singleton(ANY));
            }

            return out;
        }

        /*
         * Method calls.
         *
         * We do not have a side-effect summary for the callee.
         * Conservatively invalidate all heap and availability
         * information.
         */
        if (u instanceof InvokeStmt
                || (u instanceof AssignStmt
                    && ((AssignStmt) u).getRightOp() instanceof InvokeExpr)) {

            if (u instanceof AssignStmt) {

                AssignStmt stmt = (AssignStmt) u;

                if (stmt.getLeftOp() instanceof Local) {

                    Local lhs = (Local) stmt.getLeftOp();

                    killAvailability(out, lhs);

                    out.stackMap.put(lhs, singleton(ANY));
                }
            }

            out.heapMap.clear();
            out.availMap.clear();

            return out;
        }

        if (!(u instanceof AssignStmt)) {
            return out;
        }

        AssignStmt stmt = (AssignStmt) u;

        Value lhs = stmt.getLeftOp();
        Value rhs = stmt.getRightOp();

        // --------------------------------------------------------
        // Case 1: Local = ArrayRef
        //
        //     x = a[i]
        // --------------------------------------------------------

        if (lhs instanceof Local && rhs instanceof ArrayRef) {

            Local destination = (Local) lhs;
            ArrayRef arrayRef = (ArrayRef) rhs;

            Local base = (Local) arrayRef.getBase();

            Set<String> baseObjects = getPointsTo(base, in);

            killAvailability(out, destination);

            Set<String> resultValues = new HashSet<>();

            for (String obj : baseObjects) {

                if (ANY.equals(obj)) {
                    resultValues.add(ANY);
                    continue;
                }

                ObjFieldPair ofp =
                        new ObjFieldPair(obj, ARRAY_FIELD);

                /*
                 * If heap information is absent, the array element
                 * value is unknown.
                 */
                Set<String> values =
                        in.heapMap.getOrDefault(
                                ofp,
                                singleton(ANY)
                        );

                resultValues.addAll(values);

                /*
                 * After this load, destination contains the value
                 * read from this abstract array object.
                 */
                // out.availMap
                //         .computeIfAbsent(
                //                 ofp,
                //                 k -> new LinkedHashSet<>()
                //         )
                //         .add(destination);
                // commented for soundness
            }

            if (resultValues.isEmpty()) {
                resultValues.add(ANY);
            }

            out.stackMap.put(destination, resultValues);

            return out;
        }

        // --------------------------------------------------------
        // Case 2: Local = InstanceFieldRef
        //
        //     x = obj.f
        // --------------------------------------------------------

        if (lhs instanceof Local && rhs instanceof InstanceFieldRef) {

            Local destination = (Local) lhs;
            InstanceFieldRef fieldRef = (InstanceFieldRef) rhs;

            Local base = (Local) fieldRef.getBase();
            SootField field = fieldRef.getField();

            Set<String> baseObjects = getPointsTo(base, in);

            killAvailability(out, destination);

            Set<String> resultValues = new HashSet<>();

            for (String obj : baseObjects) {

                if (ANY.equals(obj)) {
                    resultValues.add(ANY);
                    continue;
                }

                ObjFieldPair ofp = new ObjFieldPair(obj, field);

                Set<String> values =
                        in.heapMap.getOrDefault(
                                ofp,
                                singleton(ANY)
                        );

                resultValues.addAll(values);

                /*
                 * The destination now holds the value of obj.f.
                 */
                out.availMap
                        .computeIfAbsent(
                                ofp,
                                k -> new LinkedHashSet<>()
                        )
                        .add(destination);
            }

            if (resultValues.isEmpty()) {
                resultValues.add(ANY);
            }

            out.stackMap.put(destination, resultValues);

            return out;
        }

        // --------------------------------------------------------
        // Case 3: Local = NewExpr / NewArrayExpr / NewMultiArrayExpr
        //
        //     x = new C
        //     a = new int[n]
        // --------------------------------------------------------

        if (lhs instanceof Local && rhs instanceof AnyNewExpr) {

            Local destination = (Local) lhs;

            String obj = getAllocationId(u);

            killAvailability(out, destination);

            out.stackMap.put(destination, singleton(obj));

            return out;
        }

        // --------------------------------------------------------
        // Case 4: Local = Local
        //
        //     x = y
        // --------------------------------------------------------

        if (lhs instanceof Local && rhs instanceof Local) {

            Local destination = (Local) lhs;
            Local source = (Local) rhs;

            Set<String> values = getPointsTo(source, in);

            /*
             * Save availability facts for source before killing
             * destination. This also handles x = x correctly.
             */
            Set<ObjFieldPair> sourceAvailability =
                    getAvailableLocations(source, in);

            killAvailability(out, destination);

            out.stackMap.put(
                    destination,
                    new HashSet<>(values)
            );

            /*
             * If source was a valid representative for a field,
             * destination becomes another valid representative.
             */
            for (ObjFieldPair ofp : sourceAvailability) {

                out.availMap
                        .computeIfAbsent(
                                ofp,
                                k -> new LinkedHashSet<>()
                        )
                        .add(destination);
            }

            return out;
        }

        // --------------------------------------------------------
        // Case 5: Local = Constant
        //
        //     x = 10
        //     x = null
        // --------------------------------------------------------

        if (lhs instanceof Local && rhs instanceof Constant) {

            Local destination = (Local) lhs;

            killAvailability(out, destination);

            out.stackMap.put(
                    destination,
                    singleton(constantId((Constant) rhs))
            );

            return out;
        }

        // --------------------------------------------------------
        // Case 6: ArrayRef = value
        //
        //     a[i] = x
        //
        // Array indices are not distinguished. Therefore, this
        // operation is always a weak update.
        // --------------------------------------------------------

        if (lhs instanceof ArrayRef) {

            ArrayRef arrayRef = (ArrayRef) lhs;
            Local base = (Local) arrayRef.getBase();

            Set<String> baseObjects = getPointsTo(base, in);
            Set<String> rhsValues = getAbstractValues(rhs, in, u);

            /*
             * If the base may refer to any object, all tracked heap
             * information may be affected.
             */
            if (baseObjects.contains(ANY)) {

                out.heapMap.clear();
                out.availMap.clear();

                return out;
            }

            for (String obj : baseObjects) {

                ObjFieldPair ofp =
                        new ObjFieldPair(obj, ARRAY_FIELD);

                /*
                 * Weak update:
                 * preserve old values and add the newly stored value.
                 *
                 * If the old value is unknown, retain ANY.
                 */
                Set<String> oldValues =
                        out.heapMap.getOrDefault(
                                ofp,
                                singleton(ANY)
                        );

                Set<String> updated =
                        new HashSet<>(oldValues);

                updated.addAll(rhsValues);

                out.heapMap.put(ofp, updated);

                /*
                 * The old availability information is no longer
                 * guaranteed after a store.
                 */
                out.availMap.remove(ofp);
            }

            return out;
        }

        // --------------------------------------------------------
        // Case 7: InstanceFieldRef = value
        //
        //     obj.f = x
        // --------------------------------------------------------

        if (lhs instanceof InstanceFieldRef) {

            InstanceFieldRef fieldRef = (InstanceFieldRef) lhs;

            Local base = (Local) fieldRef.getBase();
            SootField field = fieldRef.getField();

            Set<String> baseObjects = getPointsTo(base, in);
            Set<String> rhsValues = getAbstractValues(rhs, in, u);

            /*
             * If the base may be ANY, the store may affect every
             * tracked object.
             */
            if (baseObjects.contains(ANY)) {

                out.heapMap.clear();
                out.availMap.clear();

                return out;
            }

            /*
             * Strong update is valid only if the base points to
             * exactly one known abstract object.
             */
            boolean strongUpdate =
                    baseObjects.size() == 1;

            /*
             * Find locals known to hold the same value as RHS.
             *
             * This is useful for:
             *
             *     obj.f = x
             *
             * If x is already equivalent to y, then after a strong
             * update y can also represent obj.f.
             */
            Set<Local> equivalentLocals =
                    getEquivalentLocals(rhs, in);

            for (String obj : baseObjects) {

                ObjFieldPair ofp =
                        new ObjFieldPair(obj, field);

                if (strongUpdate) {

                    /*
                     * Strong update: replace the old field value.
                     */
                    out.heapMap.put(
                            ofp,
                            new HashSet<>(rhsValues)
                    );

                    out.availMap.remove(ofp);

                    /*
                     * After a strong update, RHS and all its known
                     * equivalent locals represent the new field value.
                     */
                    if (!equivalentLocals.isEmpty()) {

                        out.availMap.put(
                                ofp,
                                new LinkedHashSet<>(equivalentLocals)
                        );
                    }

                } else {

                    /*
                     * Weak update: retain old values and add RHS.
                     */
                    Set<String> oldValues =
                            out.heapMap.getOrDefault(
                                    ofp,
                                    singleton(ANY)
                            );

                    Set<String> updated =
                            new HashSet<>(oldValues);

                    updated.addAll(rhsValues);

                    out.heapMap.put(ofp, updated);

                    /*
                     * A weak update does not guarantee that the
                     * field now equals RHS. Invalidate availability.
                     */
                    out.availMap.remove(ofp);
                }
            }

            return out;
        }

        // --------------------------------------------------------
        // Case 8: Other local assignments
        //
        // Examples:
        //     x = (C) y
        //     x = y + 1
        //     x = lengthof a
        //
        // For expressions not explicitly modeled, use ANY.
        // --------------------------------------------------------

        if (lhs instanceof Local) {

            Local destination = (Local) lhs;

            Set<String> values =
                    getAbstractValues(rhs, in, u);

            Set<ObjFieldPair> sourceAvailability =
                    rhs instanceof Local
                            ? getAvailableLocations((Local) rhs, in)
                            : Collections.emptySet();

            killAvailability(out, destination);
d
            out.stackMap.put(
                    destination,
                    new HashSet<>(values)
            );

            for (ObjFieldPair ofp : sourceAvailability) {

                out.availMap
                        .computeIfAbsent(
                                ofp,
                                k -> new LinkedHashSet<>()
                        )
                        .add(destination);
            }

            return out;
        }

        /*
         * Static-field operations and other unsupported forms are
         * not represented in the instance heap abstraction.
         *
         * For a static-field write, invalidate availability facts
         * conservatively because the analysis does not model static
         * state or possible references reachable through it.
         */
        if (lhs instanceof StaticFieldRef) {

            out.heapMap.clear();
            out.availMap.clear();
        }

        return out;
    }

    // ============================================================
    // Abstract values and points-to helpers
    // ============================================================

    private Set<String> singleton(String value) {

        Set<String> result = new HashSet<>();
        result.add(value);

        return result;
    }

    private String constantId(Constant constant) {

        return "CONST:"
                + constant.getClass().getSimpleName()
                + ":"
                + constant.toString();
    }

    /*
     * Returns the abstract values associated with a local.
     *
     * A missing local is unknown, not an empty points-to set.
     */
    private Set<String> getPointsTo(Local local, FlowState state) {

        Set<String> values = state.stackMap.get(local);

        if (values == null || values.isEmpty()) {
            return singleton(ANY);
        }

        return new HashSet<>(values);
    }

    /*
     * Returns the abstract value of an expression.
     *
     * This implementation explicitly handles locals, constants,
     * allocation expressions, and casts. Other expressions are
     * conservatively represented by ANY.
     */
    private Set<String> getAbstractValues(
            Value value,
            FlowState state,
            Unit currentUnit) {

        if (value instanceof Local) {
            return getPointsTo((Local) value, state);
        }

        if (value instanceof Constant) {
            return singleton(constantId((Constant) value));
        }

        if (value instanceof AnyNewExpr) {
            return singleton(getAllocationId(currentUnit));
        }

        if (value instanceof CastExpr) {

            CastExpr castExpr = (CastExpr) value;

            return getAbstractValues(
                    castExpr.getOp(),
                    state,
                    currentUnit
            );
        }

        return singleton(ANY);
    }

    // ============================================================
    // Availability helpers
    // ============================================================

    /*
     * Remove a local from every availability set.
     *
     * If x is reassigned, it can no longer represent the old value
     * of any field or array element.
     */
    private void killAvailability(FlowState state, Local local) {

        for (Set<Local> locals : state.availMap.values()) {
            locals.remove(local);
        }

        state.availMap.entrySet().removeIf(
                entry -> entry.getValue().isEmpty()
        );
    }

    /*
     * Returns all (object, field) pairs for which local is currently
     * known to hold the field value.
     */
    private Set<ObjFieldPair> getAvailableLocations(
            Local local,
            FlowState state) {

        Set<ObjFieldPair> result = new HashSet<>();

        for (Map.Entry<ObjFieldPair, LinkedHashSet<Local>> entry
                : state.availMap.entrySet()) {

            if (entry.getValue().contains(local)) {
                result.add(entry.getKey());
            }
        }

        return result;
    }

    /*
     * Returns locals known to hold the same value as the RHS.
     *
     * If RHS is a local, it is equivalent to every local in each
     * availability set containing it.
     *
     * Constants are not represented by local availability facts.
     */
    private Set<Local> getEquivalentLocals(
            Value rhs,
            FlowState state) {

        Set<Local> result = new LinkedHashSet<>();

        if (!(rhs instanceof Local)) {
            return result;
        }

        Local source = (Local) rhs;

        result.add(source);

        for (Set<Local> locals : state.availMap.values()) {

            if (locals.contains(source)) {
                result.addAll(locals);
            }
        }

        return result;
    }

    // ============================================================
    // Redundant-load reporting (POST-FIXPOINT ONLY)
    // ============================================================

    private void reportRedundantLoads(
            Body body,
            Map<Unit, FlowState> IN) {

        SootMethod method = body.getMethod();

        String className =
                method.getDeclaringClass().getName();

        String methodName =
                method.getName();

        for (Unit u : body.getUnits()) {

            if (!(u instanceof AssignStmt)) {
                continue;
            }

            AssignStmt stmt = (AssignStmt) u;

            if (!(stmt.getLeftOp() instanceof Local)) {
                continue;
            }

            Local destination = (Local) stmt.getLeftOp();

            Value rhs = stmt.getRightOp();

            FlowState in = IN.get(u);

            if (in == null) {
                continue;
            }

            /*
             * Case 1: x = obj.f
             */
            if (rhs instanceof InstanceFieldRef) {

                InstanceFieldRef fieldRef =
                        (InstanceFieldRef) rhs;

                Local base = (Local) fieldRef.getBase();

                Set<String> baseObjects =
                        getPointsTo(base, in);

                Local replacement =
                        findCommonAvailableLocal(
                                in,
                                baseObjects,
                                fieldRef.getField()
                        );

                if (replacement != null) {

                    reportRedundantLoad(
                            className,
                            methodName,
                            u,
                            rhs,
                            destination,
                            replacement
                    );
                }
            }

            /*
             * Case 2: x = a[i]
             */
            else if (rhs instanceof ArrayRef) {

                ArrayRef arrayRef = (ArrayRef) rhs;

                Local base = (Local) arrayRef.getBase();

                Set<String> baseObjects =
                        getPointsTo(base, in);

                Local replacement =
                        findCommonAvailableLocal(
                                in,
                                baseObjects,
                                ARRAY_FIELD
                        );

                if (replacement != null) {

                    reportRedundantLoad(
                            className,
                            methodName,
                            u,
                            rhs,
                            destination,
                            replacement
                    );
                }
            }
        }
    }

    /*
     * A load through a possibly multi-target base is redundant only
     * if one common local is available for every possible target.
     *
     * Example:
     *
     *     pointsTo(base) = {O1, O2}
     *
     *     avail(O1, f) = {x, y}
     *     avail(O2, f) = {y, z}
     *
     * The common available local is y.
     *
     * If any target is ANY, or if the intersection is empty, the
     * load is not reported as redundant.
     */
    private Local findCommonAvailableLocal(
            FlowState state,
            Set<String> baseObjects,
            SootField field) {

        if (baseObjects == null
                || baseObjects.isEmpty()
                || baseObjects.contains(ANY)) {

            return null;
        }

        Set<Local> common = null;

        for (String obj : baseObjects) {

            ObjFieldPair ofp =
                    new ObjFieldPair(obj, field);

            Set<Local> available =
                    state.availMap.get(ofp);

            if (available == null || available.isEmpty()) {
                return null;
            }

            if (common == null) {

                common = new LinkedHashSet<>(available);

            } else {

                common.retainAll(available);

                if (common.isEmpty()) {
                    return null;
                }
            }
        }

        if (common == null || common.isEmpty()) {
            return null;
        }

        return common.iterator().next();
    }

    private void reportRedundantLoad(
            String className,
            String methodName,
            Unit u,
            Value loadExpression,
            Local destination,
            Local replacement) {

        int line = u.getJavaSourceStartLineNumber();

        System.out.println(
                ">>> REDUNDANT LOAD detected at line " + line
        );

        System.out.println("    " + u);

        System.out.println(
                "    Replace with: "
                        + destination.getName()
                        + " = "
                        + replacement.getName()
        );

        String redundantString =
                loadExpression.toString()
                        + " "
                        + replacement.getName();

        RedundancyRepository.add(
                className,
                methodName,
                line,
                redundantString
        );
    }
}


// ================================================================
// FlowState
// ================================================================

class FlowState {

    /*
     * Local -> abstract values.
     *
     * May-analysis: merge using union.
     */
    Map<Local, Set<String>> stackMap;

    /*
     * (abstract object, field) -> abstract field values.
     *
     * May-analysis: merge using union.
     */
    Map<ObjFieldPair, Set<String>> heapMap;

    /*
     * (abstract object, field) -> locals known to hold that value.
     *
     * Must-analysis: merge using intersection.
     */
    Map<ObjFieldPair, LinkedHashSet<Local>> availMap;

    FlowState() {

        stackMap = new HashMap<>();
        heapMap = new HashMap<>();
        availMap = new HashMap<>();
    }

    FlowState copy() {

        FlowState result = new FlowState();

        for (Map.Entry<Local, Set<String>> entry
                : stackMap.entrySet()) {

            result.stackMap.put(
                    entry.getKey(),
                    new HashSet<>(entry.getValue())
            );
        }

        for (Map.Entry<ObjFieldPair, Set<String>> entry
                : heapMap.entrySet()) {

            result.heapMap.put(
                    entry.getKey(),
                    new HashSet<>(entry.getValue())
            );
        }

        for (Map.Entry<ObjFieldPair, LinkedHashSet<Local>> entry
                : availMap.entrySet()) {

            result.availMap.put(
                    entry.getKey(),
                    new LinkedHashSet<>(entry.getValue())
            );
        }

        return result;
    }

    @Override
    public boolean equals(Object obj) {

        if (!(obj instanceof FlowState)) {
            return false;
        }

        FlowState other = (FlowState) obj;

        return stackMap.equals(other.stackMap)
                && heapMap.equals(other.heapMap)
                && availMap.equals(other.availMap);
    }

    @Override
    public int hashCode() {

        return Objects.hash(
                stackMap,
                heapMap,
                availMap
        );
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();

        sb.append("STACK:\n");

        for (Map.Entry<Local, Set<String>> entry
                : stackMap.entrySet()) {

            sb.append("    ")
                    .append(entry.getKey().getName())
                    .append(" -> ")
                    .append(entry.getValue())
                    .append("\n");
        }

        sb.append("HEAP:\n");

        for (Map.Entry<ObjFieldPair, Set<String>> entry
                : heapMap.entrySet()) {

            sb.append("    ")
                    .append(entry.getKey())
                    .append(" -> ")
                    .append(entry.getValue())
                    .append("\n");
        }

        sb.append("AVAIL:\n");

        for (Map.Entry<ObjFieldPair, LinkedHashSet<Local>> entry
                : availMap.entrySet()) {

            sb.append("    ")
                    .append(entry.getKey())
                    .append(" -> ")
                    .append(entry.getValue())
                    .append("\n");
        }

        return sb.toString();
    }
}


// ================================================================
// ObjFieldPair
// ================================================================

class ObjFieldPair {

    final String obj;
    final SootField field;

    ObjFieldPair(String obj, SootField field) {

        this.obj = obj;
        this.field = field;
    }

    @Override
    public boolean equals(Object o) {

        if (this == o) {
            return true;
        }

        if (!(o instanceof ObjFieldPair)) {
            return false;
        }

        ObjFieldPair other = (ObjFieldPair) o;

        return obj.equals(other.obj)
                && field.equals(other.field);
    }

    @Override
    public int hashCode() {

        return Objects.hash(obj, field);
    }

    @Override
    public String toString() {

        return "(" + obj + "." + field.getName() + ")";
    }
}