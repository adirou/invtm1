package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;
import org.antlr.v4.runtime.ParserRuleContext;

import static il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader.*;

import java.util.List;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;

import java.util.Collections;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;

    /**
     *
     * @return an instance of this class.
     */
    public static FvmFacade get() {
        if (INSTANCE == null) {
            INSTANCE = new FvmFacade();
        }
        return INSTANCE;
    }


    //<checked>
    /**
     * Checks whether a transition system is action deterministic. I.e., if for
     * any given p and α there exists only a single tuple (p,α,q) in →. Note
     * that this must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1)
            return false;
        for (TSTransition trans :  ts.getTransitions()) {
            int counter = 0;
            for (TSTransition transToCompare :  ts.getTransitions()) {
                if(trans.getFrom().equals(transToCompare.getFrom()) && trans.getAction().equals(transToCompare.getAction()))
                    counter++;
                if(counter > 1)
                    return false;
            }
        }
        return true;
    }

    /**
     * Checks whether an action is ap-deterministic (as defined in class), in
     * the context of a given {@link TransitionSystem}.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1)
            return false;
        for (TSTransition trans :  ts.getTransitions()) {
            int counter = 0;
            for (TSTransition transToCompare :  ts.getTransitions()) {
                if(trans.getFrom().equals(transToCompare.getFrom()) &&
                    ts.getLabelingFunction().getOrDefault(trans.getTo(),new HashSet())
                        .equals(ts.getLabelingFunction().getOrDefault(transToCompare.getTo(),new HashSet())))
                    counter++;
                if(counter > 1)
                    return false;
            }
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an execution of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be an execution of {@code ts}.
     * @return {@code true} iff {@code e} is an execution of {@code ts}.
     */
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is an execution fragment of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be an execution fragment of
     * {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S,A> nextSeq = e;

        while(!e.isEmpty()){
            S s1 = nextSeq.head();
            if (!ts.getStates().contains(s1))
                throw new StateNotFoundException(s1);
            if (nextSeq.tail().isEmpty())
                break;

            A a = nextSeq.tail().head();
            if (!ts.getActions().contains(a))
                throw new ActionNotFoundException(a);
            if (nextSeq.tail().tail().isEmpty())
                return false;

            S s2 = nextSeq.tail().tail().head();
            if (!ts.getStates().contains(s2))
                throw new StateNotFoundException(s2);
            if(!ts.getTransitions().contains(new TSTransition<>(s1,a,s2))){
                return false;
            }
            nextSeq = nextSeq.tail().tail();
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an initial execution fragment
     * of a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be an initial execution
     * fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!e.isEmpty()){
            if (ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e))
                return true;
            else
                return false;
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be a maximal execution fragment
     * of {@code ts}.
     * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
     */
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!e.isEmpty()){
            if (isExecutionFragment(ts, e) && post(ts, e.last()).isEmpty())
                return true;
            else
                return false;
        }
        return true;
    }

    /**
     * Checks whether a state in {@code ts} is terminal.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param s The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        Set<S> sPost = post(ts, s);
        return sPost.isEmpty();
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> set= new HashSet<>();
        for (TSTransition<S,?> trans : ts.getTransitions()){
            if(trans.getFrom().equals(s)){
                set.add(trans.getTo());
            }
        }
       return  set;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param c States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> set= new HashSet<>();
        for( S s : c){
            if(!ts.getStates().contains(s)){
                throw new StateNotFoundException(s);
            }
            set.addAll(post(ts,s));
        }
        return set;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> set= new HashSet<>();
        for (TSTransition<S,?> trans : ts.getTransitions()){
            if(trans.getFrom().equals(s) && trans.getAction().equals(a)){
                set.add(trans.getTo());
            }
        }
        return set;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param c Set of states in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> set= new HashSet<>();
        for( S s : c){
            if(!ts.getStates().contains(s)){
                throw new StateNotFoundException(s);
            }
            set.addAll(post(ts, s, a));
        }
        return set;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> set= new HashSet<>();
        for (TSTransition<S,?> trans : ts.getTransitions()){
            if(trans.getTo().equals(s)){
                set.add(trans.getFrom());
            }
        }
        return  set;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param c States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> set= new HashSet<>();
        for( S s : c){
            if(!ts.getStates().contains(s)){
                throw new StateNotFoundException(s);
            }
            set.addAll(pre(ts, s));
        }
        return set;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> set= new HashSet<>();
        for (TSTransition<S,?> trans : ts.getTransitions()){
            if(trans.getTo().equals(s) && trans.getAction().equals(a) ){
                set.add(trans.getFrom());
            }
        }
        return  set;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param c Set of states in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> set= new HashSet<>();
        for( S s : c){
            if(!ts.getStates().contains(s)){
                throw new StateNotFoundException(s);
            }
            set.addAll(pre(ts, s, a));
        }
        return set;
    }

    /**
     * Implements the {@code reach(TS)} function.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */

    private <S, A> void reachExcept(TransitionSystem<S, A, ?> ts, Set<S> checked, S from) {
        for(S s : post(ts,from)){
            if(!checked.contains(s)){
                checked.add(s);
                reachExcept(ts,checked,s);
            }
        }
    }
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> alreadyChecked = new HashSet<>();
        for(S s0 : ts.getInitialStates()){
            if(!alreadyChecked.contains(s0)) {
                alreadyChecked.add(s0);
                reachExcept(ts, alreadyChecked, s0);
            }
        }
        return alreadyChecked;
    }

    //<checked>
    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A> Type of actions (in both systems).
     * @param <P> Type of atomic propositions (in both systems).
     * @param ts1 The first transition system.
     * @param ts2 The second transition system.
     *
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2) {
        TransitionSystem<Pair<S1, S2>, A, P> newTs = new TransitionSystem<>();
        // add states/ initStates/ labelsFunction
        for (S1 s1 : ts1.getStates()){
            for (S2 s2 : ts2.getStates()){
                newTs.addState(Pair.pair(s1,s2));

                for(P p : ts1.getLabelingFunction().getOrDefault(s1,new HashSet<>())){
                    newTs.addToLabel(Pair.pair(s1,s2),p);
                }

                for(P p : ts2.getLabelingFunction().getOrDefault(s2,new HashSet<>())){
                    newTs.addToLabel(Pair.pair(s1,s2),p);
                }

                if(ts1.getInitialStates().contains(s1) && ts2.getInitialStates().contains(s2)){
                   newTs.addInitialState(Pair.pair(s1,s2));
                }
            }
        }

        // add AP
        newTs.addAllAtomicPropositions(ts1.getAtomicPropositions());
        newTs.addAllAtomicPropositions(ts2.getAtomicPropositions());

        // add actions
        newTs.addAllActions(ts1.getActions());
        newTs.addAllActions(ts2.getActions());

        //add transitions
        for( TSTransition trans : ts1.getTransitions()){
            for(S2 s2 : ts2.getStates()){
                newTs.addTransition(
                        new TSTransition(
                                Pair.pair(trans.getFrom(),s2),
                                trans.getAction(),
                                Pair.pair(trans.getTo(),s2)
                        )
                );
            }
        }

        for( TSTransition trans : ts2.getTransitions()){
            for(S1 s1 : ts1.getStates()){
                newTs.addTransition(
                        new TSTransition(
                                Pair.pair(s1,trans.getFrom()),
                                trans.getAction(),
                                Pair.pair(s1,trans.getTo())
                        )
                );
            }
        }

       return newTs;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A> Type of actions (in both systems).
     * @param <P> Type of atomic propositions (in both systems).
     * @param ts1 The first transition system.
     * @param ts2 The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     *
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> newTs = new TransitionSystem<>();
        // add states/ initStates/ labelsFunction
        for (S1 s1 : ts1.getStates()){
            for (S2 s2 : ts2.getStates()){
                newTs.addState(Pair.pair(s1,s2));

                for(P p : ts1.getLabelingFunction().getOrDefault(s1,new HashSet<>())){
                    newTs.addToLabel(Pair.pair(s1,s2),p);
                }

                for(P p : ts2.getLabelingFunction().getOrDefault(s2,new HashSet<>())){
                    newTs.addToLabel(Pair.pair(s1,s2),p);
                }

                if(ts1.getInitialStates().contains(s1) && ts2.getInitialStates().contains(s2)){
                    newTs.addInitialState(Pair.pair(s1,s2));
                }
            }
        }

        // add AP
        newTs.addAllAtomicPropositions(ts1.getAtomicPropositions());
        newTs.addAllAtomicPropositions(ts2.getAtomicPropositions());

        // add actions
        newTs.addAllActions(ts1.getActions());
        newTs.addAllActions(ts2.getActions());

        //add transitions
        for( TSTransition trans : ts1.getTransitions()) {
            if (handShakingActions.contains(trans.getAction())) {
                for (TSTransition trans2 : ts2.getTransitions()) {
                    if( trans2.getAction().equals(trans.getAction())) {
                        newTs.addTransition(
                                new TSTransition(
                                        Pair.pair(trans.getFrom(), trans2.getFrom()),
                                        trans.getAction(),
                                        Pair.pair(trans.getTo(), trans2.getTo())
                                )
                        );
                    }
                }
            }else{
                for(S2 s2 : ts2.getStates()){
                    newTs.addTransition(
                            new TSTransition(
                                    Pair.pair(trans.getFrom(),s2),
                                    trans.getAction(),
                                    Pair.pair(trans.getTo(),s2)
                            )
                    );
                }
            }
        }

        for( TSTransition trans : ts2.getTransitions()){
            if (!handShakingActions.contains(trans.getAction())) {
                for (S1 s1 : ts1.getStates()) {
                    newTs.addTransition(
                            new TSTransition(
                                    Pair.pair(s1, trans.getFrom()),
                                    trans.getAction(),
                                    Pair.pair(s1, trans.getTo())
                            )
                    );
                }
            }
        }

        return newTs;
    }

    /**
     * Creates a new {@link ProgramGraph} object.
     *
     * @param <L> Type of locations in the graph.
     * @param <A> Type of actions of the graph.
     * @return A new program graph instance.
     */
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraph<>();
    }

    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A> Type of actions in BOTH GRAPHS.
     * @param pg1 The first program graph.
     * @param pg2 The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> newPg = createProgramGraph();


        // add locations/ initStates
        for (L1 l1 : pg1.getLocations()) {
            for (L2 l2 : pg2.getLocations()) {
                newPg.addLocation(Pair.pair(l1, l2));

                if (pg1.getInitialLocations().contains(l1) && pg2.getInitialLocations().contains(l2)) {
                    newPg.setInitial(Pair.pair(l1, l2),true);
                }
            }
        }

        //add transitions / actions
        for (PGTransition<L1,A> trans : pg1.getTransitions()) {
            for (L2 l2 : pg2.getLocations()) {
                newPg.addTransition(
                        new PGTransition(
                                Pair.pair(trans.getFrom(), l2),
                                trans.getCondition(),
                                trans.getAction(),
                                Pair.pair(trans.getTo(), l2)
                        )
                );
            }
        }

        for (PGTransition<L2,A> trans : pg2.getTransitions()) {
            for (L1 l1 : pg1.getLocations()) {
                newPg.addTransition(
                        new PGTransition<>(
                                Pair.pair(l1, trans.getFrom()),
                                trans.getCondition(),
                                trans.getAction(),
                                Pair.pair(l1, trans.getTo())
                        )
                );
            }
        }
        //add addInitalization
        //TODO check if that's the meaning
        for (List<String> init1 : pg1.getInitalizations()){
            for (List<String> init2 : pg2.getInitalizations()){
                List newList = new LinkedList<>(init1);
                newList.addAll(init2);
                newPg.addInitalization(newList);
            }
        }


        return newPg;
    }

    private Boolean trueOrFalse(int i){
        if(i == 0)
            return false;
        return true;
    }
    private Boolean isZeroReg( Map<String, Boolean> regs){
        for(String key : regs.keySet()){
            if(regs.get(key))
                return false;
        }
        return true;
    }
    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
            Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts = new TransitionSystem();

        List<Map<String, Boolean>> listInputMap = new LinkedList<>();
        String[] inputsNames = c.getInputPortNames().toArray(new String[c.getInputPortNames().size()]);
        for(int i = 0 ; i < Math.pow(2, inputsNames.length) ; i++ ){
            Map map = new HashMap();
            for(int j = 1 ; j <= inputsNames.length ; j++){
                map.put(inputsNames[j-1],trueOrFalse((i/j)%2));
            }
            listInputMap.add(map);
        }

        List<Map<String, Boolean>> listRegMap = new LinkedList<>();
        String[] regsNames = c.getRegisterNames().toArray(new String[c.getRegisterNames().size()]);
        for(int i = 0 ; i < Math.pow(2, regsNames.length) ; i++ ){
            Map map = new HashMap();
            for(int j = 1 ; j <= regsNames.length ; j++){
                map.put(regsNames[j-1],trueOrFalse((i/j)%2));
            }
            listRegMap.add(map);
        }

        for(Map m1 : listInputMap){
            for(Map m2 : listRegMap){
                ts.addState(Pair.pair(m1,m2));
                if(isZeroReg(m2)){
                    ts.addInitialState(Pair.pair(m1,m2));
                }
            }
        }

        for(Pair<Map<String, Boolean>, Map<String, Boolean>> p : ts.getStates()){
            for(String input: p.first.keySet()){
                if(p.first.get(input)) {
                    ts.addToLabel(p, input);
                }
            }
            for(String reg: p.second.keySet()){
                if(p.second.get(reg)) {
                    ts.addToLabel(p, reg);
                }
            }
            Map<String, Boolean> outputs = c.computeOutputs(p.first,p.second);
            for(String output: outputs.keySet()){
                if(outputs.get(output)) {
                    ts.addToLabel(p, output);
                }
            }
            Map newReg = c.updateRegisters(p.first, p.second);
            for( Map inputs :listInputMap){
                ts.addTransitionFrom(p).action(inputs).to(new Pair(inputs, newReg));
            }
        }

        return ts;
    }

    //checked (mas o menos)
    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L> Type of program graph locations.
     * @param <A> Type of program graph actions.
     * @param pg The program graph to be translated into a transition system.
     * @param actionDefs Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     * graph.
     * @return A transition system representing {@code pg}.
     */
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystem();
        for( L l0: pg.getInitialLocations()){
            if(!pg.getInitalizations().isEmpty()){
                for ( List<String> initilize: pg.getInitalizations() ) {
                    Map env = new HashMap<>();

                    for(String s : initilize ){
                        env = ActionDef.effect(actionDefs, env, s);
                    }
                    ts.addInitialState(new Pair(l0,env));
                }
            }else {
                ts.addInitialState(new Pair(l0, new HashMap<>()));
            }
        }
        LinkedList<String> conditions = new LinkedList<>();

        LinkedList<Pair<L, Map<String, Object>>> queue = new LinkedList();
        queue.addAll(ts.getInitialStates());

        while(!queue.isEmpty()) {
            Pair<L, Map<String, Object>> st  = queue.removeFirst();
            //TODO- may be add labels
            for (PGTransition<L,A> trans : pg.getTransitions()){
                if(trans.getFrom().equals(st.first) && ConditionDef.evaluate(conditionDefs, st.second, trans.getCondition())) {
                    Map<String, Object> effect = ActionDef.effect(actionDefs,st.second, trans.getAction());
                    if(effect != null) {
                        Pair<L, Map<String, Object>> newSt = new Pair(trans.getTo(), ActionDef.effect(actionDefs, st.second, trans.getAction()));
                        conditions.add(trans.getCondition());
                        if (!ts.getStates().contains(newSt)) {
                            queue.add(newSt);
                        }

                        ts.addTransitionFrom(st).action(trans.getAction()).to(newSt);
                    }
                }
            }
        }

        // labeling
        for (Pair<L, Map<String, Object>> state : ts.getStates()) {
            for(String cond : conditions) {
                if( ConditionDef.evaluate(conditionDefs, state.second, cond)) {
                    ts.addToLabel(state, cond);
                    ts.addToLabel(state, state.first.toString());
                }
            }
        }


        return ts;

    }



    private <L,A> ProgramGraph<List<L>,A> createBigPgFromPg (ProgramGraph<L, A> pg){
        ProgramGraph<List<L>,A> bigPg = new ProgramGraph<>();
        for (L loc : pg.getLocations()){
            List<L> bigLoc = new LinkedList<>();
            bigLoc.add(loc);
            if (pg.getInitialLocations().contains(loc)){
                bigPg.setInitial(bigLoc, true);
            }
            bigPg.addLocation(bigLoc);
        }

        for (PGTransition<L,A> trans : pg.getTransitions()){
            PGTransition<List<L>, A> bigNewTrans = new PGTransition<>(
                    Arrays.asList(trans.getFrom()),
                    trans.getCondition() ,
                    trans.getAction(),
                    Arrays.asList(trans.getTo()));
            bigPg.addTransition(bigNewTrans);
        }

        // initializations
        for (List<String> inits : pg.getInitalizations()) {
            bigPg.addInitalization(inits);
        }
        return  bigPg;
    }

    private <L,A>  ProgramGraph<List<L>,A> mergeBigPgToSmallPg (ProgramGraph<List<L>,A> bPg, ProgramGraph<L, A> pg){

        ProgramGraph<List<L>,A> newBigPg = new ProgramGraph<>();

        Set<List<L>> locations = bPg.getLocations();

        for (List<L> locList : locations) {
            for (L loc : pg.getLocations()) {
                List<L> clonedList = new LinkedList<>(locList);
                clonedList.add(loc);

                if (pg.getInitialLocations().contains(loc) && bPg.getInitialLocations().contains(locList)) {
                    newBigPg.setInitial(clonedList, true);
                }

                newBigPg.addLocation(clonedList);
            }
        }

        // trans
        ParserBasedInterleavingActDef parser = new ParserBasedInterleavingActDef();

        List<PGTransition<List<L>,A>> oneSideTransBig = new LinkedList<>();
        List<PGTransition<L,A>> oneSideTrans = new LinkedList<>();
        //left side
        for (PGTransition<List<L>, A> trans : bPg.getTransitions()) {
            if (!parser.isOneSidedAction(trans.getAction().toString())) {
                for (L loc : pg.getLocations()) {
                    List<L> from = new LinkedList<>(trans.getFrom());
                    List<L> to = new LinkedList<>(trans.getTo());
                    from.add(loc);
                    to.add(loc);
                    PGTransition<List<L>, A> newBigTran = new PGTransition<>(
                            from, trans.getCondition(), trans.getAction(), to);
                    newBigPg.addTransition(newBigTran);
                }
            }
            else {
                oneSideTransBig.add(trans);
            }
        }

        //right side
        for (PGTransition<L, A> trans : pg.getTransitions()) {
            if (!parser.isOneSidedAction(trans.getAction().toString())) {
                for (List<L> loc : bPg.getLocations()) {

                    List<L> ClonedFrom = new LinkedList<>(loc);
                    List<L> ClonedTo = new LinkedList<>(loc);

                    ClonedFrom.add(trans.getFrom());
                    ClonedTo.add(trans.getTo());
                    PGTransition<List<L>, A> newTran = new PGTransition<>(
                            ClonedFrom, trans.getCondition(), trans.getAction(), ClonedTo);
                    newBigPg.addTransition(newTran);
                }
            }
            else {
                oneSideTrans.add(trans);
            }
        }

        //handshake
        for (PGTransition<List<L>, A> bigTran : oneSideTransBig) {
            for (PGTransition<L, A> tran : oneSideTrans) {
                A act = getHandShakeAction(bigTran.getAction(), tran.getAction());
                if( act != null) {
                    List<L> from = new LinkedList(bigTran.getFrom());
                    List<L> to = new LinkedList(bigTran.getTo());
                    from.add(tran.getFrom());
                    to.add(tran.getTo());
                    PGTransition<List<L>, A> newTran = new PGTransition<>(
                            from, mergeConds(bigTran.getCondition(), tran.getCondition()), act, to);
                    newBigPg.addTransition(newTran);
                }
            }
        }

        //initialization
        for (List<String> bigInit : bPg.getInitalizations()) {
            for (List<String> init : pg.getInitalizations()) {
                List<String> newInit = new ArrayList<>(bigInit);
                newInit.addAll(init);
                newBigPg.addInitalization(newInit);
            }
        }

        if (bPg.getInitalizations().isEmpty()){
            for (List<String> init : pg.getInitalizations()){
                newBigPg.addInitalization(init);
            }
        }

        if (pg.getInitalizations().isEmpty()){
            for (List<String> init : bPg.getInitalizations()){
                newBigPg.addInitalization(init);
            }
        }

        return newBigPg;
    }


    private <A> A getHandShakeAction(A leftAction, A rightAction) {
        if (!(leftAction instanceof String && rightAction instanceof String))
            return null;

        String[][] acceptable = {{"?","!"} , {"!","?"}};

        for (int i = 0; i < 2 ; i++){
            if (((String)leftAction).contains(acceptable[i][0]) &&
                    ((String)rightAction).contains(acceptable[i][1])){
                String chanelNameLeft = ((String) leftAction).substring(0, ((String) leftAction).indexOf(acceptable[i][0]));
                String chanelNameRight = ((String)rightAction).substring(0, ((String) rightAction).indexOf(acceptable[i][1]));
                if(chanelNameRight.equals(chanelNameLeft))
                    return (A)(leftAction+"|"+rightAction);
            }
        }

        return null;
    }

    private String mergeConds(String cond1, String cond2) {
        if (cond1.length() == 0)
            return cond2;
        if (cond2.length() == 0)
            return cond1;
        return "(" + cond1 + ") && (" + cond2 + ")";
    }

    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {
        Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
        Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());

        return transitionSystemFromChannelSystem(cs, actions, conditions);
    }

    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
         ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {

        ProgramGraph<List<L>, A> bigPg = createBigPgFromPg(cs.getProgramGraphs().get(0));

        for (int i = 1; i < cs.getProgramGraphs().size(); i++) {
            bigPg = mergeBigPgToSmallPg(bigPg, cs.getProgramGraphs().get(i));
        }

        return transitionSystemFromProgramGraph(bigPg, actions, conditions);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        StmtContext tree = pareseNanoPromelaFile(filename);
        return programGraphFromNanoPromela(tree);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext tree = pareseNanoPromelaString(nanopromela);
        return programGraphFromNanoPromela(tree);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext tree = parseNanoPromelaStream(inputStream);
        return programGraphFromNanoPromela(tree);
    }

    Set<String> visited = new HashSet<>();
    final String trueCondition = "true";
    final String exitLocation = "";


    private ProgramGraph<String, String> programGraphFromNanoPromela(StmtContext nanopromela) {
        ProgramGraph<String, String> pg = createProgramGraph();
        Map<String, Set<PGTransition<String, String>>> loc2Trans = sub(nanopromela);

        pg.addLocation(nanopromela.getText());
        pg.setInitial(nanopromela.getText(), true);
        Queue<String> locations = new LinkedList<>(pg.getLocations());

        while (!locations.isEmpty()) {
            String location = locations.poll();
            if (!location.equals(exitLocation))
                for (PGTransition<String, String> tran : loc2Trans.get(location)) {
                    if (!pg.getLocations().contains(tran.getTo())) {
                        locations.add(tran.getTo());
                    }
                    pg.addTransition(tran);
                }
        }
        return pg;
    }


    private boolean isBaseStmt(StmtContext stmt){
        return stmt.assstmt() != null || stmt.chanreadstmt() != null || stmt.chanwritestmt() != null
                || stmt.atomicstmt() != null || stmt.skipstmt() != null;
    }

    private void appendTransition(Set<PGTransition<String, String>> transitions, String from, String cond, String action, String to){
        PGTransition<String, String> pgTransition = new PGTransition<>(from, cond, action, to);
        transitions.add(pgTransition);
    }

    private void appendTransitionToMap(Map<String, Set<PGTransition<String, String>>> loc2Trans, String from, String cond, String action, String to){
        Set<PGTransition<String, String>> transitions = new HashSet<>();
        if (loc2Trans.containsKey(from))
            transitions =  loc2Trans.get(from);
        appendTransition(transitions, from, cond, action, to);
        loc2Trans.put(from, transitions);
    }

    private Map<String, Set<PGTransition<String, String>>> sub(StmtContext stmt) {
        Map<String, Set<PGTransition<String, String>>> loc2Trans;

        if (isBaseStmt(stmt))
            loc2Trans = addBasicTrans(stmt);
        else if (stmt.dostmt() != null)
            loc2Trans = addDoTrans(stmt);
        else if (stmt.ifstmt() != null)
            loc2Trans = addIfTrans(stmt);
        else
            loc2Trans = addConcatTrans(stmt);
        return loc2Trans;
    }


    private Map<String, Set<PGTransition<String, String>>> addBasicTrans(StmtContext stmt) {
        Map<String, Set<PGTransition<String, String>>> loc2Trans = new HashMap<>();
        Set<PGTransition<String, String>> transitions = new HashSet<>();
        appendTransition(transitions, stmt.getText(), trueCondition, stmt.getText(), exitLocation);
        loc2Trans.put(stmt.getText(), transitions);
        return loc2Trans;
    }

    private Map<String, Set<PGTransition<String, String>>> addIfTrans(StmtContext stmt) {
        Map<String, Set<PGTransition<String, String>>> loc2Trans = new HashMap<>();
        Set<PGTransition<String, String>> transitions = new HashSet<>();
        for (OptionContext option : stmt.ifstmt().option()) {
            loc2Trans = sub(option.stmt());
            for (PGTransition<String, String> tran : loc2Trans.get(option.stmt().getText())) {
                String cond = mergeConds(option.boolexpr().getText(), tran.getCondition());
                appendTransition(transitions, stmt.getText(), cond, tran.getAction(), tran.getTo());
            }
        }
        loc2Trans.put(stmt.getText(), transitions);
        return loc2Trans;
    }

    private Map<String, Set<PGTransition<String, String>>> addDoTrans(StmtContext stmt ) {
        List<String> condsList = new LinkedList<>();
        Map<String, Set<PGTransition<String, String>>> loc2Trans = new HashMap<>();
        String exitCond = "";
        for (OptionContext option : stmt.dostmt().option()) {
            loc2Trans.putAll(sub(option.stmt()));
            String cond = option.boolexpr().getText();
            visited =  new HashSet<>();
            loc2Trans.putAll(getTransRec(loc2Trans, stmt.getText(), option.stmt().getText(), stmt.getText(), cond));
            String notgi = "!(" + cond + ")";
            condsList.add(notgi);
        }

        exitCond = condsList.get(0);
        for(int i = 1; i < condsList.size(); i++){
            exitCond += "&&" + condsList.get(i);
        }

        appendTransitionToMap(loc2Trans, stmt.getText(), exitCond, "", exitLocation);
        return loc2Trans;
    }

    private Map<String, Set<PGTransition<String, String>>> addConcatTrans(StmtContext stmt) {
        Map<String, Set<PGTransition<String, String>>> loc2TransTmp = new HashMap<>();
        Map<String, Set<PGTransition<String, String>>> loc2Trans = new HashMap<>();
        StmtContext stmt1 = stmt.stmt(0);
        StmtContext stmt2 = stmt.stmt(1);
        loc2TransTmp = sub(stmt1);
        loc2Trans = sub(stmt2);
        loc2Trans.putAll(loc2TransTmp);
        visited =  new HashSet<>();
        loc2Trans.putAll(getTransRec(loc2Trans, stmt.getText(), stmt1.getText(), stmt2.getText(), ""));
        return loc2Trans;
    }



    private Map<String, Set<PGTransition<String, String>>> getTransRec(Map<String, Set<PGTransition<String, String>>> loc2Trans, String Stmt,
                        String optionStmt, String toStmt, String cond) {
        if (!visited.contains(optionStmt)) {
            visited.add(optionStmt);
            for (PGTransition<String, String> tran : loc2Trans.get(optionStmt)) {
                String mergedCond = mergeConds(cond, tran.getCondition());
                String to = tran.getTo() + ";" + toStmt;
                if (tran.getTo().equals(exitLocation))
                    to = toStmt;
                appendTransitionToMap(loc2Trans, Stmt, mergedCond, tran.getAction(), to);

                if (!tran.getTo().isEmpty())
                    loc2Trans.putAll(getTransRec(loc2Trans, to, tran.getTo(), toStmt, trueCondition));
            }
        }
        return loc2Trans;
    }


    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts> Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A> Type of actions in the transition system.
     * @param <P> Type of atomic propositions in the transition system, which is
     * also the type of the automaton alphabet.
     * @param ts The transition system.
     * @param aut The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
            Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S> Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A> Type of actions in the transition system.
     * @param <P> Type of atomic propositions in the transition system, which is
     * also the type of the automaton alphabet.
     * @param ts The transition system.
     * @param aut A Büchi automaton for the words that do not satisfy the
     * property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
            Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new java.lang.UnsupportedOperationException();
    }

}
