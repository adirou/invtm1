package il.ac.bgu.cs.formalmethodsintro.base;

import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.AP.P;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.AP.Q;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.Actions.A1;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.Actions.A3;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.States.S1;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.States.S2;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.States.S3;
import static org.junit.Assert.*;

import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedActionException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedAtomicPropositionException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedStateException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;


public class FvmFacadeTest {
    public static enum Locations {
        L1, L2, L3
    }

    public static enum States {
        S1, S2, S3
    }

    public static enum States2 {
        T1, T2, T3
    }


    public static enum AP {
        P, Q
    }

    public static enum Actions {
        A1, A2, A3
    }

    TransitionSystem<States, Actions, AP> ts;
    TransitionSystem<States2, Actions, AP> ts2;

    @Before
    public void before() {
        ts = new TransitionSystem<>();
    }

    @Test(timeout = 2000)
    public void deterministicActionFalse() throws Exception {
        ts.addState(States.S1);
        ts.addState(States.S2);
        ts.addInitialState(States.S3);

        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S2));
        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S1));

        assertFalse(FvmFacade.get().isActionDeterministic(ts));
    }

    @Test(timeout = 2000)
    public void deterministicActionTrue() throws Exception {
        ts.addState(States.S1);
        ts.addState(States.S2);
        ts.addInitialState(States.S3);

        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S2));
        ts.addTransition(new TSTransition(States.S2,Actions.A1,States.S1));

        assertTrue(FvmFacade.get().isActionDeterministic(ts));
    }

    @Test(timeout = 2000)
    public void deterministicAPFalse() throws Exception {
        ts.addState(States.S1);
        ts.addState(States.S2);
        ts.addInitialState(States.S3);

        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S2));
        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S1));
        ts.addToLabel(States.S2, AP.P);
        ts.addToLabel(States.S1, AP.P);

        assertFalse(FvmFacade.get().isActionDeterministic(ts));
    }

    @Test(timeout = 2000)
    public void deterministicAPTrue() throws Exception {
        ts.addState(States.S1);
        ts.addState(States.S2);
        ts.addInitialState(States.S3);

        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S2));
        ts.addTransition(new TSTransition(States.S2,Actions.A1,States.S3));

        ts.addToLabel(States.S2, AP.P);
        ts.addToLabel(States.S3, AP.Q);

        assertTrue(FvmFacade.get().isAPDeterministic(ts));
    }

    @Test(timeout = 2000)
    public void interLeavingProPost() throws Exception {
        ts2 = new TransitionSystem<>();

        ts.addTransition(new TSTransition(States.S1,Actions.A1,States.S2));
        ts.addTransition(new TSTransition(States.S2,Actions.A2,States.S3));
        ts.addTransition(new TSTransition(States.S2,Actions.A1,States.S1));

        ts.addInitialState(States.S1);
        ts2.addInitialState(States2.T1);

        ts.addToLabel(States.S2, AP.P);
        ts.addToLabel(States.S1, AP.Q);

        TransitionSystem<Pair<States,States2>,Actions, AP> newTs = FvmFacade.get().interleave(ts,ts2);
        Set reachable = FvmFacade.get().reach(ts);


        assertTrue(newTs.getStates().contains(Pair.pair(States.S1,States2.T1)));

        Set set = new HashSet();
        set.add(States.S1);
        set.add(States.S3);
        assertEquals(FvmFacade.get().post(ts,States.S2),set);

        Set set1 = new HashSet();
        Set set2 = new HashSet();
        set1.add(States.S1);
        set1.add(States.S3);
        set2.add(States.S2);

        assertEquals(FvmFacade.get().post(ts,set1),set2);
    }



    @Test(timeout = 2000)
    public void pgTests() throws Exception {
        ProgramGraph<Locations,Actions> pg = new ProgramGraph<>();
        pg.addTransition(new PGTransition(Locations.L1, "true","x:=x+1",Locations.L2));
        pg.addTransition(new PGTransition(Locations.L2, "x<3","",Locations.L1));
        pg.addTransition(new PGTransition(Locations.L2, "x>=3","",Locations.L3));

        pg.setInitial(Locations.L1, true);
        List list = new LinkedList();
        list.add("x:=0");
        pg.addInitalization(list);

        Set acSet = new HashSet();
        acSet.add(new AcDef());

        Set cdSet = new HashSet();
        cdSet.add(new cdDef());

        TransitionSystem ts = FvmFacade.get().transitionSystemFromProgramGraph(pg,acSet,cdSet);

        assertTrue(true);
    }

}

class AcDef implements ActionDef{
    @Override
    public boolean isMatchingAction(Object candidate) {
        if(candidate == "x:=x+1" || candidate == "x:=0" || candidate == "")
            return true;

        return false;
    }

    @Override
    public Map<String, Object> effect(Map<String, Object> eval, Object action) {
        Map evalToReturn = new HashMap(eval);
        if(action == "x:=x+1"){
            evalToReturn.put("x", (int)eval.getOrDefault("x",0) + 1 );
            return evalToReturn;
        }
        if(action == "x:=0"){
            evalToReturn.put("x", (int)eval.getOrDefault("x",0));
            return evalToReturn;
        }
        return eval;
    }
}

class cdDef implements ConditionDef{
    @Override
    public boolean evaluate(Map<String, Object> eval, String condition) {
        if(condition == "x>=3"){
            return (int)eval.getOrDefault("x",0) >= 3;
        }

        if(condition == "x<3"){
            return (int)eval.getOrDefault("x",0) < 3;
        }
        if(condition == "true"){
            return true;
        }


        return false;
    }
}