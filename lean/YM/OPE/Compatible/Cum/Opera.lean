import YM.OPE.Compatible.Cum.Cory
/-!
# Universal script operator by ink induction. grade cap certified later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Matrix
variable {I J E R:Type}{e d t u j:ℕ}{N:Side}
abbrev Curtain (I:Type):= (k:ℕ)→ Script I k
protected noncomputable def throw {e:ℕ}(A:Script I e):Curtain I:= Pi.single e A
-- callback shapes general, erase indexed. Need P.rec not if extras cost. use `actMe` p recursion inside s induction by wellfound manually
variable (V:Row I I)(A:J→ℕ) -- adjust
abbrev Band (I:Type) (R: Type) :=∀ (d e:ℕ), Script I (e+d)→ R
-- freeze requests
private def onceV (V:Row I I)(R:Band I (Curtain I))(e d:ℕ)(T:Script I (e+d+1))(u c:ℕ): Script I (u+c)→ Curtain I:=match c with
   | 0=>fun _=>0
   | t+1=>fun Q=>∑ i:Fin (t+1), R (d+t) (e+u) (mitt e d u t T Q i V)
-- factor self callback
abbrev BandLeft (I:Type)(d:ℕ):= ∀ (e:ℕ), Script I (e+d)→ Curtain I
private def walkK (V:Row I I)(e:ℕ)(d:ℕ)(T:Script I (e+d+1))(R:∀ i<d+1,BandLeft I i) : Curtain I:=match d with -- adjust
   | 0=>0
   | d+1=> ∑ i:Fin (d+1), R d (by omega) e (knots e d T i V)
variable [DecidableEq J] (u:J→ℕ)(y:J→ℕ)(P:∀ i:J, Script I (y i+u i)) (lamp:J→Bool)
-- pure
private def Scenario (s:Finset J)(F:∀ t:Finset J,t.card<s.card→ Band I (Curtain I))(d:ℕ)(e:ℕ)(T:Script I (e+d)):Curtain I:=match d with
    | 0=> if s=∅ then Shell.throw (e:=e) T else 0
    | d+1=> Scenario s F d (e+1) (Shell.Temper e d T) + walkK V e d T (fun i _ e p=>Scenario s F i e p)+ ∑ i∈s.attach,
                    if lamp i.val then onceV V (F (s.erase i.val) (card_lt_card (erase_ssubset i.property))) e d T (y i.val) (u i.val) (P i.val) else 0
termination_by d
-- measure outer
protected def Hall (V:Row I I)(u y:J→ℕ)(P:∀ i:J, Script I (y i+u i))(lamp:J→Bool)(s:Finset J)(d e:ℕ) (T:Script I (e+d)): Curtain I :=
    Scenario V u y P lamp s (fun t _=> fun d e p=> Shell.Hall V u y P lamp t d e p) d e T -- must use protected Hall
termination_by s.card
@[simp] lemma Hall_nil (s:Finset J)(T:Script I e): Shell.Hall V u y P lamp s 0 e T= if s=∅ then Shell.throw T else 0:=by rw [Shell.Hall, Scenario]
-- expose callbacks with erase proofirrelevance. no cost. easier universal Offer criterion recursion.
abbrev WalkK (V:Row I I)(e d:ℕ)(T:Script I (e+d+1))(F:∀ i:ℕ,BandLeft I i): Curtain I:= walkK V e d T fun i _=> F i
abbrev Once (V:Row I I)(F:Band I (Curtain I))(e d:ℕ)(T:Script I (e+d+1))(u c:ℕ): Script I (u+c)→ Curtain I:= onceV V F e d T u c
lemma script_run (s:Finset J)(d e:ℕ) (T:Script I (e+d+1)): Shell.Hall V u y P lamp s (d+1) e T= Shell.Hall V u y P lamp s d (e+1) (Shell.Temper e d T)+ WalkK V e d T (Shell.Hall V u y P lamp s)+∑ i∈s,if lamp i then Once V (Shell.Hall V u y P lamp (s.erase i)) e d T (y i) (u i) (P i) else 0:=by
    conv_lhs=>rw [Shell.Hall,Scenario]
    congr 1; swap; ·  exact Finset.sum_attach s (fun i=> if lamp i then Once V (Shell.Hall V u y P lamp (s.erase i)) e d T (y i) (u i) (P i) else 0)
    rw [Shell.Hall]; unfold WalkK; congr! 2 -- proof with recurrence
    funext i t e p; rw [Shell.Hall]
lemma once_nil (d e j:ℕ)(T:Script I (e+d+1))(R:Script I (j+0))(A:Band I (Curtain I)): Once V A e d T j 0 R=0:=rfl
lemma once_plus (d e u t:ℕ)(T: Script I (e+d+1))(W: Script I (u+(t+1)))(A:Band I (Curtain I)):Once V A e d T u (t+1) W=∑ i:Fin (t+1),A (d+t) (e+u) (mitt e d u t T W i V):=rfl
@[simp] lemma soak_nil (e:ℕ)(T:Script I (e+1))(F:∀ i:ℕ,BandLeft I i): WalkK V e 0 T F=0:=rfl
lemma soak_plus (e d:ℕ)(T: Script I (e+(d+1)+1))(F:∀ i:ℕ,BandLeft I i):WalkK V e (d+1) T F=∑ i:Fin (d+1), F d e (knots e d T i V):=rfl
end YM.OPE.Libra.Shell
