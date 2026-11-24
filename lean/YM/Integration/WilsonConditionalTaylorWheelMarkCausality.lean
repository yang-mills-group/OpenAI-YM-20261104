import YM.Integration.WilsonConditionalTaylorIndependentMarked

/-! Coupling coefficients in the normalized full rooted transfer are causal:
through a fixed order E only the submitted earlier grades through E enter.
This is needed to descend many true marked dates at one fixed cap. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelMarkCausality
open FormalBulk08 Lattice Laurent Exterior RG Wilson Precision Bloch Tree Next.Free
open FormalBulk08.Lava FormalBulk08.Kemp FormalBulk08.Flat FormalBulk08.Mesa FormalBulk08.Reef
open Function Filter
open scoped Classical BigOperators
variable {I:Type} (q:I→I→ℝ)

theorem linked (p A B:Waves I) (n e r:ℕ) (old:∀i≤n,∀g≤e,A i g=B i g):
    brawl q p A n e r=brawl q p B n e r:=by
  unfold brawl
  apply Finset.sum_congr rfl
  intro a h
  apply Finset.sum_congr rfl
  intro b hb
  have a':a.1+a.2=e:=Finset.mem_antidiagonal.mp h
  have b':b.1+b.2=n:=Finset.mem_antidiagonal.mp hb
  rw [old b.2 (by omega) a.2 (by omega)]

theorem heat (p:Waves I) (A B:OrbitV I) (E:ℕ) (old:∀e≤E,A e=B e)
    (n e r:ℕ) (bound:e≤E):dipper q p A n e r=dipper q p B n e r:=by
  induction n using Nat.strong_induction_on generalizing e r with
  | h n ih=>
    cases n with
    | zero=>rw [dipper_first,dipper_first,old e bound]
    | succ n=>
      rw [dipper_succ,dipper_succ,ih n (by omega) e _ bound]
      rw [linked q p _ _ n e r (fun i lo g cap=>by funext m;exact ih i (by omega) g m (cap.trans bound))]

theorem marked {G:Gauge} {K:KernelChoices} {j t:ℕ} (P:Flight j t) (L:Lodge P.patch) (W A B:Pot G)
    (O:ChartRatio G) (branch:P.patch.Branches K G) (E cap e r:ℕ) (bound:e≤E) (old:∀i≤E,A i=B i):
    braise P L W A O branch cap e r=braise P L W B O branch cap e r:=by
  unfold braise
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  apply heat _ _ _ _ E _ n e r bound
  intro i hi
  funext d
  exact congrArg (Glide.urn P L G K) (congrFun (old i hi) d)
end YM.Integration.WilsonConditionalTaylorWheelMarkCausality
end
