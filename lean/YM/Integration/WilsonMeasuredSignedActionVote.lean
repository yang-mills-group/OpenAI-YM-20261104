import YM.Integration.WilsonMeasuredSignedActionDebits
import YM.Integration.WilsonMeasuredSignedActionStation
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionVote
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof Campaign
open WilsonOriginalNullPlacedGermMap WilsonOriginalMicroscopicGuardedReporters
open WilsonMeasuredSignedActionCourse WilsonPositionProgramBlockedTrialVoice
open WilsonMeasuredSignedActionAverage WilsonMeasuredSignedActionDebits
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T)
local notation "F₀" => R.family.labels.level 4
local notation "C₀" => R.family
local notation "B₀" => R.family.localSection 4
local notation "H₀" => R.family.path
local notation "P₀" => R.family.params

def rent (j per:ℕ):ℝ:=max 0 (invoice (C:=C₀) 4 j per*stock C₀ j)
private theorem cost_positive:0≤cost F₀:=by
  unfold cost
  positivity [zero_le_one.trans (Motion.orbitCost_one_le F₀)]

include L in
theorem original (simple:G.Simple):∀ᶠ j:ℕ in atTop,∀{N per n target:ℕ}(live:j+n≤N){η:ℝ}
    (A:(C₀).label 4 ≃ₗ[ℂ] (C₀).label 4)(e:(C₀).label 4)
    (_home:Opened C₀ 4 j per)(_arrived:Arrived R 4 j (j+n) N per target (by omega) live η A e)
    (_invariant:fixed F₀ (axis F₀))(s E:ℝ)(_sp:0<s)
    (_weak:(F₀).coeffSize ((s:ℂ) • (F₀).core e-axis F₀)≤E)
    (_budget:cost F₀*((E+rent R j per*(F₀).coeffSize (axis F₀))/(1-rent R j per))<
       total*(F₀).coeffSize (axis F₀)),
    ∃c:ℝ,0≤c ∧ (F₀).core (pool F₀ (A.symm e))=(c:ℂ) • axis F₀:=by
  filter_upwards [WilsonMeasuredSignedActionFitted.original R L simple] with j returned
  intro N per n target live η A e home arrived invariant s E sp weak budget
  let I:=denomination F₀ H₀ N (j+n)
  let w:=A.symm e
  obtain ⟨Z,hz,_,fields,moves,sign⟩:=returned (per:=per) live
  let X:=I.symm.trans Z.index
  let x:=X w
  have point:=fields w
  have appointment (k:ℕ)(eq:k=n)(hk:j+k≤N):
      (Z.plays (I.symm w)).density 0 B₀ ((H₀).rep N per j)=
        WilsonPositionProgramOriginalBlockedTrial.carried R 4 (b:=j) (n:=k) (p:=per) hk 0 w:=by
    subst k;exact point
  have seen:=WilsonMeasuredSignedActionFitted.measured R (K:=j+n) (by omega) live arrived home hz (I.symm w)
    (appointment _ (by omega) _)
  change (F₀).coeffSize (e-x)≤ invoice (C:=C₀) 4 j per*Z.charge (I.symm w) at seen
  have inv:0≤ invoice (C:=C₀) 4 j per:=mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Germ.germ_close F₀ P₀).choose_spec.1.le) (Real.exp_pos _).le
  have billed: (F₀).coeffSize ((F₀).core (x-e))≤rent R j per*(F₀).coeffSize ((F₀).core x):=by
    have rev:(F₀).coeffSize (x-e)=(F₀).coeffSize (e-x):=by
      apply Finset.sum_congr rfl
      intro i _
      exact norm_sub_rev _ _
    calc _ ≤ (F₀).coeffSize (x-e):=Work.G08.size_core _ _
      _ ≤ _:=rev.trans_le seen
      _ ≤ invoice (C:=C₀) 4 j per*(stock C₀ j*(F₀).coeffSize ((F₀).core x)):=
        mul_le_mul_of_nonneg_left (hz.cone _) inv
      _ ≤ _:=by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right ..) (Work.G08.size_nonneg _ _)
  have scaled:(F₀).coeffSize ((s:ℂ) • (F₀).core x-(s:ℂ) • (F₀).core e)≤
      rent R j per*(F₀).coeffSize ((s:ℂ) • (F₀).core x):=by
    rw [←smul_sub,←map_sub,WilsonMeasuredSignedActionCone.size,WilsonMeasuredSignedActionCone.size,abs_of_pos sp]
    exact (mul_le_mul_of_nonneg_left billed sp.le).trans_eq (mul_left_comm ..)
  have small:rent R j per<1:=max_lt (by norm_num) (home.small.trans (by norm_num))
  have paid:=relative F₀ _ _ _ (le_max_left 0 _) small weak scaled
  exact inspected F₀ simple X moves sign invariant sp
    ((mul_le_mul_of_nonneg_left paid (cost_positive R)).trans_lt budget)

end YM.Integration.WilsonMeasuredSignedActionVote
end
