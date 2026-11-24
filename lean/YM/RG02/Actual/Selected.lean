import YM.RG02.Actual.Condition
import YM.SectorNext.VACUUM_NORMALIZATION.Noise
import YM.Pert.Asymptotics.RawAxis

/-! Same witness and period throughout. The all-coarse-field positivity in
this real step does not assert any tail cost or complex domain for a later
normalization estimate. A useful (potentially severe) reciprocal bound for
fixed period can use `den_floor`, *not* offered for a volume-uniform error. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Actual
open MeasureTheory Filter Function RG Wilson Extra.Trajectories Conditional SectorNext.Vacuum
open scoped YM.Push.LogIdentity.Tags Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge} {H : History G} {C : Family G} {N p m : ℕ}

abbrev nextStep (H : History G) (p m : ℕ) := H.levels.clock.op m p

lemma coupling_pos (h : H.Selected) (hm : m ≤ N) : 0 < H.β N p m :=
  lt_of_lt_of_le (div_pos (lt_trans zero_lt_one (H.levels.fits.delayed m)) (by norm_num)) (h.represents N p m hm).band.1

lemma run_pos (h : C.Makes) (hm : m ≤ N) : 0<Pert.Asymptotics.regulatorRun C N p m :=
  inv_pos.mpr (Real.sqrt_pos.mpr (coupling_pos h.wilson hm))

lemma run_value (h : C.Makes) (hm : m ≤ N) :
    C.path.β N p m = 1/(Pert.Asymptotics.regulatorRun C N p m)^2 := by
  rw [Pert.Asymptotics.regulatorRun,inv_pow, Real.sq_sqrt (coupling_pos h.wilson hm).le,one_div,inv_inv]

variable (h : H.Selected)
include h

lemma eval_pos (hm : m ≤ N) (U : Config G (H.S.side m p)) : 0 < (H.rep N p m).eval U := by
  rw [← Insertions.vac_eq h hm]; exact Insertions.vac_pos hm _
lemma eval_cont (hm : m ≤ N) : Continuous (H.rep N p m).eval := by
  rw [← Insertions.vac_eq h hm]; exact (Insertions.vac_smooth hm).continuous.comp matrixField_cont
lemma eval_envelope (hm : m ≤ N) : Envelope (H.rep N p m).eval := (H.rep N p m).envelope (h.represents _ _ _ hm).good
lemma eval_integrable (hm : m ≤ N) : Integrable (H.rep N p m).eval (prior G (H.S.side m p)) :=
  (eval_envelope h hm).integrable _

variable (hm : m<N) (V : Config G (H.S.side m p))
include hm
local notation "S" => nextStep H p m
local notation "R" => H.rep N p (m+1)
local notation "W" => H.rep N p m

theorem den_eval : denominator S R V=(W).eval V := by
  rw [denominator_value S (h.represents N p (m+1) hm).good (H.levels.blocks m p).branches, (h.steps _ _ _ hm).1]

theorem den_pos : 0<denominator S R V := by rw [den_eval h hm]; exact eval_pos h hm.le V

theorem posterior_law : IsProbabilityMeasure (posterior S R V) := probability S
  (h.represents N p _ hm).good (fun U => (eval_pos h hm U).le) (H.levels.blocks m p).branches (den_pos h hm V)

theorem den_floor : Real.exp (-(wires (H.S.side m p)*(2*kick S (R).beta)))*partition G (H.S.side N p) (H.β N p N) ≤
    denominator S R V := by
  rw [denominator_value S (h.represents N p _ hm).good (H.levels.blocks m p).branches,
    ← H.partition_eq h N p (m+1) hm]
  exact (push_sandwich S (H.levels.blocks m p).branches (R).beta (R).eval (eval_integrable h hm)
    (fun u => (eval_pos h hm u).le) V).1
end YM.RG02.Actual
