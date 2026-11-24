import YangMills.WilsonProof.NativeSupport.WilsonLatticeData

import YangMills.CutoffTrajectory
import YangMills.LatticeFields
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Mesh and bare-coupling estimates along the Wilson trajectory. -/

set_option autoImplicit false

noncomputable section

namespace YangMills.Wilson

open Filter

open scoped Topology

variable {g : GaugeGroup}

namespace WilsonTrajectory

variable {B : Maxwell.Reference g} {C : WilsonFamily g}

theorem meshAtZero (trajectory : WilsonTrajectory B C) : C.mesh 0 = 1 := by
  simp [WilsonFamily.mesh, trajectory.denominatorZero]

theorem meshTendsToZero (family : WilsonFamily g) :
    Tendsto family.mesh atTop (𝓝 0) := by
  unfold WilsonFamily.mesh
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp family.denominatorStrict.tendsto_atTop)

theorem sameBareReference (trajectory : WilsonTrajectory B C) (p q : ℕ) :
    C.beta 0 p = C.beta 0 q := by
  obtain ⟨_, _, origin, _⟩ := trajectory.bare
  exact (origin p).trans (origin q).symm

theorem barePositive (trajectory : WilsonTrajectory B C) (data : WilsonData B C)
    (N p : ℕ) : 0 < C.beta N p := by
  obtain ⟨reference, positive, _, band⟩ := trajectory.bare
  have den : (1 : ℕ) ≤ (C.denominator N).val := (C.denominator N).property
  have logarithm : 0 ≤ Real.log ((C.denominator N).val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast den)
  have center : 0 < wilsonBareCenter B C reference N := by
    unfold wilsonBareCenter
    exact add_pos_of_pos_of_nonneg positive
      (mul_nonneg (mul_nonneg (by norm_num) data.positive.le) logarithm)
  exact (half_pos center).trans_le (band N p).1

theorem rejectsNonpositiveBare (trajectory : WilsonTrajectory B C) (data : WilsonData B C)
    {N p : ℕ} (bad : C.beta N p ≤ 0) : False :=
  (not_le_of_gt (trajectory.barePositive data N p)) bad

theorem rejectsLargeLogSteps (trajectory : WilsonTrajectory B C) {ε : ℝ} (positive : 0 < ε)
    (bad : ∃ᶠ m : ℕ in atTop, ε ≤ wilsonLogStep C m) : False := by
  apply bad
  filter_upwards [trajectory.gentle.eventually (gt_mem_nhds positive)] with m small
  exact not_le_of_gt small

end WilsonTrajectory

end YangMills.Wilson
