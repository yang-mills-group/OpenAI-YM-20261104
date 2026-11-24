import YM.Integration.LocalComparisonPacketMultiplier
import YM.Integration.LocalComparisonSignedLinearity
import YM.OPE.Therm.Law

/-! Integrability of the complete chosen packet model.

The original Paid and PrescribedPackets receipts first give the global
unit-test bound and the exact subset-wise linearity of the full countable
packet sum. Each admitted test is then rescaled using its own Orbit.Bill.
The resulting finite-dimensional bound is used only for integrability at
fixed data. No uniform quantitative estimate for arbitrary tests is asserted.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function Finset MeasureTheory Lattice Wilson RG Marker RG3.Held
open Comparison.Density.RenderM Comparison.RG02
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {D : V → ComparisonDensity.Address.Orbit}

omit [Fintype V] in
private theorem letter_coordinate_smul {s : Finset V}
    {f : TestSpace D → ℂ}
    (h : Letter ℂ (fun v => (D v).Mood) s f)
    (c : V → ℂ) (x : TestSpace D) :
    f (fun v => c v • x v) = (∏ v ∈ s, c v) * f x := by
  let y (t : Finset V) : TestSpace D :=
    fun v => if v ∈ t then c v • x v else x v
  have hy (t : Finset V) : t ⊆ s →
      f (y t) = (∏ v ∈ t, c v) * f x := by
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp [y]
    | @insert i t hi ih =>
      intro hts
      have his : i ∈ s := hts (mem_insert_self i t)
      have hfun : y (insert i t) = update (y t) i (c i • x i) := by
        funext v
        by_cases hv : v = i
        · subst v
          simp [y]
        simp [y, hv, update_of_ne]
      have hbase : update (y t) i (x i) = y t := by
        have hv : y t i = x i := by simp [y, hi]
        rw [← hv]
        exact update_eq_self i (y t)
      rw [hfun, h.scale _ i his, hbase,
        ih (insert_subset_iff.mp hts).2, prod_insert hi]
      simp only [smul_eq_mul]
      ring
  calc
    f (fun v => c v • x v) = f (y s) :=
      h.stay _ _ (fun v hv => by simp [y, hv])
    _ = (∏ v ∈ s, c v) * f x := hy s (Subset.refl s)

omit [Fintype V] [DecidableEq V] in
private theorem tests_from_unit (x : TestSpace D) :
    ∃ (c : V → ℂ) (y : IndependentTests D),
      x = fun v => c v • testInclusion D y v := by
  choose a ha using fun v => (D v).admits (x v)
  let b (v : V) : ℝ := a v + 1
  have hb (v : V) : 0 < b v := by
    dsimp [b]
    linarith [(ha v).nonneg]
  let y : IndependentTests D := fun v =>
    ⟨((b v : ℝ) : ℂ)⁻¹ • (x v).val, by
      have hbill := (ha v).more (show a v ≤ b v by dsimp [b]; linarith)
      have hs := hbill.smul (((b v : ℝ) : ℂ)⁻¹)
      simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hb v), inv_mul_cancel₀ (ne_of_gt (hb v))] using hs⟩
  refine ⟨fun v => (b v : ℂ), y, ?_⟩
  funext v
  apply Subtype.ext
  change (x v).val = (b v : ℂ) • ((b v : ℂ)⁻¹ • (x v).val)
  rw [smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (hb v).ne'

private theorem packet_read_measurable {n : Side}
    (M : MarkedPackets D G n R) (x : TestSpace D) (g : ℝ) :
    Measurable (fun U : Config G n => M.read x g U) := by
  unfold MarkedPackets.read
  apply Measurable.tsum
  intro i
  apply Continuous.measurable
  change Continuous (fun U : Config G n =>
    (Poly.send (M.mode i) (M.term x g U i)).part)
  apply continuous_pi
  intro s
  simp only [Poly.part_send]
  by_cases hs : s = M.mode i
  · simp only [if_pos hs]
    cases hi : M.packet i with
    | none =>
      simp only [MarkedPackets.term, hi]
      exact continuous_const
    | some T =>
      simp only [MarkedPackets.term, hi]
      unfold Token.read Token.touch Slot.atSite expandAt
      fun_prop
  simp only [if_neg hs]
  exact continuous_const

section Paid
variable {n : Side} {M : MarkedPackets D G n R}
    {p : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

/-- Full packet summability and the original Paid receipt extend the
unit-test bound to every admitted independent test, including zeros.
The bound here is only a fixed-data integrability license. -/
theorem MarkedPackets.Paid.multiplier_envelope
    (h : M.Paid p address region w g width budget coverOffset coverSlope)
    (hs : ∀ (x : TestSpace D) (U : Config G n),
      Summable (fun i => Poly.send (M.mode i) (M.term x g U i)))
    (x : TestSpace D) :
    Envelope (fun U : Config G n => Poly.pass (M.read x g U)) := by
  obtain ⟨c, y, hx⟩ := tests_from_unit x
  obtain ⟨k, hk, hnorm⟩ := Poly.equivalent_norm (R := R) h.positive
  let B : ℝ := Real.exp (2 ^ M.rankCap * (Fintype.card V * budget)) * k
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le hk
  have hunit (U : Config G n) :
      ‖Poly.pass (M.read (testInclusion D y) g U)‖ ≤ B :=
    (hnorm _).trans (mul_le_mul_of_nonneg_right (h.multiplier_price y U) hk)
  let a (s : R.Mode) : ℂ := ∏ v ∈ s.val, c v
  let A : ℝ := ∑ s : R.Mode, ‖a s‖
  have hA : 0 ≤ A := sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨Poly.pass_cont.measurable.comp (packet_read_measurable M x g),
    A * B, fun U => ?_⟩
  change ‖(Poly.pass (M.read x g U)).part‖ ≤ A * B
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA hB)).2
  intro s
  have hp := (h.read_published U (fun z => hs z U)).pass s
  have he := letter_coordinate_smul hp c (testInclusion D y)
  rw [← hx] at he
  rw [he, norm_mul]
  have ha : ‖a s‖ ≤ A := single_le_sum (fun _ _ => norm_nonneg _) (mem_univ s)
  have hv : ‖(Poly.pass (M.read (testInclusion D y) g U)).part s‖ ≤ B :=
    (norm_le_pi_norm (Poly.part (Poly.pass (M.read (testInclusion D y) g U))) s).trans
      (hunit U)
  exact mul_le_mul ha hv (norm_nonneg _) hA
end Paid

section Formal
variable {C : Family G} {datum : LocalFormal.Datum C R}
    {Y : Bulk.Chain C.path}
    {inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period)}
    {model : MarkedPackets D G (C.side datum.level datum.period) R} {order : ℕ}
    {p : BudgetPoint} {address : V → Support (C.side datum.level datum.period)}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood)
      (C.side datum.level datum.period)}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

/-- The prescribed completion supplies the whole-domain summability used
above; no additional domination assumption is introduced. -/
theorem PrescribedPackets.multiplier_envelope
    (hF : PrescribedPackets Y datum inputColors model order)
    (hP : model.Paid p address region w g width budget coverOffset coverSlope)
    (hg : g ≠ 0) (x : TestSpace D) :
    Envelope (fun U => Poly.pass (model.read x g U)) :=
  hP.multiplier_envelope (fun z U => hF.summable z g hg U) x

/-- The literal full model is integrable under the original normalized
history law. All independent tests are arbitrary elements of TestSpace. -/
theorem PrescribedPackets.actual_model_integrable
    (hF : PrescribedPackets Y datum inputColors model order) (hC : C.Makes)
    (hP : model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)
    (x : TestSpace D) :
    Integrable (fun U => Poly.pass (model.read x
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U))
      (OPE.Therm.scene C.path datum.cutoff datum.period datum.level) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2
      (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  letI : IsProbabilityMeasure
      (OPE.Therm.scene C.path datum.cutoff datum.period datum.level) :=
    OPE.Therm.probability hC.wilson datum.below.le
  obtain ⟨hmeas, B, hB⟩ := hF.multiplier_envelope hP hg x
  exact Integrable.of_bound hmeas.aestronglyMeasurable B (ae_of_all _ hB)
/-- The same complete model also has the unnormalized L1 receipt needed
by an actual transport step, with its original full vacuum kept intact. -/
theorem PrescribedPackets.actual_model_weighted_integrable
    (hF : PrescribedPackets Y datum inputColors model order) (hC : C.Makes)
    (hP : model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)
    (x : TestSpace D) :
    Integrable (fun U => (C.path.rep datum.cutoff datum.period datum.level).eval U •
      Poly.pass (model.read x
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U))
      (prior G (C.side datum.level datum.period)) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2
      (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  have hm := hF.multiplier_envelope hP hg x
  have hv := (C.path.rep datum.cutoff datum.period datum.level).envelope
    (hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  obtain ⟨B, hB⟩ := hm.cost
  obtain ⟨K, hK⟩ := hv.cost
  refine Integrable.of_bound (hv.meas.smul hm.meas).aestronglyMeasurable
    (K * B) (ae_of_all _ fun U => ?_)
  rw [norm_smul]
  exact mul_le_mul (hK U) (hB U) (norm_nonneg _)
    ((norm_nonneg _).trans (hK U))

/-- The literal inverse multiplier has the same fixed-data envelope
construction. Subset-wise linearity is preserved by native negation and
finite exponentiation, so arbitrary admitted tests, including zeros,
remain in the original domain. -/
theorem PrescribedPackets.inverse_multiplier_envelope
    (hF : PrescribedPackets Y datum inputColors model order)
    (hP : model.Paid p address region w g width budget coverOffset coverSlope)
    (hg : g ≠ 0) (x : TestSpace D) :
    Envelope (fun U => Poly.pass (-(model.read x g U))) := by
  obtain ⟨c, y, hx⟩ := tests_from_unit x
  obtain ⟨k, hk, hnorm⟩ := Poly.equivalent_norm (R := R) hP.positive
  let B : ℝ := Real.exp (2 ^ model.rankCap * (Fintype.card V * budget)) * k
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le hk
  have hneg (a : Poly R) : Poly.price w (-a) = Poly.price w a := by
    simp only [Poly.price, Poly.part_neg, norm_neg]
  have hprice (U : Config G (C.side datum.level datum.period)) :
      Poly.price w (Poly.pass (-(model.read (testInclusion D y) g U))) ≤
        Real.exp (2 ^ model.rankCap * (Fintype.card V * budget)) := by
    have hp := Poly.pass_budget hP.positive (-(model.read (testInclusion D y) g U))
    rw [hneg] at hp
    exact hp.trans (Real.exp_monotone (hP.read_price y U))
  have hunit (U : Config G (C.side datum.level datum.period)) :
      ‖Poly.pass (-(model.read (testInclusion D y) g U))‖ ≤ B :=
    (hnorm _).trans (mul_le_mul_of_nonneg_right (hprice U) hk)
  let a (s : R.Mode) : ℂ := ∏ v ∈ s.val, c v
  let A : ℝ := ∑ s : R.Mode, ‖a s‖
  have hA : 0 ≤ A := sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨Poly.pass_cont.measurable.comp (packet_read_measurable model x g).neg,
    A * B, fun U => ?_⟩
  change ‖(Poly.pass (-(model.read x g U))).part‖ ≤ A * B
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA hB)).2
  intro s
  have hp := hF.inverse_multiplier_published hP hg U s
  have he := letter_coordinate_smul hp c (testInclusion D y)
  rw [← hx] at he
  rw [he, norm_mul]
  have ha : ‖a s‖ ≤ A := single_le_sum (fun _ _ => norm_nonneg _) (mem_univ s)
  have hv : ‖(Poly.pass (-(model.read (testInclusion D y) g U))).part s‖ ≤ B :=
    (norm_le_pi_norm (Poly.part (Poly.pass (-(model.read (testInclusion D y) g U)))) s).trans
      (hunit U)
  exact mul_le_mul ha hv (norm_nonneg _) hA

/-- The complete inverse model is integrable under the original normalized
history law, with no new estimate on a represented residual. -/
theorem PrescribedPackets.actual_inverse_model_integrable
    (hF : PrescribedPackets Y datum inputColors model order) (hC : C.Makes)
    (hP : model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)
    (x : TestSpace D) :
    Integrable (fun U => Poly.pass (-(model.read x
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U)))
      (OPE.Therm.scene C.path datum.cutoff datum.period datum.level) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2
      (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  letI : IsProbabilityMeasure
      (OPE.Therm.scene C.path datum.cutoff datum.period datum.level) :=
    OPE.Therm.probability hC.wilson datum.below.le
  obtain ⟨hmeas, B, hB⟩ := hF.inverse_multiplier_envelope hP hg x
  exact Integrable.of_bound hmeas.aestronglyMeasurable B (ae_of_all _ hB)

/-- The inverse model also has genuine L1 for the unnormalized transport
input, with the original full vacuum density still present. -/
theorem PrescribedPackets.actual_inverse_model_weighted_integrable
    (hF : PrescribedPackets Y datum inputColors model order) (hC : C.Makes)
    (hP : model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)
    (x : TestSpace D) :
    Integrable (fun U => (C.path.rep datum.cutoff datum.period datum.level).eval U •
      Poly.pass (-(model.read x
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1)) U)))
      (prior G (C.side datum.level datum.period)) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2
      (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  have hm := hF.inverse_multiplier_envelope hP hg x
  have hv := (C.path.rep datum.cutoff datum.period datum.level).envelope
    (hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  obtain ⟨B, hB⟩ := hm.cost
  obtain ⟨K, hK⟩ := hv.cost
  refine Integrable.of_bound (hv.meas.smul hm.meas).aestronglyMeasurable
    (K * B) (ae_of_all _ fun U => ?_)
  rw [norm_smul]
  exact mul_le_mul (hK U) (hB U) (norm_nonneg _)
    ((norm_nonneg _).trans (hK U))

end Formal

end YM.Integration.LocalComparison
end
