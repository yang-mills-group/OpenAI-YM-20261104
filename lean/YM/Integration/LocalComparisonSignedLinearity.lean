import YM.Integration.LocalComparisonSignedRemainder
import YM.RG3.Held.Lives

/-!
Subset-wise test linearity of the literal signed remainder. The existing
packet Paid receipt supplies its coefficient tensors, and the existing
formal receipt supplies summability of the complete completion. This does
not construct either receipt, or identify a changed-label atom family with
the fixed test domain. Every product uses the native disjoint-mode algebra.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

open Function MeasureTheory Lattice Wilson RG Marker
open Comparison.Density.RenderM Comparison.RG02 RG3.Held
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {D : V → ComparisonDensity.Address.Orbit}

omit [Fintype V] in
private theorem published_integral {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : TestSpace D → Ω → Poly R)
    (hF : ∀ U, Published (K := ℂ) (fun v => (D v).Mood) (fun x => F x U))
    (hI : ∀ x, Integrable (F x) μ) :
    Published (K := ℂ) (fun v => (D v).Mood) (fun x => ∫ U, F x U ∂μ) := by
  intro s
  have he (x : TestSpace D) : (∫ U, F x U ∂μ).part s =
      ∫ U, (F x U).part s ∂μ := ((Poly.get s).integral_comp_comm (hI x)).symm
  simp_rw [he]
  have hi (x : TestSpace D) : Integrable (fun U => (F x U).part s) μ :=
    (Poly.get s).integrable_comp (hI x)
  constructor
  · intro x y h
    exact integral_congr_ae (ae_of_all _ fun U => (hF U s).stay x y h)
  · intro x i hs a b
    simp_rw [(hF _ s).join x i hs a b]
    exact integral_add (hi _) (hi _)
  · intro x i hs a b
    simp_rw [(hF _ s).scale x i hs a b]
    exact integral_smul a _

variable {n : Side} {M : MarkedPackets D G n R}
    {p : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

omit [Fintype V] in
/-- The fixed paths and the already-paid coefficient tensors give the
literal packet term's dependence on exactly its own marked colors. -/
theorem MarkedPackets.Paid.term_letter
    (h : M.Paid p address region w g width budget coverOffset coverSlope)
    (i : ℕ) (U : Config G n) :
    Letter ℂ (fun v => (D v).Mood) (M.mode i).val
      (fun x => M.term x g U i) := by
  cases hi : M.packet i with
  | none =>
    simp only [MarkedPackets.term, hi]
    exact Letter.still
  | some T =>
    have ht : Letter ℂ (fun v => (D v).Mood) (M.mode i).val
        (fun x => T.read x U) := by
      change Letter ℂ (fun v => (D v).Mood) (M.mode i).val
        (fun x => ∑ j, ((∏ k, (T.path k).atSite U T.root (j k) : ℝ) : ℂ) * T.gem j x)
      exact Letter.total Finset.univ _ (fun j _ => (h.multilinear i T hi j).cmul _)
    simpa only [MarkedPackets.term, hi] using ht.cmul ((g : ℂ) ^ M.power i)

/-- Summability is required on the whole stated test domain. No unit-ball
estimate is used to justify this infinite sum. -/
theorem MarkedPackets.Paid.read_published
    (h : M.Paid p address region w g width budget coverOffset coverSlope)
    (U : Config G n)
    (hs : ∀ x, Summable (fun i => Poly.send (M.mode i) (M.term x g U i))) :
    Published (K := ℂ) (fun v => (D v).Mood) (fun x => M.read x g U) := by
  apply Published.assembly _ ?_ hs
  intro i s
  by_cases he : s = M.mode i
  · subst s
    simp only [Poly.part_send, if_pos]
    exact h.term_letter i U
  · simp only [Poly.part_send, if_neg he]
    exact Letter.still

variable {C : Family G} {datum : LocalFormal.Datum C R}
    {Y : Bulk.Chain C.path}
    {inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period)}
    {model : MarkedPackets D G (C.side datum.level datum.period) R} {order : ℕ}

/-- Native finite nilpotent exponentiation preserves the subset-wise
linearity because only disjoint marked modes multiply. -/
theorem PrescribedPackets.inverse_multiplier_published
    (hF : PrescribedPackets Y datum inputColors model order)
    {p : BudgetPoint} {address : V → Support (C.side datum.level datum.period)}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood)
      (C.side datum.level datum.period)}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : model.Paid p address region w g width budget coverOffset coverSlope)
    (hg : g ≠ 0) (U : Config G (C.side datum.level datum.period)) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => Poly.pass (-(model.read x g U))) := by
  have hr := hP.read_published U (fun x => hF.summable x g hg U)
  have hn : Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => -(model.read x g U)) := by
    simpa only [Published, Pi.smul_apply, neg_one_smul] using hr.smul (-1)
  exact hn.pass

/-- The same physical kernel carries already-established input linearity
through its genuine integrable full-polynomial push. -/
theorem actualPush_published (N period level : ℕ)
    (F : TestSpace D → Config G (C.side (level + 1) period) → Poly R)
    (hF : ∀ U, Published (K := ℂ) (fun v => (D v).Mood) (fun x => F x U))
    (hI : ∀ x, Integrable (F x) (prior G (C.side (level + 1) period)))
    (U : Config G (C.side level period)) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => actualPush C N period level (F x) U) := by
  let S := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  apply published_integral (prior G (C.side (level + 1) period))
    (fun x W => S.density β W U • F x W)
  · intro W
    simpa only [Published, Pi.smul_apply, Complex.coe_smul] using
      (hF W).smul ((S.density β W U : ℝ) : ℂ)
  · intro x
    exact StepData.push_slice (C.path.levels.transition_mass ..) U (F x) (hI x)

variable (hC : C.Makes)
    (F : TestSpace D → Config G (C.side (datum.level + 1) datum.period) → Poly R)
    (hInput : ∀ U, Published (K := ℂ) (fun v => (D v).Mood) (fun x => F x U))
    (hIntegrable : ∀ x, Integrable (F x)
      (prior G (C.side (datum.level + 1) datum.period)))
    (hFormal : PrescribedPackets Y datum inputColors model order)
    {p : BudgetPoint} {address : V → Support (C.side datum.level datum.period)}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood)
      (C.side datum.level datum.period)}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hPaid : model.Paid p address region w
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
      width budget coverOffset coverSlope)

include hC hInput hIntegrable hFormal hPaid

/-- No new model-linearity hypothesis is added: this uses the original Paid
and formal receipts, plus the actual full input's linearity and integrability.
The construction of those receipts remains a separate obligation. -/
theorem actualSignedRemainder_published
    (U : Config G (C.side datum.level datum.period)) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => actualSignedRemainder C datum.cutoff datum.period datum.level F model x U) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
      (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2
      (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  have hm := hFormal.inverse_multiplier_published hPaid hg U
  have hi := actualPush_published datum.cutoff datum.period datum.level F hInput hIntegrable U
  have hv := (Published.one (K := ℂ) (T := fun v => (D v).Mood) (R := R)).smul
    (-((C.path.rep datum.cutoff datum.period datum.level).eval U : ℂ))
  simpa only [Published, actualSignedRemainder, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
    neg_smul, Pi.neg_apply, Pi.one_apply, sub_eq_add_neg] using (hm.product hi).sum hv

/-- Normalization uses the original field-dependent vacuum, which is fixed
with respect to the independent insertion variables. -/
theorem actualNormalizedSignedRemainder_published
    (U : Config G (C.side datum.level datum.period)) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => normalized C datum.cutoff datum.period datum.level
        (actualSignedRemainder C datum.cutoff datum.period datum.level F model x) U) := by
  have h := actualSignedRemainder_published hC F hInput hIntegrable hFormal hPaid U
  simpa only [Published, normalized, Pi.smul_apply, Complex.coe_smul] using
    h.smul ((((C.path.rep datum.cutoff datum.period datum.level).eval U)⁻¹ : ℝ) : ℂ)

end YM.Integration.LocalComparison
