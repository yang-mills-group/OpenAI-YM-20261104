import YM.Integration.WilsonThermalMultiplier

/-! Truncate by the number of genuine curvature insertions on every original
walk. Test the complete nonlinear difference against any bounded Borel phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermalReadout

open MeasureTheory Filter Set Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open WilsonThermalPacketSum WilsonPolynomialResponse
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
variable {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
variable (P : MarkedPackets D G n R) (g : ℝ) (x : IndependentTests D)

def low (c : ℕ) (U : Config G n) : Poly R :=
  P.read (testInclusion D x) g U - high P g x c U

def gap (c : ℕ) (U : Config G n) : Poly R :=
  Poly.pass (P.read (testInclusion D x) g U) - Poly.pass (low P g x c U)

omit [Fintype V] in
theorem atom (i : ℕ) : Continuous (fun U : Config G n =>
    Poly.send (P.mode i) (P.term (testInclusion D x) g U i)) := by
  change Continuous (fun U : Config G n => (Poly.send (P.mode i) (P.term (testInclusion D x) g U i)).part)
  apply continuous_pi
  intro s
  simp only [Poly.part_send]
  by_cases hs : s = P.mode i
  · simp only [if_pos hs]
    cases hi : P.packet i with
    | none =>
      simp only [MarkedPackets.term,hi]
      exact continuous_const
    | some T =>
      simp only [MarkedPackets.term,hi]
      unfold Token.read Token.touch Slot.atSite expandAt
      fun_prop
  · simp only [if_neg hs]
    exact continuous_const

theorem measurable (c : ℕ) : Measurable (gap P g x c) := by
  have m : Measurable (fun U => P.read (testInclusion D x) g U) :=
    Measurable.tsum (fun i => (atom P g x i).measurable)
  have h : Measurable (high P g x c) := by
    apply Measurable.tsum
    intro i
    change Measurable (fun U : Config G n => if c ≤ P.rank i then
      Poly.send (P.mode i) (P.term (testInclusion D x) g U i) else (0:Poly R))
    by_cases hi : c ≤ P.rank i
    · simpa only [if_pos hi] using (atom P g x i).measurable
    · simp only [if_neg hi]
      exact measurable_const
  exact (Poly.pass_cont.measurable.comp m).sub (Poly.pass_cont.measurable.comp (m.sub h))

variable {P g} {w : V → ℝ} {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {width budget : ℝ} {off cov : ℕ} (H : P.Paid p address region w g width budget off cov)

include H in
theorem low_eq (c cap : ℕ) (hcap : P.rankCap ≤ cap) (U : Config G n) :
    low P g x c U = ∑' i, if P.rank i < c then
      Poly.send (P.mode i) (P.term (testInclusion D x) g U i) else 0 := by
  have h₀ := (H.uniform_read cap hcap x U).1
  have h₁ := (Poly.budgeted H.positive (at_field x H c cap hcap U).2.1 (fun i => (scalar x c i U).le)).1
  unfold low MarkedPackets.read high
  rw [←h₀.tsum_sub h₁]
  apply tsum_congr
  intro i
  by_cases hi : c ≤ P.rank i
  · simp [token,hi,not_lt.mpr hi]
  · simp [token,hi,lt_of_not_ge hi]

def amplifier (c cap marks : ℕ) (budget : ℝ) : ℝ :=
  slope marks (uniformReadCost cap marks budget + cost c cap marks 2 0 budget)

include H in
theorem field (c cap : ℕ) (hcap : P.rankCap ≤ cap) (U : Config G n) :
    Poly.price w (gap P g x c U) ≤ amplifier c cap (Fintype.card V) budget *
      ∑' i, entry P w g x c i U := by
  let f := P.read (testInclusion D x) g U
  let h := high P g x c U
  let A := uniformReadCost cap (Fintype.card V) budget
  let B := cost c cap (Fintype.card V) 2 0 budget
  have hF : Poly.price w f ≤ A := (H.uniform_read cap hcap x U).2
  have hp : Poly.price w h ≤ ∑' i, entry P w g x c i U := price x H c cap hcap U
  have hC := at_field x H c cap hcap U
  have hneg : Poly.price w (-h) = Poly.price w h := by simp only [Poly.price,Poly.part_neg,norm_neg]
  have hl : Poly.price w (f-h) ≤ A+B := by
    rw [sub_eq_add_neg]
    have u := Poly.addition H.positive f (-h)
    rw [hneg] at u
    exact u.trans (add_le_add hF (hp.trans hC.2.2))
  have hB : 0 ≤ B := budget_nonneg hC
  have hA : 0 ≤ A := (Poly.nonnegative H.positive _).trans hF
  have hK := WilsonThermalMultiplier.slope_nonneg (Fintype.card V) (add_nonneg hA hB)
  have q := multiplier H.positive (hF.trans (le_add_of_nonneg_right hB)) hl
  have ident : f-(f-h)=h := by abel
  rw [ident] at q
  exact q.trans (mul_le_mul_of_nonneg_left hp hK)

include H in
theorem tested (μ : Measure (Config G n)) [IsProbabilityMeasure μ]
    (c cap : ℕ) (hcap : P.rankCap ≤ cap) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ)
    (probe : Config G n → ℂ) (hm : Measurable probe) (hr : ∀ U, ‖probe U‖ ≤ 1)
    (L : Poly R →L[ℂ] ℂ) (hL : ∀ p, ‖L p‖ ≤ Poly.price w p) :
    let F := fun U => probe U * L (gap P g x c U)
    Integrable F μ ∧ ‖∫ U, F U ∂μ‖ ≤ amplifier c cap (Fintype.card V) budget *
      cost c cap (Fintype.card V) t δ budget := by
  let K := amplifier c cap (Fintype.card V) budget
  let C := cost c cap (Fintype.card V) 2 0 budget
  have hc := at_field x H c cap hcap (1:Config G n)
  have h0 := (Poly.nonnegative H.positive _).trans (H.uniform_read cap hcap x (1:Config G n)).2
  have hK : 0 ≤ K := WilsonThermalMultiplier.slope_nonneg _ (add_nonneg h0 (budget_nonneg hc))
  let F := fun U => probe U * L (gap P g x c U)
  have measF : Measurable F := hm.mul (L.continuous.measurable.comp (measurable P g x c))
  have bound (U : Config G n) : ‖F U‖ ≤ K * ∑' i, entry P w g x c i U := by
    calc _ = ‖probe U‖ * ‖L (gap P g x c U)‖ := norm_mul _ _
         _ ≤ ‖L (gap P g x c U)‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hr U) (norm_nonneg _)
         _ ≤ _ := (hL _).trans (field x H c cap hcap U)
  have hI : Integrable F μ := (integrable_const (K*C)).mono' measF.aestronglyMeasurable
    (ae_of_all _ fun U => (bound U).trans (mul_le_mul_of_nonneg_left (at_field x H c cap hcap U).2.2 hK))
  exact ⟨hI,(norm_integral_le_integral_norm _).trans
    (dominated x H μ c cap hcap t δ ht hd rare (fun U => ‖F U‖) K hK (fun _ => norm_nonneg _) bound)⟩

end YM.Integration.WilsonThermalReadout
end
