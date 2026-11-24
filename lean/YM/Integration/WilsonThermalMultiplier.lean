import YM.Integration.WilsonThermalPacketSum
import YM.Integration.WilsonPolynomialResponse

/-! Compare the full original marked gas multiplier to the matching low-curvature field value on the same regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermalMultiplier
open MeasureTheory Filter Set Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets Push.AbsoluteSums
open WilsonThermalPacketSum WilsonPolynomialResponse
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
variable {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
variable {P : MarkedPackets D G n R} {g width budget : ℝ} {w : V → ℝ}
variable {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {off cov : ℕ} (H : P.Paid p address region w g width budget off cov)
variable (x : IndependentTests D) (c cap : ℕ) (hcap : P.rankCap ≤ cap)

def tracks (P : MarkedPackets D G n R) (x : IndependentTests D) (g : ℝ) (c : ℕ) (Q : Config G n) : Prop :=
  (∀ i U, P.rank i < c → P.term (testInclusion D x) g U i = P.term (testInclusion D x) g Q i) ∧
    (∀ i, c ≤ P.rank i → P.term (testInclusion D x) g Q i = 0)

include H hcap in
theorem read (Q U : Config G n) (hq : tracks P x g c Q) :
    P.read (testInclusion D x) g U - P.read (testInclusion D x) g Q = high P g x c U := by
  have a := (H.uniform_read cap hcap x U).1
  have b := (H.uniform_read cap hcap x Q).1
  unfold MarkedPackets.read high
  rw [←a.tsum_sub b]
  apply tsum_congr
  intro i
  by_cases hr : c ≤ P.rank i
  · simp only [token,hr,if_true,hq.2 i hr,Poly.send_zero,sub_zero]
  · simp only [token,if_neg hr,hq.1 i U (lt_of_not_ge hr),sub_self]

theorem slope_nonneg (m : ℕ) {A : ℝ} (ha : 0 ≤ A) : 0 ≤ slope m A :=
  Finset.sum_nonneg fun _ _ => div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)

include H hcap in
theorem expected (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (Q : Config G n)
    (hq : tracks P x g c Q) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ) :
    (∫ U, Poly.price w (Poly.pass (P.read (testInclusion D x) g U) -
        Poly.pass (P.read (testInclusion D x) g Q)) ∂μ) ≤
      slope (Fintype.card V) (uniformReadCost cap (Fintype.card V) budget) *
        cost c cap (Fintype.card V) t δ budget := by
  let K := slope (Fintype.card V) (uniformReadCost cap (Fintype.card V) budget)
  have hK : 0 ≤ K := slope_nonneg _ ((Poly.nonnegative H.positive _).trans (H.uniform_read cap hcap x Q).2)
  apply dominated x H μ c cap hcap t δ ht hd rare _ K hK (fun _ => Poly.nonnegative H.positive _)
  intro U
  have h := multiplier H.positive (H.uniform_read cap hcap x U).2 (H.uniform_read cap hcap x Q).2
  rw [read H x c cap hcap Q U hq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (price x H c cap hcap U) hK)

end YM.Integration.WilsonThermalMultiplier
end
