import YM.Integration.WilsonThermalReadout
import YM.Integration.WilsonInvariantPacketRanks

/-! On the original simple gauge group, the complete subseries below two
curvature insertions is exactly its value at the identity field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFlatPacketSource
open MeasureTheory Finset Lattice Wilson RG Marker OPE.Therm
open Comparison.Density.RenderM LocalComparison LocalComparison.MarkedPackets
open WilsonThermalPacketSum WilsonThermalMultiplier WilsonThermalReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
variable {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
variable {P : MarkedPackets D G n R} {w : V → ℝ} {g width budget : ℝ}
variable {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {off cov : ℕ} (H : P.Paid p address region w g width budget off cov)
variable (x : IndependentTests D)

omit [Fintype V] in
include H in
theorem positive (i : ℕ) (hr : 0 < P.rank i) :
    P.term (testInclusion D x) g (1:Config G n) i = 0 := by
  cases hi : P.packet i with
  | none => simp [MarkedPackets.term,hi]
  | some T =>
    have hface (z : Face (Per n)) : faceValue (1:Config G n) z = 1 := by simp [faceValue,travel,square]
    have he := WilsonCurvatureEndpoints.cold T (testInclusion D x) ((H.coefficient i T hi).2 x) 0
      le_rfl (1:Config G n) (fun j => by rw [hface,G.chord_one])
    rw [zero_pow hr.ne',mul_zero] at he
    simp only [MarkedPackets.term,hi,norm_le_zero_iff.mp he,mul_zero]

omit [Fintype V] in
include H in
theorem lowest (hG : G.Simple) : tracks P x g 2 (1:Config G n) := by
  refine ⟨?_,fun i hi => positive H x i (by omega)⟩
  intro i U hi
  rcases (show P.rank i = 0 ∨ P.rank i = 1 by omega) with h | h
  · exact WilsonInvariantPacketRanks.zero h _ _ _ _
  · rw [WilsonInvariantPacketRanks.one hG H h,WilsonInvariantPacketRanks.one hG H h]

include H in
theorem subseries (hG : G.Simple) (cap : ℕ) (hr : P.rankCap ≤ cap) (U : Config G n) :
    low P g x 2 U = P.read (testInclusion D x) g (1:Config G n) := by
  unfold low
  rw [←read H x 2 cap hr 1 U (lowest H x hG)]
  abel

include H in
theorem signed (hG : G.Simple) (μ : Measure (Config G n)) [IsProbabilityMeasure μ]
    (cap : ℕ) (hr : P.rankCap ≤ cap) (t δ : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ δ)
    (rare : ∀ z : Face (Per n), μ.real (trigger z t) ≤ δ)
    (probe : Config G n → ℂ) (hm : Measurable probe) (hp : ∀ U, ‖probe U‖ ≤ 1)
    (L : Poly R →L[ℂ] ℂ) (hL : ∀ p, ‖L p‖ ≤ Poly.price w p) :
    let F := fun U => probe U * L (Poly.pass (P.read (testInclusion D x) g U) -
      Poly.pass (P.read (testInclusion D x) g (1:Config G n)))
    Integrable F μ ∧ ‖∫ U, F U ∂μ‖ ≤ amplifier 2 cap (Fintype.card V) budget *
      cost 2 cap (Fintype.card V) t δ budget := by
  simpa only [gap,subseries H x hG cap hr] using
    tested x H μ 2 cap hr t δ ht hd rare probe hm hp L hL

end YM.Integration.WilsonFlatPacketSource
end
