import YM.Integration.WilsonMacroscopicPrescribedInputs
import YM.RG17.Gathers

/-! The actual signed product with independently prescribed position fields
and a fixed macroscopic smooth exterior, compared to the measured packet
on the same Wilson hierarchy. Its spatial margin pays every coupling order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicExteriorMeasurement
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T)
  {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
  (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)
  (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
  (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J : ℝ → PhysMS.tower S) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F A (J r) d)
include hG W source pace hB fac Q leading paid

/-- A real reporting layout for the numerical measurement; only its terminal
frame is replaced by the previously chosen position normalization. -/
theorem located : ∃ L : Layout F,
    L.level = WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
    Located (Pier.Lair.tender F L J) ∧ ∀ d : ℕ, Pier.Lair.Paying F (Pier.Lair.tender F L J) d := by
  obtain ⟨u, mantle, L, _, pegs, level, shift, buys, _⟩ :=
    WilsonReportPrescribedFrame.selected hG W source pace hB F fac J leading paid
  have near : RG17.Panoramic.Comparably R L.level :=
    level ▸ WilsonReportPrescribedFrame.comparable hG pace hB
  exact ⟨L,level,(Pier.Lair.seated F (WilsonReportPrescribedFrame.present F J leading paid)
    mantle fac.toServices L pegs near shift Q).1,buys⟩

variable {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
  (X : RG17.External R.family S) {K : Set (Points n)} (compact : IsCompact K) (apart : K ⊆ conf n)
include compact apart

/-- Literal two-test measurement. `appeared` uses the genuine signed
original product, while `charge` uses the original homogeneous reader's
intrinsic output field integrated against precisely the same exterior. -/
theorem signed {g : ℝ → ℝ} (hg : Trace.Pilot.Coupling G g) (H q : ℕ) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) : ∀ᶠ r in Trace.Pilot.trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
    let u := fun i => J r (d i) (v i)
    ‖RG17.appeared F u X r ψ - X.charge F H (RG17.basket Q H u r ψ)‖ ≤
      ε*g r^q*r^((H:ℝ)+1-σ)*(∫ z : Points (X.n+1), ‖X.test z‖)*(∫ z : Points n, ‖ψ z‖) := by
  obtain ⟨L,_,loc,_⟩ := located hG W source pace hB F fac Q J leading paid
  let Z := Pier.Lair.tender F L J
  have ext := RG17.exteriorBound Q Z fac.toServices loc X (fun i => Sum.inr (v i)) H compact apart (half_pos hσ)
  have tariff := PhysMS.subpower_payment hg hG 1 (σ/2) (half_pos hσ) ε hε q
  filter_upwards [ext, tariff, RG17.positiveLength] with r ht price pos
  intro ψ support
  have bound := ht ψ support
  have budget : r^((H:ℝ)+1-σ/2) ≤ ε*g r^q*r^((H:ℝ)+1-σ) := by
    rw [one_mul] at price
    rw [show (H:ℝ)+1-σ/2=σ/2+((H:ℝ)+1-σ) by ring, Real.rpow_add pos]
    exact mul_le_mul_of_nonneg_right price (Real.rpow_nonneg pos.le _)
  exact bound.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right budget
    (integral_nonneg fun z=>norm_nonneg (X.test z))) (integral_nonneg fun z=>norm_nonneg (ψ z)))

end YM.Integration.WilsonMacroscopicExteriorMeasurement
