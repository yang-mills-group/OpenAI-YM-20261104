import YangMills.WilsonProof.NativeSupport.IssuedBridge.WilsonQ198PublicPostCentres
import YM.Integration.WilsonQ198PhysicalPhaseWords
import YM.GradedFar.Lay
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace IssuedBridge.WilsonQ198PostFrankValue
open YM YM.Integration Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FVA2 FVA2.Register FVA2.Scale Maxwell XSpace XSpace.Normalize
open WilsonNestedReportedCharacterCurrentBayQ198Physical
open scoped Topology Classical BigOperators
open Function Filter Set PowerSeries
open YM.Integration.GradedFar
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets
open FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Tariff YM.Integration.GradedFar.Tariff.Sunshine
open scoped Topology BigOperators Classical ContDiff

universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {n : ℕ}
theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {κ : ℝ}
    (fund : FundedOriginalProperties.{u} hG κ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    {b : ℕ} (hb : 0 < b) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower S)
    (Z : WilsonPrescription G) (lead : Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, Frame.obedient F A (J r) d)
    {K : Set (Points n)} (compact : IsCompact K) (safe : K ⊆ conf n)
    {θ : ℝ → ℝ} (heat : Trace.Pilot.Coupling G θ) {γ : ℝ} (hγ : γ < 4)
    (pos : ∀ᶠ r in Trace.Pilot.trail, 0 < r) (h : ℕ) (v : ListInput G n h) :
    WilsonQ198PhysicalPhaseWords.Priced F (WilsonPositionHomogeneousFrame.homogeneous F J Z)
      K (fun _ x _ => x) γ [] h v := by
  intro ε hε
  let w : (i : Fin n) → Free R.family (Ceiling n h i) :=
    fun i => (Maxwell.Free.fields R.family.labels h).symm (v i)
  let C : ℝ := ∏ i, ‖w i‖
  have hC : 0 ≤ C := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hd : 0 < 1 + C := by linarith
  have he : 0 < ε / (1+C) := div_pos hε hd
  have H := IssuedBridge.WilsonQ198PublicPostCentres.original hG W fund pace hb F fac Q J Z
    lead paid (Ceiling n h) compact safe heat hγ he
  filter_upwards [H, pos] with r hr hrpos
  intro x hx o t u
  let P := WilsonPositionHomogeneousFrame.homogeneous F J Z
  have ht := _root_.YM.Integration.GradedFar.Tariff.atTable_within F P t (Ceiling n h) v o hrpos (safe hx)
  have hu := _root_.YM.Integration.GradedFar.Tariff.atTable_within F P u (Ceiling n h) v o hrpos (safe hx)
  change ‖S.classMoment (spectator F t) (Ceiling n h) (r • x) (labels P r v) -
    S.classMoment (spectator F u) (Ceiling n h) (r • x) (labels P r v)‖ ≤ ε * r^γ
  rw [ht, hu]
  calc
    _ ≤ (ε / (1+C)) * r^γ * C := hr x hx o t u w
    _ = (ε * (C / (1+C))) * r^γ := by ring
    _ ≤ ε * r^γ := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hε.le ((div_le_one hd).2 (by linarith))) (Real.rpow_nonneg hrpos.le _)

end IssuedBridge.WilsonQ198PostFrankValue
