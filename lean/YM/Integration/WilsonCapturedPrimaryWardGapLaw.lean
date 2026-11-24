import YM.Integration.WilsonCapturedPrimaryWardFile

/-! Compare two original finite field coordinates with the same marked projection on the measured law. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardGapLaw
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox OPE OPE.Orbits
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonOffsetReportingProducts
open scoped Classical BigOperators Topology
open WilsonAddressedCollarEquations WilsonOffsetEquationLaw WilsonAddressedEquationShelf
open PhysicalNext.Repeat Legato Bandage
variable {G : Gauge} (R : Run G)
variable (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)
  (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
  (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
include W portfolio issued

theorem original : ∃ radius : ℕ → ℕ,
    ∀ (I : Type) [Fintype I] (d : I → ℕ), ∀ᶠ N : ℕ in atTop,
        ∀ (p : ℕ) (x y : (i : I) → R.family.label (d i)) (o : I → Site (R.family.side N p))
        (X : Config G (R.family.side N p) → ℂ), (∀ i,b.step (d i) (N,p) (x i)=b.step (d i) (N,p) (y i)) → Avoids V radius d o →
        (∀ i, LocalOn (Mark.Outer (radius (d i)) (o i)) X) → Envelope X →
        moment (R.family.beta N p) (fun U =>
          (∏ i, R.family.O N p (y i) (o i) U) * X U) =
        moment (R.family.beta N p) (fun U =>
          (∏ i, (R.family.O N p (x i) (o i) U -
            residual R.family (V (d i)) N p (P (d i) (N,p)) (x i-y i) (o i) U)) * X U) := by
  choose radius null using WilsonThermometerReverseWard.single R V W P b portfolio issued
  refine ⟨radius,fun I _ d => ?_⟩
  filter_upwards [eventually_all.mpr (fun i:I => null (d i))] with N star
  intro p x y o X sharing separated localX bounded
  let H i := R.family.O N p (y i) (o i)
  let J i := incoming R.family (V (d i)) N p (P (d i) (N,p))
    (x i-y i) (o i)
  have hH (i:I) := R.family.continuousO N p (d i) (y i) (o i)
  have hJ (i:I) : Continuous (J i) := incoming_continuous ..
  have erased := WilsonSignedEquationProducts.erase (R.family.beta N p)
    (fun i => Mark.Outer (radius (d i)) (o i)) (fun i=>H i+J i) J
    (fun i => (hH i).add (hJ i)) hJ
    (fun i j h => by
      have h₁ : LocalOn (Mark.Outer (radius (d i)) (o i)) (H j) :=
        fun U Z agreed=>R.family.localO N p (d j) _ (o j) U Z (agrees_mono agreed (separated i j h).1)
      have h₂ : LocalOn (Mark.Outer (radius (d i)) (o i)) (J j) :=
        fun U Z agreed=>incoming_local _ _ _ _ _ _ U Z (agrees_mono agreed (separated i j h).2)
      exact ⟨fun U Z agreed=>congr_arg₂ (·+·) (h₁ U Z agreed) (h₂ U Z agreed),h₂⟩)
    (fun i Z outside boundedZ => by
      simpa only [map_sub,sharing i,sub_self,sub_zero,J] using
        star i p (x i-y i) (o i) Z outside boundedZ)
    Finset.univ X bounded (fun i _ => localX i)
  have atField (i : I) (U) : R.family.O N p (x i) (o i) U -
      residual R.family (V (d i)) N p (P (d i) (N,p)) (x i-y i) (o i) U =
      H i U + J i U := by
    have linear := ((R.family.linearO N p (d i) (o i)).mk' _).map_sub (x i) (y i)
    change R.family.O N p (x i-y i) (o i) = R.family.O N p (x i) (o i)-R.family.O N p (y i) (o i) at linear
    simp only [WilsonOffsetReportingProducts.residual,linear,Pi.sub_apply,H,J]
    change _ = R.family.O N p (y i) (o i) U + _
    ring
  simp only [atField]
  simpa only [Pi.add_apply,add_sub_cancel_right] using erased.symm

end YM.Integration.WilsonCapturedPrimaryWardGapLaw
