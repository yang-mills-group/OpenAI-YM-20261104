import YM.Integration.WilsonAddressedEquationMoments
import YM.Integration.WilsonAddressedCollarEquations
import YM.Integration.WilsonAddressedEquationCourse
import YM.Integration.WilsonSeparatedOffsetSites
import YM.Integration.WilsonOriginalThermometerFineCells

/-! Remove the actual Haar equation from the projected product on the original
Wilson law. The tested difference is then the measured field minus the signed
equation mismatch on each leg. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerReverseWard
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
local notation "χ" r:max N:max p:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,p)
local notation "wt" => WilsonSeparatedOriginalThermometerCells.weight
include W portfolio issued

theorem single :
    ∀ d, ∃ radius : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ) (x : R.family.label d)
        (o : Site (R.family.side N p)) (X : Config G (R.family.side N p) → ℂ),
        LocalOn (Mark.Outer radius o) X → Envelope X →
        moment (R.family.beta N p) (fun U =>
          incoming R.family (V d) N p (P d (N,p)) (x - b.step d (N,p) x) o U * X U) = 0 := by
  intro d
  obtain ⟨r,M,vanish⟩ := Mark.radiusH W (V d) (portfolio d)
  refine ⟨r,?_⟩
  filter_upwards [Mark.lengths R.family.S M] with N size
  intro p x o X away bounded
  have member := (issued.foundation.step d N p).id_sub x
  obtain ⟨y,hy,raw⟩ := member
  change bindP R.family W d N p (P d (N,p)) y = x - b.step d (N,p) x at raw
  rw [← raw,evaluated]
  have active : 0 < R.family.beta N p :=
    (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed _))).trans_le
      ((R.makes.wilson.represents N p N le_rfl).band.1)
  exact ((vanish y hy).scale (((R.family.S.a N:ℂ)^d)⁻¹))
    (R.family.side N p) (size p) o (R.family.beta N p) active.ne' X away bounded

theorem projected : ∃ radius : ℕ → ℕ,
    ∀ (I : Type) [Fintype I] (d : I → ℕ), ∀ᶠ N : ℕ in atTop,
        ∀ (p : ℕ) (x : (i : I) → R.family.label (d i)) (o : I → Site (R.family.side N p))
        (X : Config G (R.family.side N p) → ℂ), Avoids V radius d o →
        (∀ i, LocalOn (Mark.Outer (radius (d i)) (o i)) X) → Envelope X →
        moment (R.family.beta N p) (fun U =>
          (∏ i, R.family.O N p (b.step (d i) (N,p) (x i)) (o i) U) * X U) =
        moment (R.family.beta N p) (fun U =>
          (∏ i, (R.family.O N p (x i) (o i) U -
            residual R.family (V (d i)) N p (P (d i) (N,p)) (x i-b.step (d i) (N,p) (x i)) (o i) U)) * X U) := by
  choose radius null using single R V W P b portfolio issued
  refine ⟨radius,fun I _ d => ?_⟩
  filter_upwards [eventually_all.mpr (fun i:I => null (d i))] with N star
  intro p x o X separated localX bounded
  let H i := R.family.O N p (b.step (d i) (N,p) (x i)) (o i)
  let J i := incoming R.family (V (d i)) N p (P (d i) (N,p))
    (x i-b.step (d i) (N,p) (x i)) (o i)
  have hH (i:I) := R.family.continuousO N p (d i) (b.step (d i) (N,p) (x i)) (o i)
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
    (fun i Z => star i p (x i) (o i) Z) Finset.univ X bounded (fun i _ => localX i)
  have atField (i : I) (U) : R.family.O N p (x i) (o i) U -
      residual R.family (V (d i)) N p (P (d i) (N,p)) (x i-b.step (d i) (N,p) (x i)) (o i) U =
      H i U + J i U := by
    have hr := congrFun (restore (V (d i)) N p (P (d i) (N,p)) b (x i) (o i)) U
    change H i U + _ = R.family.O N p (x i) (o i) U - J i U at hr
    linear_combination -hr
  simp only [atField]
  simpa only [Pi.add_apply,add_sub_cancel_right] using erased.symm

end YM.Integration.WilsonThermometerReverseWard
