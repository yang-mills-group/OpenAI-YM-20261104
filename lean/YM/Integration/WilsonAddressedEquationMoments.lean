import YM.Integration.WilsonAddressedCollarEquations
import YM.Integration.WilsonAddressedEquationCourse
import YM.Integration.WilsonSeparatedOffsetSites
import YM.Integration.WilsonOriginalThermometerFineCells

/-! Clear the original Wilson equation stencils on every occupied microscopic
    placement before returning the complete graded reading on a coarser cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedEquationMoments
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

private theorem single :
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

theorem faces : ∃ radius : ℕ → ℕ,
    ∀ (I : Type) [Fintype I] (d : I → ℕ), ∀ᶠ N : ℕ in atTop,
        ∀ (p : ℕ) (x : (i : I) → R.family.label (d i)) (o : I → Site (R.family.side N p))
        (X : Config G (R.family.side N p) → ℂ), Avoids V radius d o →
        (∀ i, LocalOn (Mark.Outer (radius (d i)) (o i)) X) → Envelope X →
        moment (R.family.beta N p) (fun U => (∏ i, R.family.O N p (x i) (o i) U) * X U) =
        moment (R.family.beta N p) (fun U =>
          (∏ i, corrected R.family (V (d i)) N p (P (d i) (N,p)) b (x i) (o i) U) * X U) := by
  choose radius null using single R V W P b portfolio issued
  refine ⟨radius,fun I _ d => ?_⟩
  filter_upwards [eventually_all.mpr (fun i:I => null (d i))] with N star
  intro p x o X separated localX bounded
  let A i := R.family.O N p (x i) (o i)
  let D i := incoming R.family (V (d i)) N p (P (d i) (N,p)) (x i-b.step (d i) (N,p) (x i)) (o i)
  have result := WilsonSignedEquationProducts.erase (R.family.beta N p)
    (fun i => Mark.Outer (radius (d i)) (o i)) A D
    (fun i => R.family.continuousO N p (d i) (x i) (o i))
    (fun i => incoming_continuous ..)
    (fun i j h => ⟨fun U Z agreed => R.family.localO N p (d j) (x j) (o j) U Z
        (agrees_mono agreed (separated i j h).1),
      fun U Z agreed => incoming_local _ _ _ _ _ _ U Z (agrees_mono agreed (separated i j h).2)⟩)
    (fun i X => star i p (x i) (o i) X) Finset.univ X bounded (fun i _ => localX i)
  simp_rw [restore]
  exact result

def Placed : Prop :=
    ∀ (φ : Test 3), tsupport φ ⊆ conf 3 → ∃ (K : ℝ) (p₀ : ℕ), 0 < K ∧
      ∀ᶠ N : ℕ in atTop, ∀ p ≥ p₀, ∀ r : ℝ, 0 < r → r ≤ 1 → R.family.S.a N * K ≤ r →
      ∀ (A : Group R.family 6) {w : ℕ} (wN : w ≤ N) (read : (Badge → ℂ) → ℂ),
        let cell := R.family.S.toDepth wN p
        φ.applyTo (fun y => read (row A (N,p) ((χ r N p) y))) =
          ∑ parent : Fin 3 → Site (R.family.side w p), ∑ t : Fin 3 → Site cell.count,
            let o := fun i => cell.assemble (parent i,t i)
            wt φ (χ r N p) o * read (correctedRow R V P b A (N,p) o)

theorem placed : Placed R V P b := by
  obtain ⟨radius,erase⟩ := faces R V W P b portfolio issued
  intro φ legal
  obtain ⟨K,p₀,pos,geometric⟩ := clearance R V radius φ legal
  refine ⟨K,p₀,pos,?_⟩
  filter_upwards [geometric,erase (Fin 3) (fun i=> (grade i).val)] with N geo cancel p hp r hr cap mesh A w wN read
  let z : UVIndex := (N,p)
  have fold := (WilsonAddressedCollarFolds.original A r z wN φ read).1
  rw [fold]
  apply Finset.sum_congr rfl
  intro parent _
  apply Finset.sum_congr rfl
  intro t _
  let cell := R.family.S.toDepth wN p
  let o := fun i => cell.assemble (parent i,t i)
  by_cases live : wt φ (χ r N p) o = 0
  · change wt φ (χ r N p) o * _ = wt φ (χ r N p) o * _
    simp only [live,zero_mul]
  · change wt φ (χ r N p) o * read (row A z o) = _ * read (correctedRow R V P b A z o)
    congr 1
    apply congrArg read
    funext s
    let v := fun i : Fin 3 => A.station.wheel.atCut z (index A (grade i)) (vector A s i)
    have fixed := cancel p v o (fun _ => 1) (geo p hp r hr cap mesh o live)
      (fun _ _ _ _ => rfl) (Mark.cont_envelope continuous_const)
    rw [WilsonPositionThermometerJointFaces.ensemble]
    change Wilson.moment (R.family.beta N p) (fun U => ∏ i, R.family.O N p (v i) (o i) U) =
      Wilson.moment (R.family.beta N p) (fun U => ∏ i,
        corrected R.family (V ((grade i).val)) N p (P ((grade i).val) (N,p)) b (v i) (o i) U)
    simp only [mul_one] at fixed
    convert fixed using 3
    congr

end YM.Integration.WilsonAddressedEquationMoments
