import YM.Integration.WilsonGraphUniformMixedShapeMass
import YM.Integration.WilsonGraphAppointedMixedShapeJets
import YM.Integration.WilsonGraphMeasuredCompactCorrelation

noncomputable section
namespace YM.Integration.WilsonGraphAppointedPhysicalShapePrice

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open _root_.IssuedBridge
open scoped Topology BigOperators Classical ContDiff

universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : Axis}
variable {O : OrderS g.core} {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable {R : PhysicalNext.Repeat.Legato.Run g.core}
variable (Z : WilsonPrescription g.core) (V : Vision E ξ) (Q : Perspective H Z true)
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion
local notation "t" => V.T Z
local notation "Cvt" => PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1)

/-- The charged finite signed polynomial uses one original external heat conversion and
one substitution of the coupling on the independently chosen graph data. -/
theorem series (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    {n : ℕ} (d : Caps n) (u : FVA2.GradedFar.Inputs g.core d) (p : ℕ) (s : ℝ) :
    EqOn (fun y => FVA2.GradedFar.crop p s
        (sent X (publicDegree d) y (FVA2.GradedFar.raised (publicWithin d) u)))
      (fun y => publicTruncation Cvt (publicLetters d u) y p s) (conf n) := by
  intro y hy
  let x : Scale.Stage n := ⟨y,hy⟩
  have same := WilsonGraphAppointedStationaryPrices.polynomialAt Z Q (publicDegree d)
    (FVA2.GradedFar.raised (publicWithin d) u) (FVA2.Teller.logNu 1) x p s
  exact same.symm.trans (publicMixedPolynomial (R := R) Z Q.MS Q.matching paid d u x p s)

private theorem transfer {n j : ℕ} {a b c : Points n → ℂ} {x : Points n} {D : ℝ}
    (same : b =ᶠ[𝓝 x] c) (price : YangMills.Matching.shapeJetEstimateAt j a b x D) :
    YangMills.Matching.shapeJetEstimateAt j a c x D := by
  refine ⟨price.1, price.2.1.congr_of_eventuallyEq same.symm, ?_⟩
  intro k hk
  have equal : (fun y => a y - b y) =ᶠ[𝓝 x] (fun y => a y - c y) :=
    Filter.EventuallyEq.rfl.sub same
  rw [← (equal.iteratedFDeriv ℝ k).eq_of_nhds]
  exact price.2.2 k hk

/-- Fixed-vector form, simultaneously on every physical center, viewer, and
point of the separated compact, for the nominated public conversion. -/
theorem fixed (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n : ℕ} (d : Caps n) (u : FVA2.GradedFar.Inputs g.core d)
    (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n) (p j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
      YangMills.Matching.shapeJetEstimateAt j
        (fun y => TrueCompact V.pupil.last (V.Post Z) viewer (r s) o y u)
        (fun y => publicTruncation Cvt (publicLetters d u) y p (t (r s)))
        x (A * |t (r s)| ^ (p+1)) := by
  obtain ⟨A,hA,hp⟩ := WilsonGraphAppointedMixedShapeJets.original Z V Q l r scale
    (publicWithin d) u K hK separated p j
  refine ⟨A,hA,?_⟩
  filter_upwards [hp] with s price
  intro viewer o x hx
  have localEq := (show ∀ᶠ y in 𝓝 x, y ∈ conf n from (conf_open n).mem_nhds (separated hx)).mono fun y hy =>
    series (R := R) Z Q paid d u p (t (r s)) hy
  exact transfer localEq (price viewer o x hx)

/-- The group determines the two external MS inputs before the election. The same
perspective prices all arities, grades, cutoffs, shape orders and separated compacts. -/
theorem appointed (R : PhysicalNext.Repeat.Legato.Run g.core) (hg : g.IsSimple) (V : Vision E ξ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let M := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = M ∧ Vision.StandaloneCorrelation V Z M ∧
      ∀ {ι : Type} (l : Filter ι) (r : ι → ℝ), Tendsto r l trail →
      ∀ {n : ℕ} (d : Caps n) (u : FVA2.GradedFar.Inputs g.core d) (K : Set (Points n)),
        IsCompact K → K ⊆ conf n → ∀ p j : ℕ, ∃ A : ℝ, 0 ≤ A ∧
        ∀ᶠ s in l, ∀ (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
          YangMills.Matching.shapeJetEstimateAt j
            (fun y => TrueCompact V.pupil.last (V.Post Z) viewer (r s) o y u)
            (fun y => publicTruncation
              (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1))
              (publicLetters d u) y p (V.T Z (r s))) x (A * |V.T Z (r s)|^(p+1)) := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨Q,hQ,accepted,hp⟩ := separatedGraphSumOnGroupFiledDatum (R := R) hg V true
  refine ⟨Q,hQ,accepted,?_⟩
  intro ι l r scale n d u K hK separated p j
  have localPaid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1) := by
    rw [hQ]
    exact hp
  exact fixed (R := R) Z V Q localPaid l r scale d u K hK separated p j


theorem uniform (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n : ℕ} (d : Caps n) (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n)
    (p j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
      ∀ v : FVA2.GradedFar.Inputs g.core d, YangMills.Matching.shapeJetEstimateAt j
        (fun y => TrueCompact V.pupil.last (V.Post Z) viewer (r s) o y v)
        (fun y => publicTruncation Cvt (publicLetters d v) y p (t (r s))) x
        (A * WilsonGraphUniformMixedShapeMass.inputMass g v * |t (r s)|^(p+1)) := by
  obtain ⟨A,hA,priced⟩ := WilsonGraphUniformMixedShapeMass.original Z V Q l r scale
    (publicWithin d) K hK separated p j
  refine ⟨A,hA,priced.mono fun s price viewer o x hx v => ?_⟩
  have localEq := (show ∀ᶠ y in 𝓝 x, y ∈ conf n from (conf_open n).mem_nhds (separated hx)).mono
    fun y hy => series (R := R) Z Q paid d v p (t (r s)) hy
  exact transfer localEq (price viewer o x hx v)

theorem capped (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail) (n cap : ℕ)
    (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n) (p j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (d : Caps n), (∀ i, d i ≤ cap) →
      ∀ (v : FVA2.GradedFar.Inputs g.core d) (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
        YangMills.Matching.shapeJetEstimateAt j
          (fun y => TrueCompact V.pupil.last (V.Post Z) viewer (r s) o y v)
          (fun y => publicTruncation Cvt (publicLetters d v) y p (t (r s))) x
          (A * WilsonGraphUniformMixedShapeMass.inputMass g v * |t (r s)|^(p+1)) := by
  classical
  let D := Fin n → Fin (cap+1)
  choose A nonnegative price using fun d : D => uniform (R := R) Z V Q paid l r scale
    (fun i => (d i).val) K hK separated p j
  refine ⟨∑ d : D, A d, Finset.sum_nonneg (fun d _ => nonnegative d), ?_⟩
  filter_upwards [Filter.eventually_all.mpr price] with s allGrades
  intro d within v viewer o x hx
  let ds : D := fun i => ⟨d i, Nat.lt_succ_of_le (within i)⟩
  have charged := allGrades ds viewer o x hx v
  refine ⟨charged.1, charged.2.1, fun k hk => (charged.2.2 k hk).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
  apply mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun d _ => nonnegative d) (Finset.mem_univ ds))
  exact Finset.prod_nonneg fun _ _ => YangMills.Matching.sectorMass_nonneg _

theorem original (R : PhysicalNext.Repeat.Legato.Run g.core) (hg : g.IsSimple) (V : Vision E ξ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let M := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = M ∧ Vision.StandaloneCorrelation V Z M ∧
      ∀ {ι : Type} (l : Filter ι) (r : ι → ℝ), Tendsto r l trail →
      ∀ (n cap : ℕ) (K : Set (Points n)), IsCompact K → K ⊆ conf n → ∀ p j : ℕ,
        ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in l, ∀ (d : Caps n), (∀ i, d i ≤ cap) →
        ∀ (v : FVA2.GradedFar.Inputs g.core d) (viewer : Peers V) (o : E4) (x : Points n), x ∈ K →
          YangMills.Matching.shapeJetEstimateAt j
            (fun y => TrueCompact V.pupil.last (V.Post Z) viewer (r s) o y v)
            (fun y => publicTruncation
              (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1))
              (publicLetters d v) y p (V.T Z (r s))) x
            (A * WilsonGraphUniformMixedShapeMass.inputMass g v * |V.T Z (r s)|^(p+1)) := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨Q,hQ,accepted,hp⟩ := separatedGraphSumOnGroupFiledDatum (R := R) hg V true
  have paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1) := by
    rw [hQ]
    exact hp
  refine ⟨Q,hQ,accepted,?_⟩
  intro ι l r scale n cap K hK separated p j
  exact capped (R := R) Z V Q paid l r scale n cap K hK separated p j

end YM.Integration.WilsonGraphAppointedPhysicalShapePrice

