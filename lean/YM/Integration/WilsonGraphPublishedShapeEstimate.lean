import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneMeasuredCorrelationEstimates
import YM.Integration.WilsonGraphAppointedPhysicalShapePrice

noncomputable section
namespace YM.Integration.WilsonGraphPublishedShapeEstimate

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


local notation "B₀" => YangMills.maxwellReference g
local notation "T₀" => YangMills.hierarchy (g := g) V.pupil.last V.pupil.P

theorem sum (S : YangMills.Matching.Conversion B₀) (M : YangMills.MSbar.Coefficients B₀)
    (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g) {n : ℕ}
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) (x : Points n)
    (p : ℕ) (clock : ℝ) :
    publicTruncation S a x p clock =
      ∑ k : Fin (p+1), (clock : ℂ)^k.val * S.correlation M k.val a x := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (clock : ℂ)^k * S.correlation M k a x)]
  simp only [publicTruncation, WilsonGraphStandaloneCorrelation.converted_read S M read]

theorem jetTransport {n j : ℕ} {a b c d : Points n → ℂ} {x : Points n} {D : ℝ}
    (field : a =ᶠ[𝓝 x] c) (reading : b =ᶠ[𝓝 x] d)
    (price : YangMills.Matching.shapeJetEstimateAt j a b x D) :
    YangMills.Matching.shapeJetEstimateAt j c d x D := by
  refine ⟨price.1.congr_of_eventuallyEq field.symm, price.2.1.congr_of_eventuallyEq reading.symm, ?_⟩
  intro k hk
  have equal : (fun y => a y - b y) =ᶠ[𝓝 x] (fun y => c y - d y) := field.sub reading
  rw [← (equal.iteratedFDeriv ℝ k).eq_of_nhds]
  exact price.2.2 k hk

theorem onField (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    (Hₘ : YangMills.Matching.CorrelationOnly.Measurement B₀ T₀)
    (clock : Hₘ.clock =ᶠ[trail] t)
    (M : YangMills.MSbar.Coefficients B₀) (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g)
    (n p j : ℕ) (d : Caps n) (K : Set (Points n)) (hK : IsCompact K)
    (separated : K ⊆ YangMills.WilsonFamily.separated n)
    (field : ∀ᶠ s : ℝ in trail, ∀ (phase : Option (T₀).Character) (v : FVA2.GradedFar.Inputs g.core d)
        (o : E4) (y : Points n), y ∈ conf n →
        (T₀).correlation phase (Hₘ.inputs s (publicLetters d v))
          (WithLp.toLp 2 fun i => o + s • y i) = TrueCompact V.pupil.last (V.Post Z) phase s o y v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ (phase : Option (T₀).Character) (v : (i : Fin n) → (B₀).sector (d i)) (o : E4) (x : Points n), x ∈ K →
      let a := publicLetters d v
      YangMills.Matching.shapeJetEstimateAt j
        (fun y => (T₀).correlation phase (Hₘ.inputs s a) (WithLp.toLp 2 fun i => o + s • y i))
        (fun y => ∑ k : Fin (p+1), (Hₘ.clock s : ℂ)^k.val * (Cvt).correlation M k.val a y) x
        (A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)) * |Hₘ.clock s|^(p+1)) := by
  obtain ⟨A,hA,hp⟩ := WilsonGraphAppointedPhysicalShapePrice.uniform (R := R)
    Z V Q paid trail id tendsto_id d K hK separated p j
  refine ⟨A,hA,?_⟩
  filter_upwards [hp,field,clock] with s hs genuine hc
  intro phase v o x hx
  dsimp only
  rw [hc]
  have sf := (show ∀ᶠ y in 𝓝 x, y ∈ conf n from (conf_open n).mem_nhds (separated hx)).mono
    fun y hy => (genuine phase v o y hy).symm
  exact jetTransport sf (Filter.Eventually.of_forall fun y => sum Cvt M read (publicLetters d v) y p (t s))
    (hs phase o x hx v)


theorem shapeFromField (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    (Hₘ : YangMills.Matching.CorrelationOnly.Measurement B₀ T₀)
    (clock : Hₘ.clock =ᶠ[trail] t)
    (M : YangMills.MSbar.Coefficients B₀) (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g)
    (field : ∀ (n : ℕ) (d : Caps n), ∀ᶠ s : ℝ in trail,
      ∀ (phase : Option (T₀).Character) (v : FVA2.GradedFar.Inputs g.core d) (o : E4) (y : Points n),
        y ∈ conf n → (T₀).correlation phase (Hₘ.inputs s (publicLetters d v))
          (WithLp.toLp 2 fun i => o + s • y i) = TrueCompact V.pupil.last (V.Post Z) phase s o y v) :
    YangMills.Matching.CorrelationOnly.ShapeIncome M Cvt Hₘ := by
  intro n p j d K hK clear
  exact onField (R := R) Z V Q paid Hₘ clock M read n p j d K hK clear (field n d)


theorem published (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    (M : YangMills.MSbar.Coefficients B₀) (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g)
    (n p j : ℕ) (d : Caps n) (K : Set (Points n)) (hK : IsCompact K)
    (separated : K ⊆ YangMills.WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (phase : Option (T₀).Character)
      (v : FVA2.GradedFar.Inputs g.core d) (o : E4) (x : Points n), x ∈ K →
        YangMills.Matching.shapeJetEstimateAt j
          (fun y => (T₀).correlation phase (ElectedMeasurement.inputs V Z s d v)
            (WithLp.toLp 2 fun i => o + s • y i))
          (fun y => ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z s : ℂ)^k.val *
            (Cvt).correlation M k.val (publicLetters d v) y) x
          (A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)) *
            |ElectedMeasurement.clock V Z s|^(p+1)) := by
  obtain ⟨A,hA,hp⟩ := WilsonGraphAppointedPhysicalShapePrice.uniform (R := R)
    Z V Q paid trail id tendsto_id d K hK separated p j
  refine ⟨A,hA,?_⟩
  filter_upwards [hp, (show ∀ᶠ s : ℝ in trail, 0 < s from self_mem_nhdsWithin)] with s hs positive
  intro phase v o x hx
  have field := (show ∀ᶠ y in 𝓝 x, y ∈ conf n from (conf_open n).mem_nhds (separated hx)).mono
    fun y hy => (ElectedMeasurement.scalar V Z phase d v positive o y hy).symm
  exact jetTransport field (Filter.Eventually.of_forall fun y => sum Cvt M read (publicLetters d v) y p (t s))
    (hs phase o x hx v)

theorem onClockFrame (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1))
    (Hₘ : YangMills.Matching.CorrelationOnly.Measurement B₀ T₀)
    (clock : Hₘ.clock =ᶠ[trail] ElectedMeasurement.clock V Z)
    (frames : ∀ d, ∀ᶠ s : ℝ in trail, ∀ v : (B₀).sector d,
      Hₘ.frame s d v = ElectedMeasurement.frame V Z s d v)
    (M : YangMills.MSbar.Coefficients B₀) (read : M.correlation = WilsonGraphStandaloneCorrelation.bare g) :
    YangMills.Matching.CorrelationOnly.ShapeIncome M Cvt Hₘ := by
  apply shapeFromField (R := R) Z V Q paid Hₘ clock M read
  intro n d
  have each : ∀ᶠ s : ℝ in trail, ∀ i : Fin n, ∀ v : (B₀).sector (d i),
      Hₘ.frame s (d i) v = ElectedMeasurement.frame V Z s (d i) v :=
    Filter.eventually_all.mpr fun i => frames (d i)
  filter_upwards [each, (show ∀ᶠ s : ℝ in trail, 0 < s from self_mem_nhdsWithin)] with s sr positive
  intro phase v o y hy
  have hinputs : Hₘ.inputs s (publicLetters d v) = ElectedMeasurement.inputs V Z s d v := by
    funext i
    exact congrArg (fun w : (T₀).Field (d i) => (⟨d i,w⟩ : (T₀).Tag)) (sr i (v i))
  rw [hinputs]
  exact ElectedMeasurement.scalar V Z phase d v positive o y hy

theorem group (R : PhysicalNext.Repeat.Legato.Run g.core) (hg : g.IsSimple) (V : Vision E ξ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let D := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = D ∧ Vision.StandaloneCorrelation V Z D ∧
      ∀ M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g),
      M.correlation = WilsonGraphStandaloneCorrelation.bare g →
      ∀ (n p j : ℕ) (d : Caps n) (K : Set (Points n)), IsCompact K → K ⊆ conf n →
        ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
        ∀ (phase : Option (YangMills.hierarchy (g := g) V.pupil.last V.pupil.P).Character) (v : FVA2.GradedFar.Inputs g.core d) (o : E4) (x : Points n), x ∈ K →
          YangMills.Matching.shapeJetEstimateAt j
            (fun y => (YangMills.hierarchy (g := g) V.pupil.last V.pupil.P).correlation phase (ElectedMeasurement.inputs V Z s d v)
              (WithLp.toLp 2 fun i => o + s • y i))
            (fun y => ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z s : ℂ)^k.val *
              (PostedAppointedConversion.filed Z Q.MS Q.matching (FVA2.Teller.logNu 1)).correlation
                M k.val (publicLetters d v) y) x
            (A * (∏ i, YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) (v i)) *
              |ElectedMeasurement.clock V Z s|^(p+1)) := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨Q,hQ,approved,price⟩ := separatedGraphSumOnGroupFiledDatum (R := R) hg V true
  refine ⟨Q,hQ,approved,?_⟩
  intro M read n p j d K hK separated
  have paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1) := by
    rw [hQ]
    exact price
  exact published (R := R) Z V Q paid M read n p j d K hK separated


theorem referenceSum (S : YangMills.Matching.Conversion B₀) {n : ℕ}
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) (x : Points n) (p : ℕ) (clock : ℝ) :
    publicTruncation S a x p clock = ∑ k : Fin (p+1), (clock : ℂ)^k.val *
      WilsonGraphStandaloneCorrelation.converted S k.val a x := by
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (clock : ℂ)^k * WilsonGraphStandaloneCorrelation.converted S k a x) (p+1)).symm

def ReferenceShape : Prop :=
  ∀ (n cap : ℕ) (K : Set (Points n)), IsCompact K → K ⊆ conf n → ∀ p j : ℕ,
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ d : Caps n, (∀ i, d i ≤ cap) →
      ∀ (v : FVA2.GradedFar.Inputs g.core d) (phase : Option (T₀).Character) (o : E4)
        (x : Points n), x ∈ K →
          YangMills.Matching.shapeJetEstimateAt j
            (fun y => (T₀).correlation phase (ElectedMeasurement.inputs V Z s d v)
              (WithLp.toLp 2 fun i => o + s • y i))
            (fun y => ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z s : ℂ)^k.val *
              WilsonGraphStandaloneCorrelation.converted Cvt k.val (publicLetters d v) y) x
            (A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)) *
              |ElectedMeasurement.clock V Z s|^(p+1))

theorem referenceCapped (paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1)) :
    ReferenceShape Z V Q := by
  intro n cap K hK separated p j
  obtain ⟨A,hA,hp⟩ := WilsonGraphAppointedPhysicalShapePrice.capped (R := R) Z V Q paid
    trail id tendsto_id n cap K hK separated p j
  refine ⟨A,hA,?_⟩
  filter_upwards [hp, (show ∀ᶠ s : ℝ in trail, 0 < s from self_mem_nhdsWithin)] with s hs positive
  intro d within v phase o x hx
  have field := (show ∀ᶠ y in 𝓝 x, y ∈ conf n from (conf_open n).mem_nhds (separated hx)).mono
    fun y hy => (ElectedMeasurement.scalar V Z phase d v positive o y hy).symm
  exact jetTransport field (Filter.Eventually.of_forall fun y => referenceSum Cvt (publicLetters d v) y p (t s))
    (hs d within v phase o x hx)

theorem groupReference (R : PhysicalNext.Repeat.Legato.Run g.core) (hg : g.IsSimple) (V : Vision E ξ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let D := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = D ∧ Vision.StandaloneCorrelation V Z D ∧ ReferenceShape Z V Q := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨Q,hQ,approved,price⟩ := separatedGraphSumOnGroupFiledDatum (R := R) hg V true
  have paid : AllAppointedGraphSums R Z Q.MS (FVA2.Teller.logNu 1) := by
    rw [hQ]
    exact price
  exact ⟨Q,hQ,approved,referenceCapped (R := R) Z V Q paid⟩


def CompactReference : Prop :=
  ∀ (n cap p : ℕ) (K : Set (Points n)), IsCompact K → K ⊆ conf n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ d : Caps n, (∀ i, d i ≤ cap) →
      ∀ (v : FVA2.GradedFar.Inputs g.core d) (phase : Option (T₀).Character) (o : E4)
        (x : Points n), x ∈ K →
          ‖(T₀).correlation phase (ElectedMeasurement.inputs V Z s d v)
              (WithLp.toLp 2 fun i => o + s • x i) -
            ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z s : ℂ)^k.val *
              WilsonGraphStandaloneCorrelation.converted Cvt k.val (publicLetters d v) x‖ ≤
          A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)) *
            |ElectedMeasurement.clock V Z s|^(p+1)

def TestedReference : Prop :=
  ∀ (n : ℕ) (d : Caps n) (phase : Option (T₀).Character) (v : FVA2.GradedFar.Inputs g.core d) (o : E4),
    YangMills.Matching.HasExpansion 0 (ElectedMeasurement.clock V Z)
      (fun s x => (T₀).correlation phase (ElectedMeasurement.inputs V Z s d v)
        (WithLp.toLp 2 fun i => o + s • x i))
      (fun k x => WilsonGraphStandaloneCorrelation.converted Cvt k (publicLetters d v) x)

theorem referenceCompact (shapes : ReferenceShape Z V Q) : CompactReference Z V Q := by
  intro n cap p K hK separated
  obtain ⟨A,hA,late⟩ := shapes n cap K hK separated p 0
  exact ⟨A,hA,late.mono fun s hs d within v phase o x hx =>
    YangMills.Matching.CorrelationOnly.shapeValue (hs d within v phase o x hx)⟩

theorem referenceTested (shapes : ReferenceShape Z V Q) : TestedReference Z V Q := by
  intro n d phase v o
  apply YangMills.Matching.CorrelationOnly.testedOfShapeJets (ElectedMeasurement.positive V Z Q)
    (YM.Trace.Pilot.Coupling.conforms H (V.certificate Q).calendar.clock)
  intro p K hK separated
  obtain ⟨A,hA,late⟩ := shapes n (publicDegree d) K hK separated p 0
  refine ⟨A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)),
    mul_nonneg hA (Finset.prod_nonneg fun i _ => YangMills.Matching.sectorMass_nonneg (B := B₀) (v i)), ?_⟩
  exact late.mono fun s hs x hx => hs d (publicWithin d) v phase o x hx

theorem groupComplete (R : PhysicalNext.Repeat.Legato.Run g.core) (hg : g.IsSimple) (V : Vision E ξ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let D := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = D ∧ Vision.StandaloneCorrelation V Z D ∧
      ReferenceShape Z V Q ∧ CompactReference Z V Q ∧ TestedReference Z V Q := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  obtain ⟨Q,identified,approved,shapes⟩ := groupReference R hg V
  exact ⟨Q,identified,approved,shapes,referenceCompact Z V Q shapes,referenceTested Z V Q shapes⟩


theorem atOneMatch (R : PhysicalNext.Repeat.Legato.Run g.core) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (μ : ℝ) : AllAppointedGraphSums R Z Q.MS μ := by
  intro n h d v within x k
  have physical := PostedAppointedFieldCorrelation.original (R := R) Z Q.MS Q.matching μ d v within x k
  have bare (j : ℕ) : YM.MS.Graphical.separatedGraphSum μ g.core h x.val j = Equator.wave μ Q.MS h n x j :=
    YM.MS.Graphical.identification_screen μ Q.MS x.property
  simpa only [AppointedGraphSum, bare] using physical

theorem beforeConstruction (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let D := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = D ∧
      ∀ (_R : PhysicalNext.Repeat.Legato.Run g.core) {ε : ℝ} {e : Axis} {O : OrderS g.core}
        (E : Construction.{u} H ε e O) {ξ : Extraction.Order} (V : Vision E ξ),
        Vision.StandaloneCorrelation V Z D ∧ ReferenceShape Z V Q ∧
          CompactReference Z V Q ∧ TestedReference Z V Q := by
  dsimp only
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let D := WilsonCapturedPhysicalMSDatum.original g.core
  obtain ⟨Q,hQ⟩ := compared H Z true D
  refine ⟨Q,hQ,?_⟩
  intro R ε e O E ξ V
  have shapes := referenceCapped (R := R) Z V Q (atOneMatch R Z Q (FVA2.Teller.logNu 1))
  have physical : Vision.StandaloneCorrelation V Z D := by
    rw [← hQ]
    exact Vision.standaloneFromActualField V Q
  exact ⟨physical,shapes,referenceCompact Z V Q shapes,
    referenceTested Z V Q shapes⟩

theorem beforeVolumeChoice (hg : g.IsSimple) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let D := WilsonCapturedPhysicalMSDatum.original g.core
    ∃ Q : Perspective H Z true, Q.MS = D ∧
      ∀ (_R : PhysicalNext.Repeat.Legato.Run g.core) {ε : ℝ} {e : Axis} {O : OrderS g.core}
        (E : Construction.{u} H ε e O) (pick : (ξ : Extraction.Order) → Vision E ξ)
        (ξ : Extraction.Order), Vision.StandaloneCorrelation (pick ξ) Z D ∧
          ReferenceShape Z (pick ξ) Q ∧ CompactReference Z (pick ξ) Q ∧ TestedReference Z (pick ξ) Q := by
  dsimp only
  obtain ⟨Q,hQ,all⟩ := beforeConstruction (H := H) hg
  exact ⟨Q,hQ,fun R _ _ _ E pick ξ => all R E (pick ξ)⟩

section Public
open YangMills YangMills.Matching YangMills.Matching.CorrelationOnly
variable {g' : YangMills.GaugeGroup} {B : YangMills.Maxwell.Reference g'}
variable {C : YangMills.WilsonFamily g'} {T : YangMills.Hierarchy C}
variable (M : YangMills.MSbar.Coefficients B) (S : YangMills.Matching.Conversion B)
variable (Hₘ : YangMills.Matching.CorrelationOnly.Measurement B T)

theorem tested (shapes : ShapeIncome M S Hₘ) (n : ℕ) (d : Fin n → ℕ) :
    ∃ m : ℕ, ∀ (phase : Option T.Character) (v : (i : Fin n) → B.sector (d i)) (o : E4),
      let a : Fin n → YangMills.Matching.Label B := fun i => ⟨d i, v i⟩
      YangMills.Matching.HasExpansion m Hₘ.clock (fun s x => T.correlation phase (Hₘ.inputs s a)
        (WithLp.toLp 2 fun i => o + s • x i)) (fun k x => S.correlation M k a x) := by
  refine ⟨0, ?_⟩
  intro phase v o
  apply testedOfShapeJets Hₘ.positive (clockAtZero Hₘ)
  intro p K hK clear
  obtain ⟨A,hA,late⟩ := shapes n p 0 d K hK clear
  refine ⟨A * (∏ i, sectorMass (v i)), mul_nonneg hA (Finset.prod_nonneg fun i _ => sectorMass_nonneg (v i)), ?_⟩
  exact late.mono fun s hs x hx => hs phase v o x hx

theorem compact (shapes : ShapeIncome M S Hₘ) (n p : ℕ) (d : Fin n → ℕ) (o : E4)
    (K : Set (YM.Points n)) (hK : IsCompact K) (clear : K ⊆ YangMills.WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : YM.Points n), x ∈ K →
        ‖correlationError M S Hₘ p (fun i => ⟨d i,v i⟩) phase o s x‖ ≤
          A * (∏ i, sectorMass (v i)) * |Hₘ.clock s|^(p+1) := by
  obtain ⟨A,hA,late⟩ := shapes n p 0 d K hK clear
  exact ⟨A,hA,late.mono fun s hs phase v x hx => shapeValue (hs phase v o x hx)⟩

end Public

end YM.Integration.WilsonGraphPublishedShapeEstimate





