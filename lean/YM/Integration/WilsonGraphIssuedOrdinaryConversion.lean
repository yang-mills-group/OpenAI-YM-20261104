import YM.Integration.WilsonGraphOrdinaryFiledRefund

noncomputable section
namespace YM.Integration.AppointedGraphOrdinaryConversion
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open YangMills YangMills.Matching YangMills.MSbar
open YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Dframe
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.FVA2.Register YM.Answer.ContinuumLimit PowerSeries
open YM.FVA2.O.Project
open YM.MS.Land YM.Integration _root_.IssuedMaxwell _root_.IssuedMaxwell.Reports
open scoped BigOperators Classical

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) {n : ℕ}
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Qstar := _root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg
abbrev filedConversion := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion

/-- The signed MS refund on the original heterogeneous basis, at the independently nominated datum. -/
def row (d : Fin n → ℕ) (v : (i : Fin n) → Sec g.core (d i)) (x : YM.Points n) (q : Q g.core) :
    PowerSeries ℂ :=
  let Z := N g hg
  let Q := Qstar.{u} g hg
  let ν := Teller.logNu 1
  let F := Measure.Z Z.scheme Z.criterion ν Q.MS
  ∑ s : (i : Fin n) → Toon g.core (d i), PowerSeries.C (∏ i, coord (s i) (v i)) *
    O.Project.refund (seats F) (seats (replay F)) (Measure.f Z.criterion ν Q.MS)
      (fun w => OPECoefficients (Equator.wave ν Q.MS) w 0 x) (fun i => Dframe.flash (s i)) q

/-- The prescribed MS refund is exactly the public issued graph OPE after the filed field and clock conversions. -/
theorem coefficient (d : Fin n → ℕ) (v : (i : Fin n) → Sec g.core (d i)) (h k : ℕ) (x : YM.Points n) :
    AppointedNullaryRefund.assemble g.core h (fun t => coeff k
      (row.{u} g hg d v x (Dframe.flash t))) =
      (filedConversion g hg).ope (GraphCoefficients.issued g) h k (fun i => ⟨d i,v i⟩) x := by
  let Z := N g hg
  let Q := Qstar.{u} g hg
  let ν := Teller.logNu 1
  let F := Measure.Z Z.scheme Z.criterion ν Q.MS
  let U := replay F
  let c := Measure.f Z.criterion ν Q.MS
  let f := _root_.IssuedBridge.PostedRealFiledCoupling.coefficient Z Q.MS ν
  let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching ν
  let L : Draft g.core n := fun s => OPECoefficients (Equator.wave ν Q.MS) s 0 x
  let A := AppointedNullaryRefund.assemble g.core h
  have HF : Civil F := ⟨fun h => (Q.matching.frame ν h).1, fun h => (Q.matching.frame ν h).2,
    fun hs => Q.matching.frameCompat ν _ _ hs⟩
  have real := _root_.IssuedBridge.PostedRealFiledCoupling.original Z Q.MS Q.matching ν
  have nominate : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core :=
    WilsonGraphPaperPublication.nominated.{u} g hg
  have issuedWord (s : Scan g.core n) (j : ℕ) :
      A (fun t => coeff j (L s (Dframe.flash t))) = GraphReader.earned g s h j x := by
    change AppointedNullaryRefund.assemble g.core h (fun t =>
      coeff j (OPECoefficients (Equator.wave ν Q.MS) s 0 x (Dframe.flash t))) = _
    rw [nominate]
    exact (AppointedOrdinaryGraphBasis.earned g s h j x).symm
  let labels (s : (i : Fin n) → Toon g.core (d i)) : Scan g.core n := fun i => Dframe.flash (s i)
  have spent := AppointedOrdinaryRefund.roster (fun s : (i : Fin n) → Toon g.core (d i) => ∏ i, coord (s i) (v i)) labels
    F U HF.turn c f real.1 real.2.1 L h k
  have same : filedConversion g hg = S :=
    congrArg (fun pos => pos.conversion) (WilsonGraphGroupPositionReference.atPerspective hg Q nominate)
  have onGraph := congrArg (fun D : Conversion (maxwellReference g) =>
    D.ope (GraphCoefficients.issued g) h k (fun i => ⟨d i,v i⟩) x) same.symm
  refine spent.trans (Eq.trans ?_ onGraph)
  unfold YangMills.Matching.Conversion.ope
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun b _ => ?_
  by_cases fits : b.val + (∑ i, (e i).val) ≤ k
  · simp only [fits, if_true]
    apply congrArg (fun y : Sec g.core h =>
      (couplingPower f j.val (k-(b.val+∑ i, (e i).val)) : ℂ) • coeff b.val (U h) y)
    change (∑ s : (i : Fin n) → Toon g.core (d i), (∏ i, coord (s i) (v i)) •
      ∑ w : LivesP (labels s), AppointedOrdinaryRefund.inputWeight F (labels s) w (fun i => (e i).val) •
        A (fun t => coeff j.val (L (decode (labels s) w) (Dframe.flash t)))) =
      GraphReader.form g d h j.val x (fun i => coeff (e i).val (F (d i)) (v i))
    simp_rw [issuedWord]
    exact (AppointedOrdinaryFiledInputs.inputColumns g F HF d v (fun i => (e i).val) h j.val x).symm
  · simp [fits]
    rfl

/-- The numerical comparison on every occupied word keeps its entire output at cap h. -/
theorem crop (d : Fin n → ℕ) (v : (i : Fin n) → Sec g.core (d i)) (h p : ℕ) (x : YM.Points n) (z : ℂ) :
    (∑ t : Toon g.core h, (∑ k ∈ Finset.range (p+1), z^k * coeff k
      (row.{u} g hg d v x (Dframe.flash t))) • theory t) =
      ∑ k ∈ Finset.range (p+1), z^k • (filedConversion g hg).ope
        (GraphCoefficients.issued g) h k (fun i => ⟨d i,v i⟩) x := by
  let R := fun t : Toon g.core h => row.{u} g hg d v x (Dframe.flash t)
  have each (t : Toon g.core h) : (∑ k ∈ Finset.range (p+1), z^k * coeff k (R t)) • theory t =
      ∑ k ∈ Finset.range (p+1), z^k • (coeff k (R t) • theory t) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
  change (∑ t : Toon g.core h, (∑ k ∈ Finset.range (p+1), z^k * coeff k (R t)) • theory t) = _
  simp_rw [each]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.smul_sum]
  exact congrArg (fun a : Sec g.core h => z^k • a) (coefficient.{u} g hg d v h k x)

end YM.Integration.AppointedGraphOrdinaryConversion

