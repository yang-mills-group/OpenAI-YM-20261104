import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Toward.Contract
import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedNullaryRefund
import YM.Integration.WilsonGraphPaperCorrelations

noncomputable section
namespace YM.FVA2.GradedFar.AppointedNullaryTariff
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
open Function Set Filter PowerSeries
open XSpace XSpace.Normalize FVA2.Register FVA2.Scale FVA2.Dframe
open O O.Score O.Project Integration
open YM.MS.Land YM.FVA2.O.Canon YangMills YangMills.MSbar
open YM.Answer.ContinuumLimit YangMills.Matching IssuedMaxwell IssuedMaxwell.Reports
open scoped BigOperators Classical

universe u
variable {G : Gauge}

theorem emptyCredit (T : Cast G) (c : PowerSeries ℂ) (L : Draft G 0)
    (s : Scan G 0) (q : Q G) : credit T c L s q = (L s q).subst c := by
  let v : LivesP s := fun i => Fin.elim0 i
  change (∑ i : LivesP s, play T s (decode s i) * (L (decode s i) q).subst c) = _
  rw [Finset.sum_eq_single v]
  · have same : decode s v = s := Subsingleton.elim _ _
    rw [same]
    simp only [play,Finset.univ_eq_empty,Finset.prod_empty,one_mul]
  · intro i _ different
    exact False.elim (different (Subsingleton.elim i v))
  · intro hn
    exact False.elim (hn (Finset.mem_univ v))

variable (N : _root_.YM.FVA2.Register.WilsonPrescription G) (ν : ℝ) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {d : Fin 0 → ℕ}

theorem tariff (x : Points 0) (v : Appointed122Fields G d) (s : Scan G 0) (q : Q G) :
    MStariff N ν M x v q = receipt (seats (replay (Measure.Z N.scheme N.criterion ν M)))
      (fun t => (OPECoefficients (Equator.wave ν M) s 0 x t).subst (Measure.f N.criterion ν M)) q := by
  let i : Words G d := fun j => Fin.elim0 j
  rw [MStariff,Finset.sum_eq_single i]
  · have same : labeling i = s := Subsingleton.elim _ _
    rw [same]
    simp only [filedMultipliers122,Finset.univ_eq_empty,Finset.prod_empty,map_one,one_mul]
    change receipt (seats (replay (Measure.Z N.scheme N.criterion ν M)))
      (credit (seats (Measure.Z N.scheme N.criterion ν M)) (Measure.f N.criterion ν M)
        (fun t : Scan G 0 => OPECoefficients (Equator.wave ν M) t 0 x) s) q = _
    apply congrArg (fun u : Bill G => receipt (seats (replay (Measure.Z N.scheme N.criterion ν M))) u q)
    funext t
    exact emptyCredit _ _ _ _ _
  · intro j _ different
    exact False.elim (different (Subsingleton.elim j i))
  · intro hn
    exact False.elim (hn (Finset.mem_univ i))

variable (g : YangMills.GaugeGroup) (hg : g.IsSimple)
private abbrev issuedN := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev noLabels : Scan g.core 0 := fun i => Fin.elim0 i
private abbrev filedConversion := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion

theorem filed (d : Fin 0 → ℕ) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (h k : ℕ) (x : Points 0) :
    AppointedNullaryRefund.assemble g.core h (fun t => coeff k
      (MStariff (issuedN g hg) (Teller.logNu 1) ((_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).MS x v (Dframe.flash t))) =
      (filedConversion g hg).ope (GraphCoefficients.issued g) h k a x := by
  let N := issuedN g hg
  let Q := (_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)
  let ν := Teller.logNu 1
  let Z := Measure.Z N.scheme N.criterion ν Q.MS
  let c := Measure.f N.criterion ν Q.MS
  let f := _root_.IssuedBridge.PostedRealFiledCoupling.coefficient N Q.MS ν
  let L : Bill g.core := OPECoefficients (Equator.wave ν Q.MS) (noLabels g) 0 x
  have hz : Civil Z := ⟨fun h => (Q.matching.frame ν h).1,fun h => (Q.matching.frame ν h).2,
    fun hs => Q.matching.frameCompat ν _ _ hs⟩
  have real := _root_.IssuedBridge.PostedRealFiledCoupling.original N Q.MS Q.matching ν
  have incoming : (fun t : Toon g.core h => coeff k (MStariff N ν Q.MS x v (Dframe.flash t))) =
      (fun t => coeff k (receipt (seats (replay Z)) (fun i => (L i).subst c) (Dframe.flash t))) := by
    funext t
    exact congrArg (coeff k) (tariff N ν Q.MS x v (noLabels g) (Dframe.flash t))
  change AppointedNullaryRefund.assemble g.core h _ = _
  rw [incoming,AppointedNullaryGraph.filed.{u}]
  have actual := AppointedNullaryRefund.refund (replay Z) hz.turn c f real.1 real.2.1 L h k
  have nominate : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core :=
    WilsonGraphPaperPublication.nominated.{u} g hg
  let C := _root_.IssuedBridge.PostedAppointedConversion.filed N Q.MS Q.matching ν
  have coupling : C.f = f := rfl
  have inverse (b : ℕ) : C.Zinv h b = coeff b (replay Z h) := rfl
  have fields (j : ℕ) :
      AppointedNullaryRefund.assemble g.core h (fun t => coeff j (L (Dframe.flash t))) =
        ∑ t : Toon g.core h, coeff j (OPECoefficients
          (Equator.wave ν (WilsonCapturedPhysicalMSDatum.original g.core))
          (noLabels g) 0 x (Dframe.flash t)) • theory t := by
    change (∑ t : Toon g.core h, coeff j (OPECoefficients (Equator.wave ν Q.MS)
      (noLabels g) 0 x (Dframe.flash t)) • theory t) = _
    rw [nominate]
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  change (couplingPower f j.val (k-b.val) : ℂ) • (coeff b.val (replay Z h))
      (AppointedNullaryRefund.assemble g.core h (fun t => coeff j.val (L (Dframe.flash t)))) =
    (couplingPower C.f j.val (k-b.val) : ℂ) • C.Zinv h b.val
      (∑ t : Toon g.core h, coeff j.val (OPECoefficients
        (Equator.wave ν (WilsonCapturedPhysicalMSDatum.original g.core))
        (noLabels g) 0 x (Dframe.flash t)) • theory t)
  rw [coupling,inverse]
  exact congrArg (fun s : Sec g.core h =>
    (couplingPower f j.val (k-b.val) : ℂ) • (coeff b.val (replay Z h)) s) (fields j.val)

theorem wholeCrop (d : Fin 0 → ℕ) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
    (h p : ℕ) (x : Points 0) (z : ℂ) :
    MScoefficient (issuedN g hg) (Teller.logNu 1) ((_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).MS x h p z v =
      ∑ k ∈ Finset.range (p+1), z^k • (filedConversion g hg).ope (GraphCoefficients.issued g) h k a x := by
  let M := ((_root_.YM.Integration.WilsonGraphPaperPublication.perspective.{u} g hg)).MS
  let row := fun t : Toon g.core h => MStariff (issuedN g hg) (Teller.logNu 1) M x v (Dframe.flash t)
  have each (t : Toon g.core h) : filedCrop122 p z (row t) • theory t =
      ∑ k ∈ Finset.range (p+1), z^k • (coeff k (row t) • theory t) := by
    rw [filedCropEq122,Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul,mul_comm]
  change (∑ t : Toon g.core h, filedCrop122 p z (row t) • theory t) = _
  simp_rw [each]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.smul_sum]
  exact congrArg (fun v : Sec g.core h => z^k • v) (filed.{u} g hg d v a h k x)

end YM.FVA2.GradedFar.AppointedNullaryTariff

