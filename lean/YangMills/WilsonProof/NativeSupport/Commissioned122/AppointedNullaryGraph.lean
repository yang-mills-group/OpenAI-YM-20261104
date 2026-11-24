import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCoefficients
import YM.FVA2.O.Project.Track
import YM.Integration.WilsonGraphGroupPositionReference
import YM.Integration.WilsonGraphPaperCorrelations

noncomputable section
namespace YM.Integration.AppointedNullaryGraph
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
open YangMills YangMills.Matching YangMills.MSbar
open YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Dframe
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.Answer.ContinuumLimit PowerSeries
open _root_.IssuedMaxwell _root_.IssuedMaxwell.Reports
open scoped BigOperators Classical

universe u
variable (g : YangMills.GaugeGroup)
private abbrev emptyScan : Scan g.core 0 := fun i => Fin.elim0 i
private abbrev wave := Equator.wave (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)

theorem rawGrade (s : Scan g.core 0) (w k : ℕ) (x : YM.Points 0) :
    GraphBasisExterior.price g s w k 0 x =
      ∑ b : Grade g.core w, coeff k (OPECoefficients (wave g) s 0 x (own b)) • vertex b := by
  have same : OPECoefficients (wave g) s 0 = LogPricing (wave g) s 0 :=
    zero_t (LogPricing (wave g) s) s
  rw [same]
  rfl

theorem emptyForm (d : Fin 0 → ℕ) (v : (i : Fin 0) → Sec g.core (d i)) (h k : ℕ) (x : YM.Points 0) :
    GraphReader.form g d h k x v = GraphReader.earned g (emptyScan g) h k x := by
  let s : (i : Fin 0) → Toon g.core (d i) := fun i => Fin.elim0 i
  have h₁ : v = (fun i => theory (s i)) := Subsingleton.elim _ _
  have h₂ : (fun i => Dframe.flash (s i)) = emptyScan g := Subsingleton.elim _ _
  rw [h₁,GraphReader.marked,h₂]

theorem issuedEmpty (a : Fin 0 → Ordinary.Label (B g)) (h k : ℕ) (x : YM.Points 0) :
    (GraphCoefficients.issued g).ope 0 h k a x = GraphReader.earned g (emptyScan g) h k x :=
  emptyForm g (fun i => (a i).1) (fun i => (a i).2) h k x

theorem fullBasis (a : Fin 0 → Ordinary.Label (B g)) (h k : ℕ) (x : YM.Points 0) :
    (GraphCoefficients.issued g).ope 0 h k a x =
      ∑ c : Toon g.core h, coeff k (OPECoefficients (wave g) (emptyScan g) 0 x (Dframe.flash c)) • theory c := by
  rw [issuedEmpty]
  change (∑ w : Fin (h+1), up (Nat.le_of_lt_succ w.isLt)
      (GraphBasisExterior.price g (emptyScan g) w.val k 0 x)) =
      ∑ c : (w : Fin (h+1)) × Grade g.core w.val,
        coeff k (OPECoefficients (wave g) (emptyScan g) 0 x (Dframe.flash c)) • theory c
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [rawGrade,map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  rfl

theorem afterInverse (S : YangMills.Matching.Conversion (B g))
    (a : Fin 0 → Ordinary.Label (B g)) (h k : ℕ) (x : YM.Points 0) :
    S.ope (GraphCoefficients.issued g) h k a x =
      ∑ j : Fin (k+1), ∑ b : Fin (k+1), (couplingPower S.f j.val (k-b.val) : ℂ) •
        S.Zinv h b.val (∑ c : Toon g.core h,
          coeff j.val (OPECoefficients (wave g) (emptyScan g) 0 x (Dframe.flash c)) • theory c) := by
  let ν : Fin 0 → Fin (k+1) := fun i => Fin.elim0 i
  unfold YangMills.Matching.Conversion.ope
  rw [Finset.sum_eq_single ν]
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Nat.add_zero,if_pos (Nat.le_of_lt_succ b.isLt)]
    rw [fullBasis]
    rfl
  · intro v _ different
    exact False.elim (different (Subsingleton.elim v ν))
  · intro hn
    exact False.elim (hn (Finset.mem_univ ν))

variable (hg : g.IsSimple)
private abbrev issuedN := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev prospect := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev chart := _root_.IssuedBridge.PostedAppointedConversion.filed (issuedN g hg)
  (prospect.{u} g hg).MS (prospect.{u} g hg).matching (Teller.logNu 1)

theorem filed (a : Fin 0 → Ordinary.Label (B g)) (h k : ℕ) (x : YM.Points 0) :
    (WilsonGraphGroupPositionReference.external g hg).conversion.conversion.ope (GraphCoefficients.issued g) h k a x =
      ∑ j : Fin (k+1), ∑ b : Fin (k+1), (couplingPower (chart.{u} g hg).f j.val (k-b.val) : ℂ) •
        (chart.{u} g hg).Zinv h b.val (∑ c : Toon g.core h,
          coeff j.val (OPECoefficients (wave g) (emptyScan g) 0 x (Dframe.flash c)) • theory c) := by
  rw [WilsonGraphGroupPositionReference.atPerspective hg (prospect.{u} g hg)
    (WilsonGraphPaperPublication.nominated.{u} g hg)]
  exact afterInverse g (chart.{u} g hg) a h k x

theorem cropped (dates : ℕ → ℕ) (strictDates : StrictMono dates) (a : Fin 0 → Ordinary.Label (B g))
    (h p : ℕ) (x : YM.Points 0) (r : ℝ) :
    let V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order dates strictDates)
    (∑ k ∈ Finset.range (p+1), ((V.T (issuedN g hg) r : ℂ)^k) •
      (WilsonGraphGroupPositionReference.external g hg).conversion.conversion.ope (GraphCoefficients.issued g) h k a x) =
    ∑ k ∈ Finset.range (p+1), ((V.T (issuedN g hg) r : ℂ)^k) •
      ∑ j : Fin (k+1), ∑ b : Fin (k+1), (couplingPower (chart.{u} g hg).f j.val (k-b.val) : ℂ) •
        (chart.{u} g hg).Zinv h b.val (∑ c : Toon g.core h,
          coeff j.val (OPECoefficients (wave g) (emptyScan g) 0 x (Dframe.flash c)) • theory c) := by
  exact Finset.sum_congr rfl fun k _ => congrArg _ (filed.{u} g hg a h k x)

end YM.Integration.AppointedNullaryGraph

