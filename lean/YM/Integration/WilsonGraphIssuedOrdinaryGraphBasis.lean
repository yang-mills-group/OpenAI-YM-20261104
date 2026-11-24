import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedNullaryGraph
import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedNullaryRefund

noncomputable section
namespace YM.Integration.AppointedOrdinaryGraphBasis
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
open YangMills YangMills.Matching YangMills.MSbar
open YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.Dframe
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.Answer.ContinuumLimit PowerSeries
open _root_.IssuedMaxwell _root_.IssuedMaxwell.Reports
open scoped BigOperators Classical

variable (g : YangMills.GaugeGroup) {n : ℕ}
private abbrev wave := Equator.wave (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)

/-- The grade component of the issued exterior reader at the appointed mass. -/
theorem grade (s : Scan g.core n) (w k : ℕ) (x : YM.Points n) :
    GraphBasisExterior.price g s w k 0 x =
      ∑ b : Grade g.core w, coeff k (OPECoefficients (wave g) s 0 x (own b)) • vertex b := by
  have same : OPECoefficients (wave g) s 0 = LogPricing (wave g) s 0 :=
    zero_t (LogPricing (wave g) s) s
  rw [same]
  rfl

/-- Reassemble every grade through the outgoing cap in the issued basis. -/
theorem earned (s : Scan g.core n) (h k : ℕ) (x : YM.Points n) :
    GraphReader.earned g s h k x = AppointedNullaryRefund.assemble g.core h (fun t =>
      coeff k (OPECoefficients (wave g) s 0 x (Dframe.flash t))) := by
  change (∑ w : Fin (h+1), up (Nat.le_of_lt_succ w.isLt)
      (GraphBasisExterior.price g s w.val k 0 x)) =
      ∑ c : (w : Fin (h+1)) × Grade g.core w.val,
        coeff k (OPECoefficients (wave g) s 0 x (Dframe.flash c)) • theory c
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [grade, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  rfl

/-- The independent public reading on an arbitrary heterogeneous input word. -/
theorem issued (d : Fin n → ℕ) (v : (i : Fin n) → Sec g.core (d i))
    (h k : ℕ) (x : YM.Points n) :
    (GraphCoefficients.issued g).ope n h k (fun i => ⟨d i, v i⟩) x =
      ∑ s : (i : Fin n) → Toon g.core (d i), (∏ i, coord (s i) (v i)) •
        AppointedNullaryRefund.assemble g.core h (fun t =>
          coeff k (OPECoefficients (wave g) (fun i => Dframe.flash (s i)) 0 x (Dframe.flash t))) := by
  change GraphReader.form g d h k x v = _
  rw [GraphReader.recorded]
  exact Finset.sum_congr rfl fun s _ => congrArg _ (earned g (fun i => Dframe.flash (s i)) h k x)

/-- Apply the filed input maps, coupling substitution and full cap-h inverse to that reader. -/
theorem converted (S : YangMills.Matching.Conversion (B g))
    (d : Fin n → ℕ) (v : (i : Fin n) → Sec g.core (d i))
    (h k : ℕ) (x : YM.Points n) :
    S.ope (GraphCoefficients.issued g) h k (fun i => ⟨d i, v i⟩) x =
      ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1),
        let used := b.val + ∑ i, (ν i).val
        if used ≤ k then (couplingPower S.f j.val (k-used) : ℂ) • S.Zinv h b.val
          (∑ s : (i : Fin n) → Toon g.core (d i),
            (∏ i, coord (s i) (S.Z (d i) (ν i).val (v i))) •
              AppointedNullaryRefund.assemble g.core h (fun t =>
                coeff j.val (OPECoefficients (wave g) (fun i => Dframe.flash (s i)) 0 x (Dframe.flash t))))
        else 0 := by
  unfold YangMills.Matching.Conversion.ope
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun b _ => ?_
  exact congrArg (fun y =>
    if b.val + ∑ i, (ν i).val ≤ k then
      (couplingPower S.f j.val (k-(b.val + ∑ i, (ν i).val)) : ℂ) • S.Zinv h b.val y
    else 0) (issued g d (fun i => S.Z (d i) (ν i).val (v i)) h j.val x)

end YM.Integration.AppointedOrdinaryGraphBasis

