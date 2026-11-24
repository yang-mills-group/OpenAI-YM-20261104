import YM.Integration.FVA1Physical.Wilson.CommonChart
import YM.RGComparison.Core16.HistoryIntegral

/-! Exact full-period conditional readout after the coarse-replica change on
the newly exposed links. All previous history variables and all tag likelihoods
remain inside the same Haar integral. -/

noncomputable section

namespace YM.Integration.FVA1Physical.Wilson

open MeasureTheory
open YM.Lattice YM.RG YM.Tree YM.Wilson YM.Precision YM.RGComparison.Core16
open scoped BigOperators Classical

variable {G : Gauge} {n c f : Side} {S : StepData c f}
    (F : Forest S.ratio) (d : Descent n f)

local notation "D" => Descent.push S F d

def replicaHistory (V : Config G c) : Descent.Fields G D :=
  Sum.elim (fun i : F.Free => replica S.ratio V i) (fun _ => 1)

def relativeTotal (β : ℕ → ℝ) (O : Config G n → ℝ) (V : Config G c) : ℝ :=
  ∑ t : (D).Tags, ∫ z, (D).integrand β t O V (z * replicaHistory F d V) ∂(D).measure G

theorem weighted_relativeTotal (β : ℕ → ℝ) (h : (D).OK G)
    {O : Config G n → ℝ} (hc : Continuous O) (hi : GaugeInvariant O) (V : Config G c) :
    (D).weighted β O V = (D).scalar G β * relativeTotal F d β O V := by
  rw [Descent.path_formula h β hc hi V]
  unfold relativeTotal
  apply congrArg ((D).scalar G β * ·)
  refine Finset.sum_congr rfl fun t _ => ?_
  have mp : MeasurePreserving (fun z : Descent.Fields G D => z * replicaHistory F d V)
      ((D).measure G) ((D).measure G) :=
    measurePreserving_pi _ _ fun i => measurePreserving_mul_right G.probHaar (replicaHistory F d V i)
  exact (mp.integral_comp (Homeomorph.mulRight (replicaHistory F d V)).measurableEmbedding
    ((D).integrand β t O V)).symm

/-- The complete vacuum, proved positive in the translated chart, divides all
insertions with the identical history, coupling, field and normalization. -/
theorem conditioned_relativeTotal (β : ℕ → ℝ) (h : (D).OK G)
    {O : Config G n → ℝ} (hc : Continuous O) (hi : GaugeInvariant O) (V : Config G c) :
    0 < relativeTotal F d β 1 V ∧
      (D).conditioned β O V = relativeTotal F d β O V / relativeTotal F d β 1 V := by
  have vac := weighted_relativeTotal F d β h (O := 1) continuous_const (fun _ _ => rfl) V
  rw [Descent.weighted_unit] at vac
  have hs := Descent.scalar_pos G D β
  have hv := Descent.positive β h V
  rw [vac] at hv
  refine ⟨(mul_pos_iff_of_pos_left hs).mp hv, ?_⟩
  change ((D).vacuum β V)⁻¹ * (D).weighted β O V = _
  rw [vac, weighted_relativeTotal F d β h hc hi V, mul_comm, ← div_eq_mul_inv,
    mul_div_mul_left _ _ hs.ne']

end YM.Integration.FVA1Physical.Wilson

