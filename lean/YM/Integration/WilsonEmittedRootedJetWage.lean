import YM.Integration.WilsonOriginalLinkedAngularPage
import YM.Integration.WilsonEmittedWindingField
import YM.TraceExtension.Swift.Beak

/-! Reconstitute the low-jet operator in the original Wilson chart from the
absolute sums of the retained thermal and bond-coordinate components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedRootedJetWage
open Function Lattice RG Stationary Finset
open scoped BigOperators Classical ContDiff
variable {G:Gauge} {n:Side}

abbrev Slot (G:Gauge) (n:Side) := Option (Site n × Loc G 1)
abbrev Joint (G:Gauge) (n:Side) := ℝ × Directions G n

def peg (G:Gauge) (n:Side) : Slot G n → Joint G n
  | none => (1,0)
  | some q => (0,edgeColor (WilsonOriginalLinkedAngularPage.ray G q))

def weight (z:Joint G n) : Slot G n → ℝ
  | none => z.1
  | some q => (edgeColor.symm z.2) q

private theorem billed (z:Joint G n) (q:Slot G n) : ‖weight z q‖ ≤ ‖z‖ := by
  cases q with
  | none => exact norm_fst_le z
  | some u =>
    let L:Directions G n →L[ℝ] Link G n := edgeColor.symm.toContinuousLinearMap
    have cap:=Trace.Swift.shortE G n L rfl
    exact (norm_le_pi_norm (L z.2) u).trans ((L.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right cap (norm_nonneg _)).trans (by simpa using norm_snd_le z)))

private theorem links (x:Link G n) :
    ∑q:Site n × Loc G 1, x q • WilsonOriginalLinkedAngularPage.ray G q = x := by
  ext u
  simp [WilsonOriginalLinkedAngularPage.ray,Finset.sum_apply]

theorem rebuilt (z:Joint G n) : ∑q:Slot G n,weight z q • peg G n q=z := by
  rw [Fintype.sum_option]
  apply Prod.ext
  · simp [weight,peg,Prod.fst_sum]
  · simp only [weight,peg,Prod.smul_snd,smul_zero,zero_add,Prod.snd_add,Prod.snd_sum]
    let eC:Link G n ≃L[ℝ] Directions G n:=edgeColor
    let X:=eC.symm z.2
    change ∑ q,X q • eC (WilsonOriginalLinkedAngularPage.ray G q)=z.2
    calc
      _ = ∑ q,eC (X q • WilsonOriginalLinkedAngularPage.ray G q):=by simp only [map_smul]
      _ = eC (∑ q,X q • WilsonOriginalLinkedAngularPage.ray G q):=(map_sum eC _ _).symm
      _ = z.2:=by rw [links];exact eC.apply_symm_apply _

theorem original {i:ℕ} (T:Tensor.T (Joint G n) ℂ i) {δ:ℝ} (pay:
    ∑u:Fin i → Slot G n, ‖T (peg G n ∘ u)‖ ≤ δ) : ‖T‖ ≤ δ := by
  have pos:0 ≤ δ:=(sum_nonneg fun a _=>norm_nonneg _).trans pay
  apply T.opNorm_le_bound pos
  intro v
  let M:=T.toMultilinearMap
  have expand := M.map_sum (fun j q=>weight (v j) q • peg G n q)
  have full: T v = ∑u:Fin i→Slot G n,(∏j,weight (v j) (u j)) • T (peg G n ∘ u) := by
    simp_rw [rebuilt] at expand
    exact expand.trans (Finset.sum_congr rfl fun u _=>M.map_smul_univ _ _)
  rw [full]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑u:Fin i→Slot G n,(∏j,‖v j‖)*‖T (peg G n ∘ u)‖:=by
      apply sum_le_sum
      intro u _
      rw [norm_smul,norm_prod]
      exact mul_le_mul_of_nonneg_right (prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>billed (v j) (u j))) (norm_nonneg _)
    _ = (∏j,‖v j‖)*(∑u:Fin i→Slot G n,‖T (peg G n ∘ u)‖):=by rw [Finset.mul_sum]
    _ ≤ _:=by rw [mul_comm δ]; exact mul_le_mul_of_nonneg_left pay (prod_nonneg fun j _=>norm_nonneg _)

end YM.Integration.WilsonEmittedRootedJetWage
