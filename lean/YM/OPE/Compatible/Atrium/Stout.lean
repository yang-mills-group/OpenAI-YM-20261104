import YM.OPE.Compatible.Basin.Ur
/-! # Finite sensor jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type*} {G:Gauge}{n m c f:Side}{r:ℕ}
namespace Script
open Page
section
variable (p: Finset (Cover×I)) -- without duplicates desired, use restricted Deck
abbrev shelf:= ↥p→ℝ
variable [Fintype I]
def lookS (j:Site n): deck I n→L[ℝ] shelf p:= ContinuousLinearMap.pi fun a:p=> ContinuousLinearMap.proj (j+wrap n a.val.1,a.val.2)
omit [Fintype I] in
-- shelf sensor e coords. finite
lemma drawer (x:shelf p): (∑ i:↥p,(x i) • (Pi.single i 1 : shelf p))= x:=by
   ext j; simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]; rw [Finset.sum_eq_single j]; split_ifs; ring; exact False.elim (by contradiction)
   · intro i _ hi; simp [Ne.symm hi]
   simp
private def codes (r:ℕ) (y:Fin r→ ↥p): Page I r:=fun i=> (y i).val
private def velo (F:shelf p→ℝ)(r:ℕ)(y: Fin r→ ↥p):= ((r.factorial:ℝ)⁻¹) * iteratedFDeriv ℝ r F 0 (fun j=>Pi.single (y j) 1)
def servo (F:shelf p→ℝ)(r:ℕ): Script I r:= ∑ i:Fin r→p, velo p F r i • Pi.single (codes p r i) 1
omit [Fintype I] in
lemma ser_s (F:shelf p→ℝ)(m r: ℕ):∃ c,soot m (servo p F r) c:=by
   let u(i:Fin r→p):= velo p F r i; let v i:Script I r:= u i • (Pi.single (codes p r i) 1 : Script I r); let Z(i: Fin r→p):= figure m (codes p r i)*|u i|
   refine ⟨_, Sack.finGather (B:=Z) _ v (fun i _=>?_) (fun i=> zero_le_one.trans (payer m _))⟩; let z:=codes p r i; have hk : (fun a=> figure m a*‖v i a‖)= Pi.single z (Z i):=by funext j; by_cases h:j=z<;>simp [v,z,Z,h]
   refine ⟨(fun j=>mul_nonneg (zero_le_one.trans (payer m j)) (norm_nonneg _)), ?_,?_⟩
   · rw [hk]; exact (hasSum_single z (fun i hi=>Pi.single_eq_of_ne hi _)).summable
   change (∑' a,figure m a*‖v i a‖) ≤ _; rw [hk]; simp
omit [Fintype I] in
lemma read_one {n:Side}(p:Page I r)(v:Fin r→deck I n)(z:Site n):scribe z (Pi.single p 1) v= render z p v:=by unfold scribe; rw [tsum_eq_single p]; simp; exact fun i hi=> by simp [hi]
set_option maxHeartbeats 200000 in
lemma ser_sense (F:shelf p→ℝ)(m:ℕ)(u:Fin m→deck I n)(z:Site n)(h:ContDiffAt ℝ m F 0): iteratedFDeriv ℝ m (F ∘ lookS p z) 0 u=(m.factorial:ℝ)*scribe z (servo p F m) u:=by
     let k i(j:p):= (lookS p z (u i)) j; let T(i:Fin m)(j:p): shelf p:= k i j • (Pi.single j 1 : shelf p); let Y:=iteratedFDeriv ℝ m F 0
     rw [jets_linear (lookS p z) h, ContinuousMultilinearMap.compContinuousLinearMap_apply]; rw [show (fun i:Fin m=> lookS p z (u i))= (fun i=> ∑ j,T i j) from funext fun i=> (drawer p _).symm]; rw [Y.map_sum T]; unfold servo; rw [reads_sum]; swap; · intro i _; let f:Script I m:= Pi.single (codes p m i) 1; have h:Summable f:=(hasSum_single (codes p m i) (fun j hj=>by simp [f,hj])).summable; exact h.const_smul (velo p F m i)
     rw [Finset.mul_sum]; refine sum_congr rfl fun i _=> ?_; rw [score_scaled,read_one]; unfold T; rw [Y.map_smul_univ]; change _*_= (m.factorial:ℝ)*( ((m.factorial:ℝ)⁻¹ * Y _)*_); have hp:(m.factorial:ℝ)≠0:= by positivity
     rw [mul_assoc ((m.factorial:ℝ)⁻¹),mul_inv_cancel_left₀ hp]; rw [mul_comm]; rfl
end
end Script
end YM.OPE.Flume
