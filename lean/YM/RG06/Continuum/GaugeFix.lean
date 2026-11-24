import YM.RG06.Continuum.GaugeOrbit
 import YM.Pert.First.Completion

/-!
# Finite radial gauge fixing on the jet sector

Eliminate radial obstructions exactly degree by degree with genuine smooth gauge phases
(exp of physical Lie elements, no formal divisor). Telescoping along each ray avoids postulating
an inverse for a continuum gauge operator. At λ=0 `abelian` instead uses ordinary gradient; no
action of a local nonabelian gauge on the g=0 connection is stipulated. We work only with
finite demands on a point jet, never imposing a gauge on the actual density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Function Analysis Labels Maxwell Tensor
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace Classical
variable {G:Gauge}

def radTest (A:Connection G)(z:E4)(t:ℝ):= ∑ i:Axis,z i • A i (t • z)
/-- Through orders < k of the CONNECTION (degree 0 included). -/
def killed (k:ℕ)(A:Connection G):=∀ i<k,∀ z:E4, iteratedDeriv i (radTest A z) 0=0

def obstacle (k:ℕ)(A:Connection G)(z:E4):G.Color:=
  (↑((k+1)*k.factorial:ℕ):ℝ)⁻¹ • ∑ i:Axis, z i • diagonal (iteratedFDeriv ℝ k (A i) 0) z
lemma obstacle_smooth (k:ℕ)(A:Connection G): Good (obstacle k A):=by
 unfold obstacle; apply ContDiff.const_smul; apply ContDiff.sum
 intro i hi; exact ((EuclideanSpace.proj i:E4→L[ℝ]ℝ)).contDiff.smul (diag_smooth _ _)
lemma obstacle_power (k:ℕ)(A:Connection G)(z:E4)(t:ℝ):obstacle k A (t • z)= t^(k+1) • obstacle k A z:=by
  unfold obstacle; simp only [PiLp.smul_apply, Tensor.homogeneous,smul_eq_mul,Finset.smul_sum,smul_smul,pow_succ]
  refine Finset.sum_congr rfl fun i _=> ?_; congr 1; ring
@[simp] lemma obstacle_flat (k:ℕ)(A:Connection G):obstacle k A 0=0:=by simp [obstacle]
lemma charge (k:ℕ)(A:Connection G)(h:Smooth A)(z:E4):
    (((k+1)*k.factorial:ℕ):ℝ) • obstacle k A z = iteratedDeriv k (radTest A z) 0:=by
  unfold obstacle radTest; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul, iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl; intro i _; rw [iteratedDeriv_fun_const_smul_field,YM.Next.Foundations.iteratedDeriv_on_line]; exact
     (ContDiff.contDiffAt (h i)).of_le (WithTop.coe_le_coe.mpr le_top)
  intro i hi; exact ContDiffAt.const_smul (f:=fun t:ℝ=>A i (t • z)) (z i) (((ContDiff.contDiffAt (h i)).of_le (show ((k:ℕ):WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp (f:=fun t:ℝ=>t • z) 0 (contDiffAt_id.smul contDiffAt_const))

variable (g:ℝ)
def dye (A:Connection G)(k:ℕ) : Phase G:=fun z=>G.lieExp (g • obstacle k A z)
lemma dye_ok (A:Connection G)(k:ℕ):Ready (dye g A k):=by
  let t:E4→G.Color:=fun z=>g • obstacle k A z
  exact (show ContDiff ℝ ∞ (fun y:G.Color=>G.mat (G.lieExp y)) from G.exp_jet.of_le le_top).comp (f:=t) (ContDiff.const_smul g (obstacle_smooth k A)) -- exp_jet in Work??
@[simp] lemma dye_flat (A:Connection G)(k:ℕ): dye g A k 0=1:=by simp [dye]

lemma obstacle_path (A:Connection G)(k:ℕ)(x:E4)(t:ℝ):
    ∑ i:Axis, x i • suffix (dye g A k) i (t • x)=g • (((k+1:ℕ):ℝ)*t^k) • obstacle k A x:=by
  -- test colors back through mat and chain
  let P:= G.colorMat (g • obstacle k A x)
  let y:= t • x
  let s:= dye g A k
  have hΦ:= dye_ok g A k
  have he: (fun z:ℝ=> face s (z • x))=fun z:ℝ=>NormedSpace.exp (z^(k+1) • P):=by
    funext z; change G.mat (G.lieExp _) = _; simp only [G.mat_lieExp,obstacle_power,smul_comm g,P,map_smul]
  let a:ℝ:= ((k+1:ℕ):ℝ)*t^k
  have hz : HasDerivAt (fun z:ℝ=>NormedSpace.exp (z^(k+1) • P)) (a • (P * NormedSpace.exp (t^(k+1) • P))) t :=by
    have hD:HasDerivAt (fun u:ℝ=>u^(k+1)) a t:=by simpa [a] using! (hasDerivAt_id' t).pow (k+1)
    exact (hasDerivAt_exp_smul_const' P _).scomp t hD
  have ht:= ((show Good (face s) from hΦ).germ y).hasFDerivAt
  have hp : HasDerivAt (fun u:ℝ=>u • x) x t:=by simpa using! (hasDerivAt_id' t).smul_const x
  have Ht:=ht.comp_hasDerivAt t hp
  change HasDerivAt (fun u:ℝ=> face s (u • x)) ((fderiv ℝ (face s) y) x) _ at Ht; rw [he] at Ht
  have hv : ∑ i:Axis,x i • basis i=x := by ext i; simp [WithLp.ofLp_sum,Finset.sum_apply,basis,Pi.single_apply, mul_ite]
  apply G.colorMat_injective
  simp only [map_sum,map_smul,suffix_color _ hΦ,suffixM]
  change _= g • a • G.colorMat (obstacle k A x)
  simp_rw [← smul_mul_assoc]
  rw [← Finset.sum_mul];
  let F:= fderiv ℝ (face s) y
  have hx : ∑ i:Axis,x i • F (basis i)= F x:= by conv_rhs=>rw [← hv,map_sum]; simp only [map_smul]
  change (∑ i:Axis,x i • F (basis i))*bar s y=_
  rw [hx, show F x=_ from Ht.unique hz, ← congr_fun he t,smul_mul_assoc, Matrix.mul_assoc, pair_right,mul_one,show P=g • G.colorMat (obstacle k A x) from map_smul ..,smul_comm] -- `P` local unfold
lemma rad_shift (k:ℕ)(hg:g≠0)(A:Connection G)(x:E4):
    radTest (dressed g A (dye g A k)) x =fun t=> G.adjoint (dye g A k (t • x)) (radTest A x t) - (((k+1:ℕ):ℝ)*t^k) • obstacle k A x := by
  funext t
  unfold radTest dressed shade; simp only [Pi.sub_apply, smul_sub,Pi.smul_apply, map_sum,map_smul,Finset.sum_sub_distrib,smul_comm _ (g⁻¹),← Finset.smul_sum]
  rw [obstacle_path g A k x t, inv_smul_smul₀ hg] -- actually g^-1 • g • rest

-- matrix product lemma with order mask. test on any real curve into the Lie group.
lemma keep {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] (k:ℕ)(X Y:ℝ→E)(h:ContDiffAt ℝ k X 0)(hY:ContDiffAt ℝ k Y 0)(H : ∀ n<k,iteratedDeriv n Y 0=0):
    iteratedDeriv k (fun t=> X t * Y t) 0=X 0 * iteratedDeriv k Y 0:=by
  rw [iteratedDeriv_fun_mul h hY, Finset.sum_eq_single 0]
  · simp
  · intro b hb he; rw [H _ (show k-b<k by have ht:=Finset.mem_range.mp hb; omega),mul_zero]
  simp
lemma keepR {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] (k:ℕ)(X Y:ℝ→E)(h:ContDiffAt ℝ k X 0)(hY:ContDiffAt ℝ k Y 0)(H : ∀ n<k,iteratedDeriv n Y 0=0):
    iteratedDeriv k (fun t=> Y t * X t) 0= iteratedDeriv k Y 0 * X 0:=by
  rw [iteratedDeriv_fun_mul hY h, Finset.sum_eq_single k]
  · simp
  · intro b hb he; rw [H _ (by have ht:=Finset.mem_range.mp hb; omega),mul_zero,zero_mul]
  simp
private lemma passes (Y : ℝ→G.Color)(h:ContDiff ℝ ∞ Y)(k:ℕ) :
    G.colorMat (iteratedDeriv k Y 0)= iteratedDeriv k (fun t=>G.colorMat (Y t)) 0:= (YM.Pert.First.iterated_clm G.colorMat.toContinuousLinearMap _ h).symm -- need h
lemma rotated_rad (A:Connection G)(h:Smooth A)(k:ℕ)(hp:killed k A)(s:Phase G)(hs:Ready s)(h0:s 0=1)(z:E4)(n:ℕ)(hn:n≤k):
    iteratedDeriv n (fun t:ℝ=> G.adjoint (s (t • z)) (radTest A z t)) 0=iteratedDeriv n (radTest A z) 0:=by
  let W(t:ℝ):=s (t • z)
  let L:ℝ→L[ℝ]E4:=(ContinuousLinearMap.id ℝ ℝ).smulRight z
  let F:= fun t:ℝ=>G.mat (W t)
  let U:= fun t:ℝ=>bar s (L t)
  let Y:=radTest A z
  let Z:=fun t=> G.colorMat (Y t)
  have he : ContDiff ℝ ∞ (radTest A z):= ContDiff.sum (fun i _=>ContDiff.const_smul (z i) (ContDiff.comp (h i) L.contDiff))
  have hF:ContDiff ℝ ∞ F:=ContDiff.comp (g:=face s) hs L.contDiff
  have hU:ContDiff ℝ ∞ U:=ContDiff.comp (g:=bar s) (Good.faces s hs) L.contDiff
  have hZ:ContDiff ℝ ∞ Z:=G.colorMat.toContinuousLinearMap.contDiff.comp he
  have hz: F 0=1:=by simp [F,W,h0]
  have hx: U 0=1:=by simp only [U,L,map_zero,bar,face,Function.comp_apply,h0,G.mat_one,star_one]
  have hpast (i:ℕ)(hm:i<n):iteratedDeriv i Z 0=0:=by unfold Z Y; rw [← passes (radTest A z) he i,hp i (hm.trans_le hn),map_zero]
  have hnW : ContDiff ℝ ∞ (fun t=> G.adjoint (W t) (Y t)):=by
    exact G.projectColor.toContinuousLinearMap.contDiff.comp ((hF.mul hZ).mul hU)
  apply G.colorMat_injective; rw [passes _ hnW, passes _ he]
  simp_rw [G.mat_adjoint] -- Gauge prefix
  change iteratedDeriv n (fun t:ℝ=>F t * Z t * U t) 0=iteratedDeriv n Z 0
  have hK(i:ℕ): (i:WithTop ℕ∞) ≤ ∞:= WithTop.coe_le_coe.mpr le_top
  have hh (i:ℕ)(hi:i≤n):iteratedDeriv i (fun t:ℝ=>F t*Z t) 0=iteratedDeriv i Z 0:= by rw [keep i F Z (hF.contDiffAt.of_le (hK i)) (hZ.contDiffAt.of_le (hK _)) (fun j hj=>hpast j (hj.trans_le hi)),hz,one_mul]
  rw [keepR n U (fun t=>F t*Z t) (hU.contDiffAt.of_le (hK _)) ((hF.mul hZ).contDiffAt.of_le (hK _)) (fun i hi=>by rw [hh i hi.le,hpast i hi]),hx,mul_one,hh n le_rfl]

lemma stage (hg:g≠0)(k:ℕ)(A:Connection G)(h:Smooth A)(hA:killed k A): killed (k+1) (dressed g A (dye g A k)) := by
  intro i hi z
  let B:= fun t:ℝ=> G.adjoint (dye g A k (t • z)) (radTest A z t)
  have hf : ContDiff ℝ ∞ B:=by
    let L:ℝ→L[ℝ] E4:= (ContinuousLinearMap.id ℝ ℝ).smulRight z
    let F:E4→G.Color:=fun x=>∑ i:Axis,z i • A i x
    have hh:Good F:=ContDiff.sum (fun i _=>ContDiff.const_smul (z i) (h i))
    change ContDiff ℝ ∞ (shade (dye g A k) F ∘ L); exact ContDiff.comp (Good.shade _ (dye_ok g A k) _ hh) L.contDiff
  let V:= ((k+1:ℕ):ℝ) • obstacle k A z
  let auxC(t:ℝ):G.Color:= t^k • V
  have hc:ContDiffAt ℝ i auxC 0:= (contDiffAt_id.pow k).smul contDiffAt_const
  rw [rad_shift g k hg, show (fun t:ℝ=> G.adjoint (dye g A k (t • z)) (radTest A z t) - _)= B-auxC by
    funext t; simp only [Pi.sub_apply,B,auxC,V,smul_smul,mul_comm]]
  rw [iteratedDeriv_sub (hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hc]
  rw [show iteratedDeriv i B 0= _ from rotated_rad A h k hA (dye g A k) (dye_ok g A k) (dye_flat g A k) z i (by omega)]
  unfold auxC V; rw [iteratedDeriv_smul_const,iteratedDeriv_fun_pow_zero]; split
  next he=> subst i; rw [smul_smul,mul_comm, ← charge _ _ h z]; push_cast; abel
  next he=> rw [Nat.cast_zero,zero_smul,hA i (by omega),sub_zero]
  exact contDiffAt_id.pow _

theorem orbit (k:ℕ)(hg:g≠0)(A:Connection G)(h:Smooth A):∃ B:Connection G, Smooth B ∧ killed k B ∧ Form.evaluate g B 0=Form.evaluate g A 0:=by
  induction k with
  | zero=> exact ⟨A,h,(fun _ hk=>False.elim (Nat.not_lt_zero _ hk)),rfl⟩
  | succ k H=> obtain ⟨B,hB,hV,hW⟩:=H; let s:=dye g B k;
               exact ⟨dressed g B s,sound _ _ hB _ (dye_ok g B k),stage g hg k B hB hV,(center_same g hg B hB s (dye_ok g B k) (dye_flat g B k)).trans hW⟩
end YM.RG06.Continuum
