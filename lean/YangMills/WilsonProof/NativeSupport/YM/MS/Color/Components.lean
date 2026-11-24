import YM.MS.Color.Components
import YM.MS.Properties
import YM.MS.Color.Triple
/-!
# Component tests on invariant tensors in symmetry conditions

One-frame $̅MS and Wilson use same group. Coefficients given on `eb`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau
open Function Filter Set Finset Only Extra.WeakScaling.Color Koszul Plane Wire Gauge
open scoped Topology InnerProductSpace ContDiff
variable {A P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {G : Gauge}

variable (G)
section
variable {V : Type} [AddCommGroup V] [Module ℝ V]
def cbasis (p : G.ColorIndex → V) : G.Color →ₗ[ℝ] V:= {
   toFun x:= ∑ i, x i • p i
   map_add' x y := by simp only [PiLp.add_apply, add_smul, sum_add_distrib]
   map_smul' c x := by simp only [PiLp.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply] }
lemma at_cbasis (p : G.ColorIndex → V) (x : G.Color): cbasis G p x=∑ i, x i • p i:=rfl
@[simp] lemma index_c (p : CI G→ V) (i : CI G): cbasis G p (eb G i)=p i:= by simp [at_cbasis, eb, EuclideanSpace.basisFun_apply,PiLp.single_apply]
lemma c_ext {f g : G.Color→ₗ[ℝ] V} (h : ∀ i:G.ColorIndex, f (eb G i)=g (eb G i)): f=g:= (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis.ext h
lemma c_ext' {f g : G.Color→ₗ[ℝ] V} (h : ∀ i:G.ColorIndex, f (eb G i)=g (eb G i)) (i:G.Color): f i=g i:= LinearMap.congr_fun (c_ext G h) _
end
variable {F: Score G A P} {d:ℤ} {b:Bool}
variable {G} (H: G.Simple)
include H
lemma single (p : G.ColorIndex→ℂ) (h : ∀ g k, (∑ i, (weight g k i:ℂ)*p i)=p k) (i) : p i=0:= by
   let f:=cbasis G p
   have hv (g:G.El) : f.comp (G.adjoint g)=f:= c_ext G (fun i=>?_)
   · rw [← index_c G p]; exact Extra.WeakScaling.Color.linear_invariant H f (fun g v=> LinearMap.congr_fun (hv g) v) _
   unfold f; rw [LinearMap.comp_apply,index_c,at_cbasis]; simpa [weight] using h g i
lemma pair_value (p : G.ColorIndex → G.ColorIndex → ℂ) (h : ∀ g i j, (∑ k, (weight g i k:ℂ)* ∑ l, (weight g j l:ℂ)*p k l)=p i j) : ∃ c:ℂ, ∀ i j, p i j= if i=j then c else 0:= by
   let q:= cbasis G fun i=> cbasis G (p i)
   have hp i j:q (eb G i) (eb G j)=p i j:=by unfold q; rw [index_c G,index_c G]
   have hb g i j: q (G.adjoint g (eb G i)) (G.adjoint g (eb G j))=p i j:= by
      simp_rw [q,at_cbasis,LinearMap.sum_apply,LinearMap.smul_apply,at_cbasis]; simpa [weight] using h g i j
   have hI (g:G.El) : ∀ i j, q (G.adjoint g i) (G.adjoint g j)= q i j:= by
      let Q : Bi G ℂ:= LinearMap.mk₂ ℝ (fun x y=> q (G.adjoint g x) (G.adjoint g y)) (fun _ _ _=>by simp) (fun _ _ _=>by simp) (fun _ _ _=>by simp) (fun _ _ _=>by simp)
      have he : Q=q:= c_ext G fun i=> c_ext G fun j=> (hb g i j).trans (hp i j).symm
      exact fun i j=> congr_arg (fun u:Bi G ℂ=> u i j) he
   obtain ⟨c,hc⟩:= Extra.WeakScaling.Color.bilinear_invariant H q hI; refine ⟨c,fun i j=>?_⟩
   rw [←hp, hc]; by_cases h0:i=j
   · rw [if_pos h0,h0, OrthonormalBasis.inner_eq_one,one_smul]
   rw [if_neg h0, OrthonormalBasis.inner_eq_zero ..,zero_smul]; exact h0
lemma triple_value (p : CI G→CI G→CI G→ℂ) (h : ∀ g i j k, (∑ u:CI G, (weight g i u:ℂ)*(∑ v:CI G, (weight g j v:ℂ)*∑ w:CI G, (weight g k w:ℂ)*p u v w)) = p i j k)
   (he : ∀ i j k, p i j k = - p j i k) (hs : ∀ i j k,p i j k=p j k i) : ∃ c:ℂ, ∀ i j k:CI G, p i j k = ⟪G.ad (eb G i) (eb G j), eb G k⟫_ℝ • c:= by
   let q:= cbasis G fun i=> cbasis G fun j=>cbasis G (p i j)
   have hp i j k : q (eb G i) (eb G j) (eb G k)=p i j k:=by unfold q; rw [index_c G,index_c G,index_c G]
   have hq (i j k:G.Color) : q i j k = ∑ u:CI G, (i u:ℂ)*(∑ v:CI G, (j v:ℂ)*∑ w:CI G, (k w:ℂ)*p u v w):=by
      simp only [q,at_cbasis, LinearMap.sum_apply,LinearMap.smul_apply,Complex.real_smul]
   have ha : ∀ i j k,q i j k = - q j i k := by
      have ha : q = -q.flip := c_ext G (fun i=> c_ext G (fun j=> c_ext G (fun k=> (hp i j k).trans ((he i j k).trans (congr_arg _ (hp j i k).symm)))))
      exact fun i j k=> congr_arg (fun q : Tri G ℂ=> q i j k) ha
   -- define rotate flip flip
   let q' : Tri G ℂ:= LinearMap.mk₂ ℝ (fun i j=> (q j).flip i) (fun x y z=> by rw [map_add]) (fun _ _ _=> by rw [map_smul]) (fun i x y=> by ext1; simp) (fun _ _ _=>by ext1; simp)
   have hh : ∀ i j k,q i j k=q j k i:= by
      have heq : q=q':= c_ext G fun i=> c_ext G fun j=> c_ext G fun k=> (hp i j k).trans ((hs ..).trans (hp j k i).symm)
      exact fun i j k=> congr_arg (fun q : Tri G ℂ=> q i j k) heq
   have hg : ∀ g x y z,q (G.adjoint g x) (G.adjoint g y) (G.adjoint g z) = q x y z:= by
      intro g
      let L:=G.adjoint g
      let Q : Tri G ℂ:= LinearMap.mk₂ ℝ (fun i j=> (q (L i) (L j)).comp L) (fun x y z=>by ext1; simp) (fun _ _ _=>by ext1; simp) (fun i x y=>by ext1; simp) (fun _ _ _=>by ext1; simp)
      have hv i j k : Q (eb G i) (eb G j) (eb G k)=p i j k:= by
         change q (G.adjoint g (eb G i)) (G.adjoint g (eb G j)) (G.adjoint g (eb G k))=_; rw [hq]; exact h g i j k
      have heq : Q=q:= c_ext G fun i=> c_ext G fun j=> c_ext G fun k=> (hv i j k).trans (hp i j k).symm
      exact fun x y z=> congr_arg (fun q : Tri G ℂ=> q x y z) heq
   obtain ⟨c,hc⟩:= Triple.complex q H ha hh hg; exact ⟨c,fun i j k=> (hp i j k).symm.trans (hc ..)⟩
end YM.MS.Landau
