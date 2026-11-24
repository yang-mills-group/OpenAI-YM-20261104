import YM.XSpace.Transfers
/-! # Read the subtractions into a symmetric (auxiliary) frame -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Structure1
open Filter Set Function Lattice Chart2 Mu Furlough Normalize Foundation JetGauge Outline Shade Future Hoops Maxwell Maxwell.Free Stall
open scoped Topology BigOperators Classical
variable {G:Gauge} {d:ℕ} (s:Signed)
abbrev τ (s:Signed)(d:ℕ) := ori (G:=G) s.ortho d
@[simp] lemma τm (t:Signed)(p:Sec G d): τ s d (τ t d p)=τ (s*t) d p:=Subtype.ext (by simp only [τ,val_ori,← pol_mul,show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..])
@[simp] lemma τone (p:Sec G d): τ 1 d p=p:= by unfold τ; rw [show (1:Signed).ortho=1 from map_one Signed.inclusionO]; exact Subtype.ext (pol_one p.val)
lemma τu : τ (G:=G) s d (leaf G d)=leaf G d:=Subtype.ext (show reflectPol s.ortho 1= (1:WickPol G) from map_one _)
lemma tasa (p:Sec G d):reel d (τ s d p)=τ s d (reel d p):=Subtype.ext (real_orient ..)
variable (T: FieldEnd G d)
def spiral (d:ℕ): Module.End ℂ (FieldEnd G d) where
  toFun T:= τ s⁻¹ d ∘ₗ T ∘ₗ τ s d
  map_add' T U:=by ext1 p; simp only [LinearMap.comp_apply,LinearMap.add_apply,map_add]
  map_smul' a T:= by ext1 p; simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_smul,RingHom.id_apply]
lemma spirals (p:Sec G d): spiral s d T p=τ s⁻¹ d (T (τ s d p)):=rfl
lemma spiral_keeps (h:T∈ Tri G d): spiral s d T∈ Tri G d:= by
  rw [tri_may] at *; simp only [spirals]; exact ⟨by rw [τu, h.1,map_zero],fun l hl p hp=> (closed_sector (h.2 l hl _ (closed_sector hp s.ortho).1) s⁻¹.ortho).1⟩

def matR (d:ℕ): (FieldEnd G d) →ₛₗ[starRingEnd ℂ] (FieldEnd G d) where
  toFun T:= reel d ∘ₛₗ T ∘ₛₗ reel d -- notation?
  map_add' T U:= by ext1 p; change reel d (T _+U _)=_+_; rw [map_add]; rfl
  map_smul' c T:= by ext1 p; change reel d (c • T _) = star c • _; rw [(reel d).map_smulₛₗ]; rfl
lemma rsa (p:Sec G d): matR d T p=reel d (T (reel d p)):=rfl
lemma rs_keeps (h:T∈ Tri G d): matR d T∈ Tri G d:= by
  rw [tri_may] at *; simp only [rsa]; exact ⟨by rw [show reel d (leaf G d)=leaf G d from Subtype.ext (map_one (realForm (G:=G))),h.1,map_zero],fun l hl p hp=> (closed_sector (h.2 l hl _ (closed_sector hp 1).2) 1).2⟩
def mid (A:FieldEnd G d): FieldEnd G d:= (2:ℂ)⁻¹ • (A+matR d A)
def R (K:Type)[Fintype K]:ℂ := Fintype.card K
omit s T in
lemma denom_card {K:Type}[Fintype K][Nonempty K]: R K≠0:=by unfold R; exact_mod_cast Fintype.card_ne_zero
private def swivels (A:FieldEnd G d):= ∑ s:Signed, spiral s d A
def forge (A:FieldEnd G d): FieldEnd G d:= (R Signed)⁻¹ • swivels (mid A)
set_option pp.universes false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4600 in
lemma axes (A:FieldEnd G d): forge A=(R Signed)⁻¹ • ∑ s:Signed, spiral s d (mid A):=by unfold forge swivels; exact Eq.refl _
lemma mid_anchor (p:Sec G d): reel d (mid T p)=mid T (reel d p):=by unfold mid; simp only [LinearMap.add_apply,LinearMap.smul_apply,rsa,(reel d).map_smulₛₗ,map_inv₀,map_ofNat,map_add,reel_back, add_comm (reel d _)]
lemma compass (h:T∈ Tri G d): forge T∈ Change G d:=by
  have H (K) (hw:K∈ Tri G d): mid K∈ Tri G d:=Submodule.smul_mem _ _ (Submodule.add_mem _ hw (rs_keeps K hw)); have ht: forge T∈ Tri G d:= Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=> spiral_keeps _ _ (H T h)); rw [tri_may] at ht; rw [may_change]; refine ⟨ht.1,ht.2,fun p=>?_, fun s p=>?_⟩
  · rw [axes T]; simp only [(reel d).map_smulₛₗ,map_inv₀,R,map_natCast,map_sum, LinearMap.smul_apply,LinearMap.sum_apply, spirals, ← tasa, ← mid_anchor] -- simp maybe loop
  rw [axes]; simp only [LinearMap.smul_apply,LinearMap.sum_apply,spirals,map_smul,map_sum]; apply congr_arg; rw [← Equiv.sum_comp (Equiv.mulRight s) (fun i=> ori s.ortho d (τ i⁻¹ d (mid T (τ i d p))))]; refine Finset.sum_congr rfl fun i _=>?_ ; change τ i⁻¹ d (mid T (τ i d (τ s d p)))=τ s d (τ (i*s)⁻¹ d (mid T (τ (i*s) d p))); simp

variable (W:Initialize G){P:FieldEnd G d}{n:ℕ}(a:ℝ)(x:Fin n→Cover)(p:Tags G d n)
lemma spun : adequate W (spiral s d T) a x p= adequate W T a (fun i=>s.act (x i)) (τ s d ∘ p):=by
  rw [adequate,adequate,sub_apply,sub_apply,show τ s d (G:=G)= ori s.ortho d from rfl,oriented_first]; apply congr_arg; simp_rw [lots]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← oriented_blossom W d a x s]; apply congr_arg; funext j; by_cases h:j=i; subst j; change τ s d _ = _; simp [spirals]; simp only [Function.comp_apply,update_of_ne h]
lemma sun : adequate W (matR d T) a x p=star (adequate W T a x (reel d ∘ p)):=by
  rw [adequate,adequate,sub_apply,sub_apply,star_sub,winter1,star_star, lots,lots,star_sum]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ; symm; rw [← winter0]; apply congr_arg; funext j; by_cases h:j=i; subst j; simp [rsa]; simp [h,reel_back]
-- dependence on origins, affine not linear map
lemma forges : adequate W (forge T) a x p=(R Signed)⁻¹ * ∑ s:Signed,(2:ℂ)⁻¹ * (adequate W (spiral s d T) a x p+adequate W (spiral s d (matR d T)) a x p):=by
  let r:=replied W a x d p; let L(F):=lot (blossom0 W d a x) F p; let f (s:Signed):= L (spiral s d T); let g s:= L (spiral s d (matR d T)); have hr: (R Signed)⁻¹ * ∑ _s:Signed,r=r:=by rw [Finset.sum_const,nsmul_eq_mul, Finset.card_univ,← mul_assoc,show (Fintype.card Signed:ℂ)=R Signed from rfl,inv_mul_cancel₀ denom_card,one_mul]
  rw [axes]; simp only [adequate,mid,map_smul,map_sum,map_add,sub_apply,add_apply,smul_apply, sum_apply,smul_eq_mul]; change r-(R Signed)⁻¹ * (∑ x:Signed,(2:ℂ)⁻¹*(f x+g x))=_ * ∑ x:Signed,(2:ℂ)⁻¹*(r-f x+(r-g x))
  nth_rw 1 [← hr]; rw [← mul_sub, ← Finset.sum_sub_distrib]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; ring
end YM.XSpace.Structure1
