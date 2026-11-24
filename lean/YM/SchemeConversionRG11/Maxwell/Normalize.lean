import YM.SchemeConversionRG11.Maxwell.Tribute
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Infinitesimal real normalizer of the color bracket

Not requiring G.El connected, chart on color inner automorphisms used instead.
Orthogonal on the physical inner product. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open scoped Topology BigOperators RealInnerProductSpace InnerProduct

variable {G : Gauge}

def adh (G : Gauge) : G.Color →ₗ[ℝ] Door G := LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad
abbrev Store (G : Gauge) := LinearMap.range (adh G)

def TracesAd (G : Gauge) (B D : Door G) := LinearMap.trace ℝ G.Color (B.toLinearMap * D.toLinearMap)
lemma traced (h : G.Simple) (x y : G.Color) : -TracesAd G (adh G x) (adh G y)= G.casimir * ⟪x,y⟫ := Gauge.trace_adjoint h ..
lemma faithAd (h : G.Simple) : Injective (adh G) := by
  intro i j he
  have hp : TracesAd G (adh G (i-j)) (adh G (i-j))=0 := by rw [map_sub,he, sub_self]; simp [TracesAd]
  have hg := traced h (i-j) (i-j); rw [hp,neg_zero] at hg
  rw [← sub_eq_zero]; exact inner_self_eq_zero.mp ((mul_eq_zero.mp hg.symm).resolve_left (Gauge.casimir_pos h).ne')
lemma adh_bracket (i j : G.Color) : adh G (G.ad i j)=adh G i*adh G j-adh G j*adh G i := ContinuousLinearMap.ext fun k ↦ LinearMap.congr_fun (Gauge.ad_jacobi ..) k
lemma adh_skew (x : G.Color) : (adh G x)† = -(adh G x) := by
  ext1 v; apply ext_inner_right ℝ; intro u
  rw [ContinuousLinearMap.adjoint_inner_left]; change _ = ⟪-G.ad x v,u⟫; rw [inner_neg_left,Gauge.ad_skew,neg_neg]; rfl

def derivingD (G : Gauge) (D : Door G) := ∀ x y : G.Color,D (G.ad x y)=G.ad (D x) y + G.ad x (D y)
lemma bracketed {D : Door G} (h : derivingD G D) (x : G.Color) : D*adh G x-adh G x*D=adh G (D x) := by
  ext1 y; change D (G.ad x y)-G.ad x (D y)=_; rw [h x y,add_sub_cancel_right]; rfl
lemma innerD (h : G.Simple) {D : Door G} (hd : derivingD G D) : D ∈ Store G := by
  classical
  let p : G.Color →ₗ[ℝ] ℝ := (LinearMap.trace ℝ G.Color).comp ((LinearMap.mulLeft ℝ (D:Module.End ℝ G.Color)).comp G.ad)
  have hc := (Gauge.casimir_pos h).ne'
  let P := (-G.casimir⁻¹) • p.toContinuousLinearMap
  let v := (InnerProductSpace.toDual ℝ G.Color).symm P
  let L := D-adh G v
  have hf (x : G.Color) : TracesAd G (adh G v) (adh G x)=p x := by
    have ht := traced h v x
    rw [show ⟪v,x⟫ = -G.casimir⁻¹ * p x from InnerProductSpace.toDual_symm_apply] at ht
    rw [← mul_assoc,mul_neg,mul_inv_cancel₀ hc,neg_mul,one_mul, neg_inj] at ht; exact ht
  have he (x : G.Color) : LinearMap.trace ℝ G.Color (L.toLinearMap*G.ad x)=0 := by
    change LinearMap.trace ℝ G.Color ((D.toLinearMap-G.ad v)*G.ad x)=0
    rw [sub_mul,map_sub]; exact sub_eq_zero.mpr (hf x).symm
  have hu (x) : L*adh G x-adh G x*L=adh G (L x) := by
    change _=adh G (D x-G.ad v x)
    unfold L; rw [map_sub,adh_bracket v x, ← bracketed hd]; simp only [mul_sub,sub_mul]; abel
  refine ⟨v,?_⟩; symm
  apply sub_eq_zero.mp
  ext1 x
  change L x=0
  let O := L x
  have hh : L.toLinearMap*G.ad x-G.ad x*L.toLinearMap=G.ad O := LinearMap.ext fun y ↦ DFunLike.congr_fun (hu x) y
  have hp : LinearMap.trace ℝ G.Color (G.ad O*G.ad O)=LinearMap.trace ℝ G.Color (L.toLinearMap* G.ad (G.ad x O)) := by
    nth_rw 1 [← hh]
    rw [Gauge.ad_jacobi, sub_mul,mul_sub,map_sub,map_sub]
    rw [mul_assoc,mul_assoc,LinearMap.trace_mul_comm ℝ (G.ad x),mul_assoc]
  have hx := Gauge.trace_adjoint h O O; rw [hp,he,neg_zero] at hx
  exact inner_self_eq_zero.mp ((mul_eq_zero.mp hx.symm).resolve_left hc)

lemma centralizer_zero (h : G.Simple) {D : Door G} (hw : D†= -D) (hc : ∀ x, adh G x*D=D*adh G x) : D=0 := by
  have he (x y : G.Color) : G.ad x (D y)= D (G.ad x y) := DFunLike.congr_fun (hc x) y
  let B : G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap.symm.toLinearMap.comp ((innerSL ℝ).toLinearMap.comp D.toLinearMap) -- semilinear
  have hb (x y) : B x y=⟪D x,y⟫ := rfl
  have hr (x y z) : B (G.ad x y) z = - B y (G.ad x z) := by rw [hb,hb,← he,Gauge.ad_skew]
  -- cf. invariant_two
  have hp (x y z) : B (G.ad x y) z = B x (G.ad y z) := by rw [skew_ad x y,map_neg,LinearMap.neg_apply, hr,neg_neg]
  have hv (x y z) : B (G.ad x y) z=B z (G.ad x y) := by rw [hr,skew_ad x z,map_neg,neg_neg,← hp,hr,skew_ad,map_neg,neg_neg]
  have hm (x y) : ⟪D x,y⟫ = ⟪D y,x⟫ := LinearMap.congr_fun (show B.flip y=B y from LinearMap.ext_on (ad_span h) (by rintro z ⟨a,b,rfl⟩; exact hv a b y)) x
  apply ContinuousLinearMap.ext; intro x; apply ext_inner_right ℝ; intro y; change ⟪D x,y⟫=⟪(0:G.Color),y⟫
  have hh := ContinuousLinearMap.adjoint_inner_left D x y
  rw [hw,neg_apply, inner_neg_left,real_inner_comm (D x)] at hh
  rw [inner_zero_left]; linarith [hm x y]

lemma tangent_form {D : Door G} (h : G.Simple) (hx : D†= -D) (hv : ∀ x, D*adh G x-adh G x*D∈ Store G) : D ∈ Store G := by
  choose f hf using hv
  let A : G.Color →ₗ[ℝ] G.Color := {
    toFun := f
    map_add' x y := faithAd h (by rw [hf,map_add,map_add,hf,hf]; simp only [mul_add,add_mul]; abel)
    map_smul' t x := faithAd h (by rw [hf,map_smul,map_smul,hf,RingHom.id_apply,smul_sub]; apply ContinuousLinearMap.ext; intro v; change D (t • _) - t • _ = t • D _-t • _; rw [map_smul]; rfl) }
  let S := A.toContinuousLinearMap
  have hs (x : G.Color) : adh G (S x) = _ := hf x
  have he : derivingD G S := by
    intro x y; apply faithAd h; rw [hs,map_add,adh_bracket x y,adh_bracket (S x),adh_bracket x (S y),hs,hs]; simp only [mul_sub,sub_mul,mul_assoc]; abel
  obtain ⟨v,hv⟩ := innerD h he
  have ho : (D-S)†= -(D-S) := by rw [map_sub,hx,← hv,adh_skew]; abel
  have hm (x) : adh G x*(D-S)=(D-S)*adh G x := by
    have hu : D*adh G x-adh G x*D=S*adh G x-adh G x*S := (hs x).symm.trans (bracketed he x).symm
    rw [mul_sub,sub_mul,←sub_eq_zero, show adh G x*D-adh G x*S-(D*adh G x-S*adh G x)=(S*adh G x-adh G x*S)-(D*adh G x-adh G x*D) by abel,hu,sub_self]
  exact ⟨v,hv.trans (sub_eq_zero.mp (centralizer_zero h ho hm)).symm⟩
end YM.SchemeConversionRG11.Corona
