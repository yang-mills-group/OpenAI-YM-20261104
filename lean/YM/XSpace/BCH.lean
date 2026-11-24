import YM.XSpace.VertexProducts
import YM.Gauge.Casimir
import YM.Push.LOOP_COEFFICIENT.Tangent

/-!
# Taylor truncation of link products used for first-order diagrams

Implement Ward transformations literally at this order using the 2-step BCH group.
Paired with lemmas for both price (cubic) and curvature (through acceleration)
in the actual group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Filter CubicMatch Push.Loops NormedSpace Function
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge}
@[ext] structure Drift (G : Gauge) where
  a : G.Color
  c : G.Color
namespace Drift
instance : One (Drift G):=⟨⟨0,0⟩⟩
instance : Mul (Drift G):=⟨fun x y=>⟨x.a+y.a,x.c+y.c+(1/2:ℝ) • G.ad x.a y.a⟩⟩
instance : Inv (Drift G):=⟨fun x=>⟨-x.a,-x.c⟩⟩
@[simp] lemma a_one : (1:Drift G).a=0:=rfl
@[simp] lemma c_one : (1:Drift G).c=0:=rfl
@[simp] lemma a_mul (x y: Drift G): (x*y).a=x.a+y.a:=rfl
@[simp] lemma c_mul (x y: Drift G): (x*y).c=x.c+y.c+(1/2:ℝ) • G.ad x.a y.a:=rfl
@[simp] lemma a_inv (x: Drift G): x⁻¹.a = -x.a:=rfl
@[simp] lemma c_inv (x: Drift G): x⁻¹.c = -x.c:=rfl
lemma ad_swap (x y : G.Color): G.ad x y= -G.ad y x:= G.colorMat_injective (by simp)
lemma ad_same (x : G.Color): G.ad x x=0:=G.colorMat_injective (by simp)
lemma ad_e (x y : G.Color) : inner ℝ x (G.ad y x)=0:=by
  have hp := Gauge.ad_skew y x x; have he := real_inner_comm x (G.ad y x); linarith


instance : Group (Drift G) where
  one_mul x:= Drift.ext (by simp) (by simp)
  mul_one x:= Drift.ext (by simp) (by simp)
  mul_assoc x y z:= Drift.ext (by simp [add_assoc]) (by simp only [c_mul,a_mul,map_add,LinearMap.add_apply,smul_add]; abel)
  inv_mul_cancel x:=Drift.ext (by simp) (by simp [ad_same])
lemma conjugate (x y : Drift G) : x*y*x⁻¹=⟨y.a,y.c+G.ad x.a y.a⟩:= by
  apply Drift.ext <;> simp only [a_mul,c_mul,a_inv,c_inv,map_neg,map_add,LinearMap.add_apply,ad_same,zero_add,smul_neg]
  · abel
  rw [ad_swap y.a x.a,smul_neg,neg_neg]; module
end Drift

section ray
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {v : ℝ → E}
lemma line (x : E) : ContDiffAt ℝ ω (fun t:ℝ=> t • x) 0:= by fun_prop
lemma iterated_line (x : E) (k : ℕ) : iteratedDeriv k (fun t:ℝ=> t • x) 0=if k=1 then x else 0:=by
  by_cases h:k=0; simp [h]
  let L:=ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
  change iteratedFDeriv ℝ k (L ∘ id) 0 _ = _
  rw [L.iteratedFDeriv_comp_left (x:=(0:ℝ)) (n:=ω) contDiffAt_id le_top]
  change L (iteratedDeriv k id (0:ℝ))=_
  rw [iteratedDeriv_id]; simp only [if_neg h]; split_ifs; exact one_smul _ _; rw [map_zero]
lemma along (x : E) (n : ℕ) (hf : ContDiffAt ℝ ω f 0) : iteratedDeriv n (fun t:ℝ => f (t • x)) 0= iteratedFDeriv ℝ n f 0 fun _=>x:=by
  let L:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x
  have h : L (1:ℝ)=x:= one_smul _ _
  change iteratedFDeriv ℝ n (f ∘ L) 0 _=_
  rw [jet_comp_linear _ (show ContDiffAt ℝ (↑n) f (L 0) by rw [map_zero]; exact hf.of_le le_top),map_zero]; simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,h]
lemma term_two (x : ℝ → E) : (2:ℝ) • term 2 x=iteratedDeriv 2 x 0:=by simp only [term,Nat.factorial, smul_smul]; norm_num
lemma term_vcomp_two (hf : ContDiffAt ℝ ω f (v 0)) (h : ContDiffAt ℝ ω v 0) : term 2 (f ∘ v)= (2:ℝ)⁻¹ • iteratedFDeriv ℝ 2 f (v 0) (fun _=> deriv v 0)+ fderiv ℝ f (v 0) (term 2 v):=by rw [term, iteratedDeriv_vcomp_two (hf.of_le le_top) (h.of_le le_top),← term_two]; simp only [Nat.factorial, map_smul, smul_add, smul_smul]; norm_num
lemma even_thrice (hf : ContDiffAt ℝ ω f 0) (H : ∀ y, f (-y)=f y) (x : E) : iteratedFDeriv ℝ 3 f 0 (fun _=>x)=0:=by
  rw [← along _ _ hf]
  let L (t:ℝ):= f (t • x)
  have he:=iteratedDeriv_comp_neg 3 L 0; simp only [show (fun t:ℝ=>L (-t))=L from funext fun t=>by simp [L,H],neg_zero] at he
  norm_num at he; change iteratedDeriv 3 L 0=0
  have h : (2:ℝ) • iteratedDeriv 3 L 0=0:=by rw [two_smul]; nth_rw 1 [he]; rw [neg_add_cancel]
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)
end ray

-- Matrix-H path normalization (second entry divided by 2).
structure Fits (f : ℝ → G.El) (x : Drift G) : Prop where
  smooth : ContDiffAt ℝ ω (G.mat ∘ f) 0
  val : f 0=1
  slope : deriv (G.mat ∘ f) 0=G.colorMat x.a
  bend : iteratedDeriv 2 (G.mat ∘ f) 0= (2:ℝ) • G.colorMat x.c+G.colorMat x.a * G.colorMat x.a
namespace Fits
set_option backward.isDefEq.respectTransparency false
variable {x y : Drift G} {f g : ℝ → G.El}

lemma exp_a (x : G.Color) : iteratedFDeriv ℝ 2 (G.mat ∘ G.lieExp) 0 (fun _=>x)=G.colorMat x*G.colorMat x:=by
  rw [← along _ _ (f:=G.mat ∘ G.lieExp) G.exp_jet.contDiffAt]
  let X:=G.colorMat x
  let v (u:ℝ):= NormedSpace.exp (u • X)
  have ht (u : ℝ) : HasDerivAt v (v u * X) u:= by apply hasDerivAt_exp_smul_const
  rw [show (fun t:ℝ=> (G.mat ∘ G.lieExp) (t • x)) = v from funext fun t => by simp [v,X]]; rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ',iteratedDeriv_one, show deriv v= _ from funext (fun u=> (ht u).deriv)]
  rw [((ht 0).mul_const X).deriv]; simp only [v,zero_smul, NormedSpace.exp_zero,one_mul]; rfl

lemma along_a (a:G.Color) : Fits (fun t:ℝ=> G.lieExp (t • a)) ⟨a,0⟩:=by
  let F:=G.mat ∘ G.lieExp
  have h:=G.exp_jet.contDiffAt (x:=0)
  refine ⟨ContDiffAt.comp (g:=F) _ (by simpa only [F,comp_def,zero_smul] using h) (line a),by simp,?_,?_⟩
  · suffices iteratedDeriv 1 (fun t:ℝ=> F (t • a)) 0 = G.colorMat a by simpa only [iteratedDeriv_one,comp_def,F] using this
    rw [along a 1 (f:=F) h, iteratedFDeriv_one_apply,show fderiv ℝ F 0 =_ from G.expDiff_zero.fderiv]; rfl
  change iteratedDeriv 2 (fun t:ℝ=> F (t • a)) 0 = _; rw [along a 2 (f:=F) h]; dsimp only [F]; rw [exp_a]; simp
lemma unit (G : Gauge) : Fits (fun _ => (1:G.El)) 1:=by simpa [show (1:Drift G)=⟨0,0⟩ from rfl] using along_a (0:G.Color)
lemma inverse (h : Fits f x) : Fits (fun t=> (f t)⁻¹) x⁻¹:=by
  let L : G.Mat ≃L[ℝ] G.Mat:=starL ℝ
  have hh {n : ℕ} : iteratedDeriv n (fun t : ℝ => G.mat (f t)⁻¹) 0=star (iteratedDeriv n (G.mat ∘ f) 0):=by
    change iteratedFDeriv ℝ n (L.toContinuousLinearMap ∘ (G.mat ∘ f)) 0 _ = _
    rw [L.toContinuousLinearMap.iteratedFDeriv_comp_left h.smooth le_top]; rfl
  refine ⟨ContinuousLinearEquiv.contDiff L |>.contDiffAt.comp 0 h.smooth,by simp [h.val],?_,?_⟩
  · suffices iteratedDeriv 1 (fun t:ℝ => G.mat (f t)⁻¹) 0= G.colorMat x⁻¹.a by simpa only [comp_def, iteratedDeriv_one] using this
    rw [hh]; simp [h.slope,G.colorMat_skew]
  change iteratedDeriv 2 (fun t:ℝ => G.mat (f t)⁻¹) 0=_; rw [hh]; simp [h.bend,G.colorMat_skew]
lemma product (h : Fits f x) (p : Fits g y) : Fits (fun t=> f t*g t) (x*y) := by
  let M:=G.mat ∘ f; let N:=G.mat ∘ g
  have hd := h.smooth.differentiableAt (by simp)
  have he := p.smooth.differentiableAt (by simp)
  have hz : M 0=1:= by simp [M,h.val]
  have hu : N 0=1:= by simp [N,p.val]
  refine ⟨h.smooth.mul p.smooth,by simp [h.val,p.val],?_,?_⟩
  · change deriv (fun t:ℝ => M t * N t) 0 =_; rw [deriv_fun_mul (c:=M) (d:=N) hd he,hz,hu,show deriv M 0=_ from h.slope,show deriv N 0=_ from p.slope]; simp
  change iteratedDeriv 2 (M*N) 0 = _
  rw [iteratedDeriv_mul (f:=M) (g:=N) (h.smooth.of_le le_top) (p.smooth.of_le le_top)]
  simp only [Drift.a_mul,Drift.c_mul,map_add,map_smul,G.colorMat_ad,smul_add,smul_smul]
  norm_num [Finset.sum_range_succ,hz,hu,Nat.choose, show deriv M 0=_ from h.slope, show deriv N 0=_ from p.slope, show iteratedDeriv 2 M 0=_ from h.bend, show iteratedDeriv 2 N 0=_ from p.bend]; simp only [two_smul]; noncomm_ring
end Fits
namespace Fits
variable {x y : Drift G} {f g : ℝ → G.El}
set_option backward.isDefEq.respectTransparency false

def logarithm (f : ℝ → G.El) (t : ℝ) := G.plog (G.mat (f t))
lemma log_zero (h : Fits f x): logarithm f 0=0:=by simp [logarithm,h.val]
lemma log_smooth (h : Fits f x): ContDiffAt ℝ ω (logarithm f) 0:= ContDiffAt.comp (g:=G.plog) (f:= G.mat ∘ f) 0 (by simp only [comp_apply,h.val,G.mat_one]; exact G.plog_diff) h.smooth
lemma reconstruct_log (h : Fits f x): G.lieExp ∘ logarithm f =ᶠ[𝓝 0] f:=by
  have he : Tendsto f (𝓝 0) (𝓝 (1:G.El)):= tendsto_mat.mpr (by simpa only [comp_apply,h.val] using h.smooth.continuousAt.tendsto)
  exact he.eventually G.plog_right
lemma log_deriv (h : Fits f x): deriv (logarithm f) 0=x.a:=by
  apply G.colorMat_injective
  let F:=G.mat ∘ G.lieExp
  have hp : F ∘ logarithm f =ᶠ[𝓝 0] G.mat ∘ f:= h.reconstruct_log.mono fun t ht=> congr_arg G.mat ht
  have he : HasFDerivAt F G.colorMat.toContinuousLinearMap (logarithm f 0):=by rw [h.log_zero]; exact G.expDiff_zero
  rw [← h.slope,← hp.deriv_eq]; exact (he.comp_hasDerivAt 0 (h.log_smooth.differentiableAt (by simp)).hasDerivAt).deriv.symm
lemma log_second (h : Fits f x): iteratedDeriv 2 (logarithm f) 0=(2:ℝ) • x.c:=by
  apply G.colorMat_injective
  let F:=G.mat ∘ G.lieExp
  have hp : F ∘ logarithm f =ᶠ[𝓝 0] G.mat ∘ f:= h.reconstruct_log.mono fun t ht=> congr_arg G.mat ht
  have he := hp.iteratedDeriv_eq 2; rw [iteratedDeriv_vcomp_two (show ContDiffAt ℝ 2 F (logarithm f 0) from (h.log_zero.symm ▸ G.exp_jet.contDiffAt.of_le le_top)) (h.log_smooth.of_le le_top), h.bend,h.log_zero,h.log_deriv, show iteratedFDeriv ℝ 2 F 0 (fun _=>x.a)=_ from exp_a x.a,add_comm ((2:ℝ) • G.colorMat x.c),show fderiv ℝ F 0=_ from G.expDiff_zero.fderiv] at he
  rw [map_smul]; exact add_left_cancel he
lemma price (h : Fits f x): term 3 (G.price ∘ f) = ⟪x.a,x.c⟫_ℝ:=by
  let F:=G.price ∘ G.lieExp
  have hp : F ∘ logarithm f =ᶠ[𝓝 0] G.price ∘ f:= h.reconstruct_log.mono fun t ht=> congr_arg G.price ht
  have hi : ContDiffAt ℝ ω F 0:= Work.F03.price_smooth G.exp_jet.contDiffAt
  obtain ⟨h0,hH⟩:= (show fderiv ℝ F 0= 0 ∧ ∀ r s, iteratedFDeriv ℝ 2 F 0 ![r,s]=⟪r,s⟫_ℝ from exp_price_rate)
  rw [← term_congr hp, term,iteratedDeriv_vcomp_three (h.log_zero.symm ▸ hi.of_le le_top) (h.log_smooth.of_le le_top), h.log_zero,h.log_deriv,h0,even_thrice hi (fun x=> by simp only [F,comp_apply,Work.F03.exp_neg_color,G.price_inv]),h.log_second,hH,hH,zero_apply,real_inner_comm _ ((2:ℝ) • x.c),real_inner_smul_right]; norm_num [Nat.factorial,two_smul]; ring
lemma curvature (h : Fits f x): term 2 (G.curvature ∘ f)=x.c:=by
  let S: G.Mat →L[ℝ] G.Mat:= (starL ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap
  let L:= G.projectColor.toContinuousLinearMap.comp ((1/2:ℝ) • (ContinuousLinearMap.id ℝ G.Mat-S))
  have he : ∀ A, L A= G.projectColor ((1/2:ℝ) • (A - star A)):=fun _=> rfl
  change term 2 (fun t=> L ((G.mat ∘ f) t))=_
  rw [term_linear L (h.smooth.of_le le_top),term,h.bend]
  rw [map_smul,he]; simp only [two_smul,star_add,star_mul,G.colorMat_skew,neg_mul_neg]
  let B:= G.colorMat x.c; let A:= G.colorMat x.a
  rw [show (1/2:ℝ) • (B+B+A*A-(-B+ -B+A*A))=B+B by module,map_add,G.project_colorMat]; norm_num [Nat.factorial]; module
end Fits
end YM.XSpace.Chart2
