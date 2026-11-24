import YM.SchemeConversionRG11.Maxwell.Normalize

/-! # Compact track of Lie-normalizing color motions. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open scoped Topology BigOperators RealInnerProductSpace InnerProduct
variable {G : Gauge} {R T : Door G}

def Fair (R : Door G) := ∀ x:G.Color, ‖R x‖=‖x‖
lemma Fair.inner {R : Door G} (h : Fair R) (x y) : ⟪R x,R y⟫=⟪x,y⟫ := (⟨R.toLinearMap,h⟩ : G.Color →ₗᵢ[ℝ] G.Color).inner_map_map ..
lemma Fair.onto (h : Fair R) : Surjective R := LinearMap.surjective_of_injective (f:=R.toLinearMap) (⟨R.toLinearMap,h⟩ : G.Color →ₗᵢ[ℝ] G.Color).injective
lemma Fair.inv (h : Fair R) : R†*R=1 := by
  ext1 x; refine ext_inner_right ℝ fun y ↦ ?_
  change ⟪(R†) (R x),y⟫= _; rw [ContinuousLinearMap.adjoint_inner_left,h.inner]; rfl
lemma Fair.inv' (h : Fair R) : R*R†=1 := by
  ext1 x; obtain ⟨y,rfl⟩ := h.onto x; change R ((R† * R) y)= _; rw [h.inv]; rfl
lemma Fair.back (h : Fair R) : Fair (R†) := fun x ↦ by obtain ⟨y,hy⟩ := h.onto x; subst x; change ‖(R†*R) y‖=_; rw [h.inv,h y]; rfl
lemma Fair.mul (h : Fair R) (hp : Fair T) : Fair (R*T) := fun x ↦ by change ‖R (T x)‖=_; rw [h,hp]
lemma Fair.norm_left (h : Fair R) (U : Door G) : ‖R*U‖=‖U‖ := le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ by change ‖R _‖ ≤ _; rw [h]; exact ContinuousLinearMap.le_opNorm U x)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ by rw [← h (U x)]; exact ContinuousLinearMap.le_opNorm (R*U) x)
lemma Fair.norm_bound (h : Fair R) : ‖R‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp only [one_mul]; rw [h x]

def Tracks (G : Gauge) := {R : Door G | Fair R ∧ ∀ x, R† * adh G x * R∈ Store G}
lemma adj_mul (R T : Door G) : (R*T)† = T†*R† := ContinuousLinearMap.adjoint_comp ..
lemma inMul (h : R∈Tracks G) (k : T∈Tracks G) : R*T∈Tracks G := by
  obtain ⟨h₁,h⟩ := h
  obtain ⟨h₂,k⟩ := k
  refine ⟨Fair.mul h₁ h₂,fun x ↦ ?_⟩
  obtain ⟨p,hp⟩ := h x
  have he : (R*T)†*adh G x*(R*T)=T†*(adh G p)*T := by rw [hp,adj_mul]; simp only [mul_assoc]
  rw [he]; exact k p
lemma scaleR (R T : Door G) (c : ℝ) : R*(c • T)=c • (R*T) := by ext1 x; exact map_smul R c _
lemma scaleL (R T : Door G) (c : ℝ) : (c • R)*T=c • (R*T) := by ext1; rfl
lemma inInv (h : R∈Tracks G) : R†∈Tracks G := by
  rcases h with ⟨h,hK⟩
  let L : Store G →ₗ[ℝ] Store G := {
    toFun v := ⟨R†*v.val*R,by obtain ⟨x,hx⟩ := v.property; rw [← hx]; exact hK x⟩
    map_add' x y := by apply Subtype.ext; dsimp; rw [mul_add,add_mul]
    map_smul' t v := by apply Subtype.ext; dsimp; rw [scaleR,scaleL] }
  have hs (b : Door G) : R*(R†*b*R)*R†=b := by calc
    _ = (R*R†)*b*(R*R†) := by simp only [mul_assoc]
    _ = _ := by rw [Fair.inv' h,one_mul,mul_one]
  have hi : Injective L := by
    intro u v he; apply Subtype.ext
    have hh := congr_arg (fun y : Store G ↦ R*y.val*R†) he; change R*_ * R†=R*(R†*v.val*R)*R† at hh; exact (hs u.val).symm.trans (hh.trans (hs v.val))
  have ht := LinearMap.surjective_of_injective (K:=ℝ) (V:=Store G) (f:=L) hi
  refine ⟨Fair.back h,fun x ↦ ?_⟩
  obtain ⟨v,hL⟩ := ht (⟨adh G x,x,rfl⟩ : Store G)
  rw [ContinuousLinearMap.adjoint_adjoint,← show (L v).val=adh G x from congr_arg Subtype.val hL]
  change R*(R†*v.val*R)*R†∈ Store G; rw [hs]; exact v.property
lemma pier (G : Gauge) : IsCompact (Tracks G) := by
  have he : IsClosed (Tracks G) := by
    have hf : Tracks G = {R : Door G|Fair R} ∩ ⋂ i, {R : Door G| R†*adh G i* R∈Store G} := by ext; simp [Tracks]
    rw [hf]; apply IsClosed.inter
    · rw [show {R : Door G|Fair R}=⋂ v:G.Color,{R| ‖R v‖=‖v‖} by ext; simp [Fair]]
      exact isClosed_iInter fun v ↦ isClosed_eq (((ContinuousLinearMap.apply ℝ G.Color v).continuous).norm) continuous_const
    apply isClosed_iInter; intro x; apply (Store G).closed_of_finiteDimensional.preimage (f:=fun R : Door G ↦ R†*adh G x* R)
    have hx : Continuous (fun R:Door G ↦ R†) := ContinuousLinearMap.adjoint.continuous
    exact (hx.mul (continuous_const (y:=adh G x))).mul continuous_id
  exact (isCompact_closedBall (0:Door G) 1).of_isClosed_subset he fun i hi ↦ (mem_closedBall.mpr (by rw [dist_zero_right]; exact Fair.norm_bound hi.1))

def firm (u : G.El) : Door G := (G.adjoint u).toContinuousLinearMap
lemma firmFair (u : G.El) : Fair (firm u) := fun x ↦ G.norm_adjoint u x
lemma firm_one : firm (1 : G.El)=1 := ContinuousLinearMap.ext fun i ↦ G.adjoint_one i
lemma firm_mul (u v : G.El) : firm (u*v)=firm u*firm v := ContinuousLinearMap.ext fun i ↦ G.adjoint_mul u v i
lemma firm_inv (u : G.El) : firm u⁻¹=(firm u)† := by
  nth_rw 1 [← one_mul (firm u⁻¹)]
  rw [← (firmFair u).inv, mul_assoc, ← firm_mul u u⁻¹, mul_inv_cancel,firm_one,mul_one]

def bracketForm (R : Door G) := ∀ x y:G.Color, R (G.ad x y) = G.ad (R x) (R y)
lemma firmBracket (u : G.El) : bracketForm (firm u) := by
  intro x y; apply G.colorMat_injective
  change G.colorMat (G.adjoint u (G.ad x y)) = _
  rw [G.mat_adjoint]
  change _ = G.colorMat (G.ad (G.adjoint u x) (G.adjoint u y))
  simp only [G.colorMat_ad,G.mat_adjoint,Gauge.conjugate,mul_sub,sub_mul]
  have hv (a b : G.Mat) : G.mat u*a*star (G.mat u)*(G.mat u*b*star (G.mat u))=G.mat u*(a*b)*star (G.mat u) := by
    calc
      _ = G.mat u * a * (star (G.mat u)*G.mat u)*b*star (G.mat u) := by simp only [mul_assoc]
      _ = _ := by rw [G.mat_star_mul, mul_one,mul_assoc (G.mat u) a]
  rw [hv,hv]
lemma autos_in (h : bracketForm (R†)) (hp : Fair R) : R ∈ Tracks G := by
  refine ⟨hp,fun x ↦ ⟨(R†) x,?_⟩⟩; ext1 y; change G.ad ((R†) x) y= (R†) (G.ad x (R y)); rw [h,show (R†) (R y)=_ from DFunLike.congr_fun hp.inv y]; rfl
lemma firm_tracks (u : G.El) : firm u∈Tracks G := autos_in (firm_inv u ▸ firmBracket _) (firmFair _)

end YM.SchemeConversionRG11.Corona
