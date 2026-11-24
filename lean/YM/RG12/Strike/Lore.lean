import Mathlib.Analysis.Analytic.IteratedFDeriv
import YM.MSbar.Dim.Plane -- Euclidean iso helper only
/-!
# Isotropic moments over our compact radial subtractions

Tools for cancelling Taylor-engineering dilation resonance at one cubic action vertex. No analytic
extension through coincidence in these moment formulas; exact Lebesgue integrals on
arbitrary compact annular layouts. Real Euclidean dimension (pure), polarize over axes in
that dimension. Not MS-bar subtraction! Reuse only Euclidean-space Mathlib and the rotation
facts.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Finset
abbrev Axis4:=Fin 4
abbrev R:=EuclideanSpace ℝ Axis4
local notation "P"=>ContinuousMultilinearMap
section pol
variable {α:Type*}[Fintype α]
-- basis-free uniqueness on diagonals by Mathlib calculus diagonal derivative
lemma unique (A B:P ℝ (fun _:α=> R) ℂ)(hA:∀ (σ:Equiv.Perm α) y,A (y∘σ)=A y)(hB:∀ (σ:Equiv.Perm α) y,B (y∘σ)=B y)(h:∀ x,A (fun _=>x)=B (fun _=>x)) : A=B:=by
   let e:=Fintype.equivFin α;let n:=Fintype.card α
   let f:= A.domDomCongr e -- order?
   let g:= B.domDomCongr e
   have hf: (fun x=>f (fun _=>x))=(fun x=>g (fun _=> x)):=funext h
   ext1 v
   have he := congr_arg (fun h:R→ℂ=> iteratedFDeriv ℝ n h 0 (v∘e.symm)) hf
   change iteratedFDeriv ℝ n (fun x=>f (fun _=>x)) 0 (v∘e.symm)=_ at he
   rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal,ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal] at he
   let m:= Fintype.card (Equiv.Perm (Fin n))
   have hm:(m:ℂ)≠0:=by exact_mod_cast (show m≠0 from Fintype.card_ne_zero)
   have ht(X:P ℝ (fun _:α=>R) ℂ)(hX:∀ (σ:Equiv.Perm α) y,X (y∘σ)=X y) (σ : Equiv.Perm (Fin n)) : X.domDomCongr e (fun i=> (v∘e.symm) (σ i))=X v:= hX ((e.trans σ).trans e.symm) v
   change ∑ σ: Equiv.Perm (Fin n), _ = ∑ σ:Equiv.Perm (Fin n),_ at he
   dsimp only [f,g] at he; rw [Finset.sum_congr rfl (fun i _=> ht A hA i),sum_congr rfl (fun i _=> ht B hB i)] at he
   simp only [sum_const, card_univ,nsmul_eq_mul] at he; exact mul_left_cancel₀ hm he
variable (w:R→ℂ)
def bill (w:R→ℂ)(v : α → R)(x:R):ℂ:=w x * (∏ i, (↑(⟪v i, x⟫_ℝ):ℂ))
lemma bill_inside (x:R)(v:α→R): ‖bill w v x‖ ≤ ‖w x‖*‖x‖^Fintype.card α*∏i,‖v i‖:=by
   unfold bill; rw [norm_mul,norm_prod, mul_assoc]
   refine mul_le_mul_of_nonneg_left (le_trans (b:=∏ i,‖x‖ * ‖v i‖) ?_ ?_) (norm_nonneg _)
   · apply Finset.prod_le_prod (g:=fun i=>‖x‖*‖v i‖)
     · intro i hi; exact norm_nonneg _
     intro i hi; rw [Complex.norm_real]; exact (norm_inner_le_norm _ _).trans_eq (mul_comm ..)
   rw [Finset.prod_mul_distrib,prod_const,card_univ]
structure Annular (w:R→ℂ):Prop where
    continu : Continuous w
    compact : HasCompactSupport w
structure Round (w:R→ℂ) : Prop extends Annular w where
    iso (U:R≃ₗᵢ[ℝ] R)(x:R): w (U x)=w x
variable (hw:Annular w)
include hw
lemma weighted {f : R→ℂ}(h:Continuous f):Integrable (fun x=>w x * f x) := Continuous.integrable_of_hasCompactSupport (hw.continu.mul h) (hw.compact.mul_right)
lemma billable (v:α→R): Integrable (bill w v):=weighted w hw (by fun_prop (disch:=exact Complex.continuous_ofReal)) -- syntax?
variable [DecidableEq α]
omit hw in
lemma billing (i:α)(u v:R)(x:R)(g:α→R):bill w (Function.update g i (u+v)) x=bill w (Function.update g i u) x+bill w (Function.update g i v) x:=by
   have he (u:R):bill w (Function.update g i u) x=w x*((⟪u,x⟫_ℝ:ℂ)*∏ j∈univ.erase i,(⟪g j,x⟫_ℝ:ℂ)):=by
      unfold bill; rw [← mul_prod_erase _ _ (Finset.mem_univ i),Function.update_self]; apply congr_arg (fun t=>w x*((⟪u,x⟫_ℝ:ℂ)*t)); apply prod_congr rfl; intro a ha; rw [Function.update_of_ne (ne_of_mem_erase ha)]
   rw [he,he,he,inner_add_left,Complex.ofReal_add]; ring
omit hw in
lemma discount (i:α)(u:R)(t:ℝ)(x:R)(g:α→R):bill w (Function.update g i (t • u)) x=t • bill w (Function.update g i u) x:=by
   unfold bill; rw [← mul_prod_erase _ _ (Finset.mem_univ i),Function.update_self, ← mul_prod_erase _ (fun i_1=>_) (Finset.mem_univ i),Function.update_self,real_inner_smul_left,Complex.ofReal_mul,Complex.real_smul]
   have he: (∏ j∈univ.erase i, (↑⟪Function.update g i (t • u) j,x⟫_ℝ:ℂ))=(∏ j∈univ.erase i,(↑⟪Function.update g i u j,x⟫_ℝ:ℂ)):= by
      apply prod_congr rfl;intro j hj; rw [Function.update_of_ne (ne_of_mem_erase hj),Function.update_of_ne (ne_of_mem_erase hj)]
   rw [he]; ring
def census : MultilinearMap ℝ (fun _:α=>R) ℂ where
   toFun v:= ∫ x,bill w v x
   map_update_add' v i u t :=by
      simp_rw [billing,integral_add (billable w hw _) (billable w hw _)] -- update decidableEq may vary
   map_update_smul' v i c t:=by simp_rw [discount,MeasureTheory.integral_smul]
-- `DecidableEq α` not used in definition if proofs? include?
def duty : P ℝ (fun _:α=>R) ℂ where
   toMultilinearMap:= census (α:=α) w hw
   cont:=by
       let f(x:R):= ‖w x‖*‖x‖^Fintype.card α; have hf:Continuous f:=by unfold f;exact (hw.continu.norm).mul (continuous_norm.pow _)
       have he:Integrable f:= hf.integrable_of_hasCompactSupport (HasCompactSupport.mul_right hw.compact.norm)
       refine (census (α:=α) w hw).continuous_of_bound (∫ x,f x) ?_
       intro v
       change ‖∫ x,bill w v x‖ ≤ _; rw [← integral_mul_const]; exact norm_integral_le_of_norm_le (he.mul_const _) (Filter.Eventually.of_forall (fun x=>bill_inside w x v))
omit [DecidableEq α] in
lemma duty_at (v:α→R) : duty w hw v=∫ x,bill w v x:=rfl
omit [DecidableEq α] in
lemma uniform (σ:Equiv.Perm α)(v:α→R):duty w hw (v ∘σ)=duty w hw v:=by
   rw [duty_at,duty_at]; unfold bill; congr 1; funext x; rw [show ∏ i, (↑(⟪(v ∘σ) i,x⟫_ℝ):ℂ) = _ from Fintype.prod_equiv σ (fun i=> (↑(⟪(v ∘σ) i,x⟫_ℝ):ℂ)) (fun i=>(↑⟪v i,x⟫_ℝ :ℂ)) (fun _=>rfl)]
omit hw [DecidableEq α] in
lemma credit_rotated (h:Round w)(v:R)(U:R≃ₗᵢ[ℝ] R): duty w h.toAnnular (fun _:α=>U v)=duty w h.toAnnular (fun _:α=>v):=by
   simp only [duty_at]
   suffices he : (fun x=> bill w (fun _:α => U v) (U x))=fun x=>bill w (fun _:α=>v) x by
      let E:= (U.toHomeomorph.toMeasurableEquiv)
      have hx:= U.measurePreserving.integral_comp E.measurableEmbedding (fun x=>bill w (fun _:α=>U v) x)
      convert hx.symm using 1
      rw [←he]
   unfold bill; simp only [h.iso,U.inner_map_map]

omit hw
-- Euclidean axis helper
abbrev bar (x:Axis4):R:=EuclideanSpace.basisFun Axis4 ℝ x
@[simp] lemma norm_bar (x:Axis4) : ‖bar x‖=1:= (EuclideanSpace.basisFun Axis4 ℝ).norm_eq_one _
--@ simp normalize δ axes
lemma dot_bar (x y:Axis4) : ⟪bar x,bar y⟫_ℝ=if x=y then 1 else 0:= by
   split
   · next h=>subst y; simp
   next h=>exact (EuclideanSpace.basisFun Axis4 ℝ).orthonormal.2 h
lemma project (x:R)(i:Axis4):⟪bar i,x⟫_ℝ = x i:=by
   rw [←(EuclideanSpace.basisFun Axis4 ℝ).repr_apply_apply, EuclideanSpace.basisFun_repr]
omit [DecidableEq α] in
lemma duty_diag (h:Round w)(v:R)(i:Axis4): duty w h.toAnnular (fun _:α=>v)=duty w h.toAnnular (fun _:α=>bar i)*(↑‖v‖:ℂ)^Fintype.card α:=by
   obtain ⟨U,hU⟩:= MSbar.Dim.norm_action (x:= ‖v‖ • bar i) (y:=v) (by simp only [norm_smul, Real.norm_eq_abs,abs_norm,norm_bar,mul_one])
   conv_lhs => rw [← hU]
   rw [credit_rotated _ h,duty_at,duty_at]; simp only [bill, real_inner_smul_left,Complex.ofReal_mul, Finset.prod_const,card_univ,mul_pow]
   rw [← MeasureTheory.integral_mul_const]
   apply MeasureTheory.integral_congr_ae; filter_upwards with x; ring
omit [DecidableEq α] in
lemma odd_lore (h:Round w)(v:R)(hn: Odd (Fintype.card α)): duty w h.toAnnular (fun _:α=>v)=0:=by
   let f:= duty w h.toAnnular (fun _:α=>v)
   suffices t:-f=f by linear_combination t*(-1/2) -- wrong orientation
   obtain ⟨U,hU⟩:=MSbar.Dim.norm_action (x:=v) (y:=-v) (by simp)
   have he := credit_rotated (α:=α) w h v U; rw [hU] at he
   unfold f; nth_rw 2 [← he]; nth_rw 1 [duty_at]; rw [duty_at];
   simp [bill,hn.neg_pow,← MeasureTheory.integral_neg]
end pol
end YM.RG12.Strike
