import YM.Frontier6.Bouquet.Anise.Steps

/-! Restrict an annular shape along a moving center. Constant Jacobians
 absorbed only upon actual measure splits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {X:Type*}{P Q R:Place}[FiniteDimensional ℝ P][FiniteDimensional ℝ Q]
abbrev insideCL (h:P≤Q) : P →L[ℝ] Q:= LinearMap.toContinuousLinearMap (Submodule.inclusion h)
variable (h:P≤Q)(z:Q)(s:Full Q)(x:P)
abbrev forward (h:P≤Q)(z:Q)(x:P):Q:= z+insideCL h x
lemma forward_cast : (forward h z x).val=z.val+x.val:=rfl
lemma forwards : Isometry (forward h z):= by apply Isometry.of_dist_eq; intro i j; unfold forward; rw [dist_add_left]; rfl

def restrictS : Full Q →ₗ[ℂ] Full P where
  toFun f:= by
    letI:=FiniteDimensional.complete ℝ P; exact ⟨f ∘ forward h z, f.contDiff.comp (contDiff_const.add (insideCL h).contDiff), f.hasCompactSupport.comp_isClosedEmbedding ((forwards h z).isClosedEmbedding),subset_univ _⟩
  map_add' _ _:= rfl
  map_smul' _ _:=rfl
@[simp] lemma restrict_at : restrictS h z s x=s (forward h z x):=rfl
lemma restrict_fun : (restrictS h z s : P→ℂ)= s ∘ forward h z:=rfl
lemma restrict_support : tsupport (restrictS h z s) ⊆ forward h z ⁻¹' tsupport s:= by rw [restrict_fun]; exact tsupport_comp_subset_preimage _ (forwards h z).continuous
lemma restrict_comp [FiniteDimensional ℝ R](he:Q≤R)(f:Full R)(y:R): restrictS h z (restrictS he y f)=restrictS (h.trans he) (forward he y z) f:=by ext1 x; simp only [restrict_at]; apply congr_arg f; apply Subtype.ext; simp [forward_cast, add_assoc]
lemma restrict_zero (s:Full P) : restrictS (le_refl P) 0 s=s:=by ext1 x; simp [forward]; rfl
lemma rides_affine (u:Room)(hx:u∈P) : restrictS h z (ride Q u s) = ride P u (restrictS h z s):=by
    let y:P:=⟨u,hx⟩
    ext1 x
    unfold ride; simp_rw [restrict_at,step_cast, restrict_fun]
    unfold Analysis.D; rw [fderiv_comp, show fderiv ℝ (forward h z) x=insideCL h from ((insideCL h).hasFDerivAt.const_add z).fderiv];
    · change _= (_ : Q →L[ℝ] ℂ) (insideCL h (ontoSpace P u)); rw [show ontoSpace Q u=insideCL h y from on_home (insideCL h y),show ontoSpace P u=y from on_home y]
    all_goals first| exact s.contDiff.differentiable (by simp) _|exact differentiableAt_const _| exact ((insideCL h).hasFDerivAt.const_add z).differentiableAt
lemma pedal_restricted (u:List Room) (he:∀ x ∈ u,x∈ P): restrictS h z (pedal Q u s)=pedal P u (restrictS h z s):=by
    induction u generalizing s with
    | nil=>rfl
    | cons i t ih=>
       change restrictS h z (ride Q i (pedal Q t s))=ride P i (pedal P t _); rw [rides_affine h z (pedal Q t s) i (he i (by simp)), ih _ (fun k hk=> he _ (List.mem_cons_of_mem i hk))]
lemma train_restricted (u:Multiset Room)(he: ∀ x∈ u,x∈ P): restrictS h z (train Q u s)=train P u (restrictS h z s):=by
    generalize hc:u.toList=w; -- equality syntax?
    have hh:(w:Multiset Room)=u:=by rw [← hc,Multiset.coe_toList];
    rw [← hh,train_list,train_list]; exact pedal_restricted _ _ _ _ (fun x hx=> he x (hh ▸ Multiset.mem_coe.mpr hx))
end YM.Frontier6.Bouquet
