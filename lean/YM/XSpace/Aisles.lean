import YM.XSpace.Choices

/-!
# Tangent to the positioning equations across any leading affine frame
Use derivative as varying slots at base point on all-horizon correlation arrays.
Get a real operator after restricting field variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ} {E:Type} [AddCommMonoid E] [Module ℂ E]
variable (F B: FieldEnd G d) (Q:MultilinearMap ℂ (fun _ : Fin n=> Sec G d) E)
-- post linear maps from all slots; global test-linear arrays with same arity
abbrev Suite (G:Gauge) (d:ℕ) (n:ℕ) (E:Type) [AddCommMonoid E] [Module ℂ E]:= Test n→ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n=>Sec G d) E

def loaded (L: Fin n→ FieldEnd G d) (P: Suite G d n E): Suite G d n E where
  toFun t:= (P t).compLinearMap L
  map_add' _ _:= by rw [map_add]; rfl
  map_smul' _ _:= by rw [map_smul]; rfl
lemma loads (L:Fin n→FieldEnd G d) (P:Suite G d n E) (t:Test n) (p:Fin n→Sec G d): loaded L P t p=P t (fun i=> L i (p i)):=rfl

def tang (P:Correl G d E):= (fun n=> ∑ i:Fin n, loaded (update (fun _=> F) i B) (P n) : Correl G d E)
lemma touches (P:Correl G d E) (t:Test n) (p:Fin n→Sec G d): tang F B P n t p=∑ i:Fin n,P n t (update (F ∘ p) i (B (p i))):=by
  simp only [tang,LinearMap.sum_apply, sum_apply,loads]; apply Finset.sum_congr rfl; intro i _; apply congr_arg; funext j; by_cases h:j=i <;> simp [h]
lemma tangent (P: Correl G d E): tang 1 B P=varies P B:=by ext n t p; rw [touches,variation]; rfl

def diffusion (P:Correl G d E): FieldEnd G d→ₗ[ℂ] Correl G d E where
  toFun B:= tang F B P
  map_add' X Y:= by ext n t p; change tang _ _ P n t p=tang _ _ P n t p + tang _ _ P n t p; simp_rw [touches,LinearMap.add_apply,MultilinearMap.map_update_add,Finset.sum_add_distrib]
  map_smul' c X:=by ext n t p; change tang _ _ P n t p=c • tang _ _ P n t p; simp_rw [touches,LinearMap.smul_apply,MultilinearMap.map_update_smul, Finset.smul_sum]

def stand (A:Change G d): FieldEnd G d:= 1 + A.val
lemma stood (A:Change G d) (p:Sec G d): stand A p=p+A.val p:=rfl
@[simp] lemma stand0 (d:ℕ): stand (0:Change G d)=(1:FieldEnd G d):=by unfold stand; rw [Submodule.coe_zero,add_zero]
lemma stoop (T:Change G (d+1)) (p:Sec G d): stand T (step d p)=step d (stand (fell d T) p):=by rw [stood,stood,map_add,fells]
lemma solitary (T:Change G d): stand T (leaf G d)=leaf G d:=by rw [stood,T.property.1,add_zero]
lemma stood_reel (T:Change G d) (p:Sec G d): reel d (stand T p)=stand T (reel d p):=by rw [stood,stood,map_add,T.property.2.2.1]
lemma stood_ori (T:Change G d) (s:Signed) (p:Sec G d): ori s.ortho d (stand T p)=stand T (ori s.ortho d p):=by rw [stood,stood,map_add,T.property.2.2.2]
lemma stood_hinge (T:Change G d) (p:Sec G d): hinge d (stand T p)=stand (arch d T) (hinge d p):=by rw [stood,stood,map_add,arched,hinges_back]
lemma reigns (T: Change G d) (P:Correl G d E): recruit (hinge d) (recruit (stand T) P)= recruit (stand (arch d T)) (recruit (hinge d) P):=by
  ext n t p; rw [recruits,recruits,recruits,recruits]; apply congr_arg; ext1 i; simp only [Function.comp_apply,stood_hinge, arches]
variable (A:Screen G d)

def slope (T:Change G d) (P:Prediction G d):= A.D ∘ₗ ((diffusion (stand T) P).restrictScalars ℝ ∘ₗ (Change G d).subtype)
lemma regular (h:A.Prepared) (K:Change G d): slope A 0 (reference G d) K= K:=by change A.D (tang (stand _) _ _)=_; rw [stand0, tangent]; exact h.1 K
end YM.XSpace.Normalize
