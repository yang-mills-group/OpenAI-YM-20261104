import YM.SchemeConversionRG11.FirstW.Vane.Track
import YM.Pert.Triangle.Identities
/-! Color & gauge equivariance here only for concrete local vertices and direct forms. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {X : Type*} [AddCommGroup X] [One X] {n : Side}
def putting (u : G.El) : Wind G X →ₗ[ℝ] Wind G X := LinearMap.pi (fun i=> (G.adjoint u) ∘ₗ LinearMap.proj i)
lemma rail_key (A : Wind G X) (u : G.El) (x : Four X) (s : Walk): rail x s (putting u A)= G.adjoint u (rail x s A) := by
  induction s generalizing x with | nil=> simp [rail] | cons i s ih=> rw [rail,LinearMap.add_apply,LinearMap.add_apply,map_add,ih]; simp only [putting,boardAt,LinearMap.smul_apply,LinearMap.proj_apply,LinearMap.pi_apply,LinearMap.comp_apply,map_smul]
lemma turn_key (A B : Wind G X) (u : G.El) (x : Four X) (s : Walk): swerve x s (putting u A) (putting u B)= G.adjoint u (swerve x s A B) := by
  induction s generalizing x with
  | nil=> simp [swerve]
  | cons i s ih=> rw [swerve_eq,swerve_eq,ih,map_add,rail_key,show boardAt x i (putting u A)= G.adjoint u (boardAt x i A) from by simp only [putting,boardAt,LinearMap.smul_apply,LinearMap.proj_apply,LinearMap.pi_apply,LinearMap.comp_apply,map_smul], Pert.Triangle.bracket_adjoint]
lemma tower_key (A B C : Wind G X) (u : G.El) (x : Four X) (s : Walk): tower G x s (putting u A) (putting u B) (putting u C)= tower G x s A B C := by
  have he (A B : Wind G X) : spire G x s (putting u A) (putting u B) = G.adjoint u (spire G x s A B) := by simp [spire,turn_key]
  rw [tower_eq,tower_eq]; simp only [rail_key,he,Pert.Triangle.inner_adjoint]
lemma letter_key (A : Wind G X) (u : G.El) (x : Four X) (j : ℕ) (h : ℝ) : Bare.wideLinear G j h x (putting u A) = Labels.Taylor.paint u (Bare.wideLinear G j h x A) := by
  have eh (B : Wind G X) i a b : Bare.wideCurl (putting u B) b i a=G.adjoint u (Bare.wideCurl B b i a) := by simp [Bare.wideCurl,putting]
  have hp s: Bare.wideLink G s (putting u A)=putting u (Bare.wideLink G s A) := funext fun i=> by simp only [putting,LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply,Bare.wideLink_apply,map_smul]
  have hr (B : Wind G X) (x : Four X): Bare.wideCore G j x (putting u B) =fun i a p=> G.adjoint u (Bare.wideCore G j x B i a p) := by funext i a p; rw [Bare.wideCore_apply,Bare.wideCore_apply]; simp only [eh,map_sum,map_smul]
  simp only [Bare.wideLinear,LinearMap.sum_apply,LinearMap.smul_apply, LinearMap.comp_apply,hp,hr,map_sum,map_smul,Labels.Taylor.turn_paint,show ∀ q:Bare.Response G j,Labels.Taylor.paint u (Bare.radialMap q) = Bare.radialMap (fun i a p=>G.adjoint u (q i a p)) from fun q=> (Bare.radial_color u q).symm]
lemma putting_mark (A : Wind G X) (u : G.El) (x : Four X) (j : ℕ) (B : Wind G X) : sheer G j x (putting u A) (putting u B) = Labels.Taylor.paint u (sheer G j x A B) := by
  have hp (B : Wind G X) s: Bare.wideLink G s (putting u B)=putting u (Bare.wideLink G s B) := funext fun i=> by simp only [putting,LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply,Bare.wideLink_apply,map_smul]
  have he (A B : Wind G X) (x : Four X) : rush G x j (putting u A) (putting u B) = fun i a p=> G.adjoint u (rush G x j A B i a p) := by
    funext i a p; simp [rush,turn_key]
  simp only [sheer_eq,hp,he,map_sum,map_smul,Labels.Taylor.turn_paint,show ∀ q:Bare.Response G j,Labels.Taylor.paint u (Bare.radialMap q) = Bare.radialMap (fun i a p=>G.adjoint u (q i a p)) from fun q=> (Bare.radial_color u q).symm]
omit [AddCommGroup X] [One X] in
lemma putting_node (u : G.El) (A : Wind G X) (i) : putting u A i= G.adjoint u (A i) := rfl
lemma branch_put (p : Ear G (Per n)) (u : G.El) : tbranch G n (p ∘ₗ putting u) = putting u⁻¹ (tbranch G n p) := by
  funext i; apply ink_eq; intro v; rw [branch_elem,putting_node,←Pert.Triangle.inner_adjoint _ _ u, ←G.adjoint_mul, mul_inv_cancel,G.adjoint_one,branch_elem]; exact congrArg p (funext (fun l=>by simp [putting,Orb.ghostLink, apply_ite (G.adjoint u)]))
end YM.RG11.FirstW
