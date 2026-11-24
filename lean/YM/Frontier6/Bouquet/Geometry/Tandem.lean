import YM.Frontier6.Bouquet.Geometry.Lights
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
/-!
# Tandems. Restrict attention to finite spaces, using standard Lebesgue
 integrations so every orthogonal split preserves. The Borel instance on Room
 is for programming projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp
-- prevent ambiguous ambient; ambient measurable chosen Borel and restrictions
-- (no measures on Room used).
scoped instance : MeasurableSpace Room:= borel Room
scoped instance : BorelSpace Room := ⟨rfl⟩
open scoped YM.Frontier6.Bouquet
variable {P Q R:Place}
structure Tandem (P Q R:Place):Prop where
   orth : Q≤Pᗮ
   full : P⊔Q=R
namespace Tandem
variable (h:Tandem P Q R)
include h
lemma lft : P≤R:=h.full ▸ le_sup_left
lemma rgt : Q≤R:=h.full ▸ le_sup_right
lemma symm : Tandem Q P R:=⟨fun x hx y hy=> inner_left_of_mem_orthogonal hx (h.orth hy), (sup_comm ..).trans h.full⟩
lemma dim_eq [FiniteDimensional ℝ P][FiniteDimensional ℝ Q]: dim P+dim Q=dim R:=by
    rw [← h.full]; have he:=finrank_sup_add_finrank_inf_eq P Q; rw [(Disjoint.mono_right h.orth P.orthogonal_disjoint).eq_bot,finrank_bot,add_zero] at he; exact he.symm
lemma assembled (u : R) : ∃ x:P,∃ y:Q, (x.val+y.val)=u.val:= by obtain ⟨x,hx,y,hy,he⟩:= mem_sup.mp ((h.full) ▸ u.property : u.val ∈ P⊔Q); exact ⟨⟨x,hx⟩,⟨y,hy⟩,he⟩
def together : P × Q→ₗ[ℝ] R:= (Submodule.inclusion h.lft).coprod (Submodule.inclusion h.rgt)
lemma together_eq (p:P)(q:Q) : (together h (p,q)).val=p.val+q.val:= rfl
abbrev Pi (P Q:Place):= WithLp 2 (P×Q)
def belt : Pi P Q ≃ₗᵢ[ℝ] R:=by
    let F : Pi P Q →ₗ[ℝ] R:= together h ∘ₗ (WithLp.linearEquiv 2 ℝ (P × Q)).toLinearMap
    have hf : ∀ x y, ⟪F x,F y⟫_ℝ=⟪x,y⟫_ℝ:= by
       intro x y; obtain ⟨⟨x,u⟩,rfl⟩:= WithLp.toLp_surjective (V:= P × Q) 2 x; obtain ⟨⟨y,v⟩,rfl⟩:= WithLp.toLp_surjective (V:= P × Q) 2 y
       change ⟪x.val+u.val,y.val+v.val⟫_ℝ=⟪x.val,y.val⟫_ℝ+⟪u.val,v.val⟫_ℝ; simp_rw [inner_add_left,inner_add_right,inner_right_of_mem_orthogonal x.property (h.orth v.property),inner_left_of_mem_orthogonal y.property (h.orth u.property),add_zero,zero_add]
    let f:= LinearMap.isometryOfInner (E:=Pi P Q) (E':=R) (𝕜:=ℝ) F hf; apply LinearIsometryEquiv.ofSurjective f; intro z; obtain ⟨i,j,hij⟩:= h.assembled z; exact ⟨WithLp.toLp 2 (i,j),Subtype.ext hij⟩
lemma belt_at (z:P × Q): belt h (WithLp.toLp 2 z)= together h z:= rfl
abbrev decoration : P × Q ≃ₜ R:= (WithLp.prodContinuousLinearEquiv 2 ℝ P Q).symm.toHomeomorph.trans (h.belt.toHomeomorph)
lemma decorating :(decoration h:P×Q→R)= together h:=rfl

section
variable [FiniteDimensional ℝ P][FiniteDimensional ℝ Q][FiniteDimensional ℝ R]
lemma expenses : MeasurePreserving (together h):= h.belt.measurePreserving.comp (WithLp.volume_preserving_toLp P Q) -- defeq?
lemma masked : MeasurableEmbedding (together h):= h.decoration.toMeasurableEquiv.measurableEmbedding
variable {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]{f:R→ Y}(he:Integrable f)
include he
lemma integrable : Integrable (fun v:P × Q=> f (together h v)) ((volume:Measure P).prod (volume: Measure Q)):= h.expenses.integrable_comp_of_integrable he
lemma integral : (∫ x:R,f x)= ∫ x:P, ∫ y:Q, f (together h (x,y)):= (h.expenses.integral_comp h.masked f).symm.trans (integral_prod _ (h.integrable he))
end
end Tandem
end YM.Frontier6.Bouquet
