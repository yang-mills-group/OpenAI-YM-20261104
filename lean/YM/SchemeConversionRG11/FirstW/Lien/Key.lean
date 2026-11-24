import YM.SchemeConversionRG11.FirstW.Lien.Chips
/-! Interpolate polynomial weights of the *lattice* correction; no DR hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {i j k : ℕ}
lemma choosingR {R U V:Type*} [_root_.Field R] [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V] (L:U→ₗ[R]V) : ∃ g:V→ₗ[R]U,∀ u,L (g (L u))=L u := by
  let M:=L.range; let S : U→ₗ[R] M:=L.rangeRestrict
  obtain ⟨q,hq⟩:= LinearMap.exists_leftInverse_of_injective M.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨F,H⟩:= LinearMap.exists_rightInverse_of_surjective S (LinearMap.range_eq_top.mpr (by rintro ⟨x,u,rfl⟩; exact ⟨u,rfl⟩))
  refine ⟨F.comp q,fun u=>?_⟩
  have hp : q (L u)=S u:=by change q.comp M.subtype (S u)=S u; rw [hq];rfl
  rw [LinearMap.comp_apply,hp]; exact congrArg Subtype.val (show S.comp F (S u) = S u from by rw [H];rfl)
lemma note_fluid (A:Nu G (j+1)) : quietly A.val ↔ flute j A.val=0 := by
 rw [silent]; refine ⟨fun h=>funext fun i=> h i.val (Nat.lt_succ_iff.mp i.isLt),fun h k hk=>?_⟩; have hh:= congrFun h (⟨k,Nat.lt_succ_iff.mpr hk⟩: Fin (j+1)); simp only [flute,LinearMap.comp_apply,scoreW,LinearMap.pi_apply, LinearMap.proj_apply,stageW,Pi.zero_apply] at hh; exact hh -- dependent!
def rootM (G : Gauge) (j : ℕ) : Nu G (j+1) →ₗ[ℝ] Music G j:= (flute j).comp (cabin G (j+1)).subtype
lemma hasFluid (j : ℕ) (x : Nu G (j+1)) (h:rootM G j x=0) : quietly x.val:= by
 apply note_fluid x|>.2; unfold rootM at h; simp only [LinearMap.comp_apply,Submodule.subtype_apply] at h; exact h
lemma easeR (j : ℕ) : ∃ S:Field4 G →ₗ[ℝ] Nu G (j+1), (∃ F: Music G j→ₗ[ℝ] Nu G (j+1), S=F.comp (flute j)) ∧ ∀ x:Nu G (j+1),quietly (S x.val-x).val := by
 obtain ⟨u,hu⟩:= choosingR (rootM G j)
 refine ⟨u.comp (flute j),⟨_,rfl⟩,fun x=>hasFluid j ((u.comp (flute j)) x.val-x) ?_⟩
 have hj : (u.comp (flute j)) x.val = u (rootM G j x):=by simp only [rootM,LinearMap.comp_apply,Submodule.subtype_apply]
 rw [map_sub,hj,hu x,sub_self]
abbrev la (G : Gauge) := Nu G 4
abbrev Rhythm (G : Gauge) := la G→ₗ[ℝ] la G→ₗ[ℝ] ℂ
variable (p : Rhythm G)
def boards (j : ℕ) (h : j≤4) : Nu G j →ₗ[ℝ] la G := Submodule.inclusion (stepped h)
def patchR (p : Rhythm G) (i j:ℕ) (hi:i≤4)(hj:j≤4): Nu G i →ₗ[ℝ] Nu G j→ₗ[ℝ]ℂ:= (p.comp (boards i hi)).compl₂ (boards j hj)
lemma pin (p : Rhythm G) (i j:ℕ) (hi:i≤4)(hj:j≤4)(x : Nu G i)(y : Nu G j): patchR p i j hi hj x y = p (boards i hi x) (boards j hj y):=rfl
lemma boards_val (m:ℕ)(x:Nu G m)(h:m≤4) : (boards m h x).val=x.val := rfl
-- gradient/weight filtration in Rhythm
def ToneR (p: Rhythm G) (d : ℕ) := ∀ a b:la G,p a b=p b a ∧ ∀ i j:ℕ,i+j≤d → a.val∈cabin G i → b.val∈cabin G j → quietly a.val → p a b=0
def pastR (p : Rhythm G) (d:ℕ):= ∀ a b:la G,∀ i j:ℕ,i+j<d → a.val∈cabin G i → b.val∈cabin G j → p a b=0
end YM.RG11.FirstW
