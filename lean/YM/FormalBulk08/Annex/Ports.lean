import YM.FormalBulk08.Annex.Palm
import YM.FormalBulk08.Dawn.Fern
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Lattice Dawn Set
open scoped BigOperators Topology ENNReal Classical ContDiff
variable {D k:ℕ} {L: Side}

def drag (D:ℕ)(i:Axis)(b:Bool)(r:ℝ):Garden D→ₗ[ℝ]Garden D where
   toFun:=useBasis i b r
   map_add' :=fun _ _=>rfl
   map_smul':=fun _ _=>rfl
lemma notch_linear (i:Axis)(b:Bool): ∃ A:Garden D→ₗ[ℝ] Garden D,∀ x,A x=notchM i b x:= by
   let u: Garden D→ₗ[ℝ]Garden D:= ∑ j,treks D j • drag D i b (taps D j); have hy (f:Garden D):rounds i b f=u f:= by unfold rounds u; rw [LinearMap.sum_apply];rfl
   refine ⟨{ toFun := notchM i b
             map_add':= ?_
             map_smul':= ?_ },fun _=>rfl ⟩
   · intro x y; apply Subtype.ext; ext1 w; change crack _ _ _ w=crack _ _ _ w+crack _ _ _ w; by_cases h:w∈nearM i b <;> simp only [crack,h,hy,map_add,↓reduceIte] <;> rfl
   intro c x; apply Subtype.ext; ext1 w; change crack _ _ _ w=c*crack _ _ _ w; by_cases h:w∈ nearM i b<;>simp only [crack,h,hy,map_smul,↓reduceIte] <;> rfl
lemma linear_reach (D:ℕ)(T:Finset Siteface) : ∃ B:ℝ,1≤B ∧ ∃ X: Garden D→ₗ[ℝ]Garden D,∀ f g:Garden D,∀ A:ℝ,0 ≤ A→Memos f g T A→ Memos f (X g) ∅ (B*A):= by
   induction T using Finset.induction_on with
   | empty=> exact ⟨1,le_rfl,LinearMap.id,fun _ _ _ _ h=>by simpa using h⟩
   | insert i T he ih=>
      obtain ⟨A,a,X,H⟩:=ih; obtain ⟨Y,Yt⟩:= notch_linear (D:=D) i.1 i.2; let K:ℝ:=1+∑ i,|treks D i|;have hx:1≤K:=le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=> abs_nonneg _);refine ⟨A*K,one_le_mul_of_one_le_of_one_le a hx,X∘ₗ Y,fun f g B b p=>?_⟩
      rw [LinearMap.comp_apply,Yt,mul_assoc]; exact H f _ _ (mul_nonneg (zero_le_one.trans hx) b) (memo_move i T f g B b p)
structure Pass (D:ℕ) (B:ℝ) (L:Studio D→ₗ[ℝ] Studio D): Prop where
    safe:1≤ B
    opake : ∀ x:Studio D,compress D (L x)=compress D x
    price: ∀ x:Studio D,‖L x‖≤ B*‖compress D x‖
lemma extension (D:ℕ): ∃ B:ℝ, ∃ L:Studio D→ₗ[ℝ]Studio D, Pass D B L:= by
   obtain ⟨B,b,L,H⟩:=linear_reach D Finset.univ; obtain ⟨R,h⟩:= (portrait D).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr (portrayed _)); have ht x:portrait D (R x)=x:= LinearMap.congr_fun h x
   let P:=(portrait D)∘ₗ L ∘ₗ R; have hz x:Memos (R x) (L (R x)) ∅ (B*‖compress D x‖):= by
       refine H (R x) (R x) _ (norm_nonneg _) ⟨fun i hi u=>?_,fun _ _ _=>rfl⟩; let z: Deck:=⟨i,hi⟩; have he : Dawn.halo (R x) u i=compress D x u z:= by nth_rw 2 [← ht x]; rfl
       rw [he]; exact (((compress D x) u).norm_coe_le_norm z).trans (norm_le_pi_norm ..)
   refine ⟨B,P,b,fun x=>?_,fun x=>panel_le _ (mul_nonneg (zero_le_one.trans b) (norm_nonneg _)) ?_⟩
   · ext1 u; ext1 z; nth_rw 2 [←ht x]; exact (hz x).meets _ z.property u
   intro i y; apply (hz x).pays y.val _ i; refine cloud_has.mpr ⟨fun k=>?_,by simp⟩; calc
       _≤‖y.val‖:=by simpa using abs_real_inner_le_norm (basis k) y.val
       _≤8:=still _
end YM.FormalBulk08.Annex
