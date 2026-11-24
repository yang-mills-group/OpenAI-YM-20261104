import YM.RG11Proof.Rigidity.Loom
import YM.RG11Proof.Rigidity.Fare

/-!
# Attach arbitrary on-shell requests by separate variation
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd Function Submodule
open scoped BigOperators Classical

variable {G : Gauge}

abbrev Bristle (G : Gauge) := G.ColorIndex → Pig G → ℝ

/-- Pair and panel exchange. -/
lemma stains_perm (W : Crowd G) (p : List (Spindle G)) (a b : Bristle G) : stainL W ((a,b)::p)=stainL W ((b,a)::p) := by
  unfold stainL; rw [palette.cons,palette.cons]; refine Finset.sum_congr rfl fun i _=> ?_
  congr 1; funext r; congr 1; ext1 l
  exact stitch_perm (List.Perm.swap ..) _
lemma chairs (W : Crowd G) {l t : List (Spindle G)} (h : List.Perm l t) : stainL W l=stainL W t := by
  let x : List (Pig G → ℝ)→ℝ := fun p=>W.asks (stitch p)
  change palette l x=palette t x
  have he : (byColor (C:=G.ColorIndex) (A:=Roll (G:=G)) id)=(id : Spindle G→Spindle G):=rfl
  simpa [deck,he] using deck_perm (C:=G.ColorIndex) (Q:=Bristle G) (hit:=id) x (fun {l r} ht=>by unfold x; refine congr_arg _ ?_; exact funext (fun _=> stitch_perm ht _)) h

lemma stains_add (W : Crowd G) (p : List (Spindle G)) (f g b : Bristle G) :
    stainL W ((f+g,b)::p)=stainL W ((f,b)::p)+stainL W ((g,b)::p) := by
  unfold stainL; simp_rw [palette.cons]; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
  rw [← palette.add]; congr 1; funext r
  rw [← ask_add]; apply congr_arg W.asks; ext1 L
  unfold stitch; simp_rw [Pi.add_apply,add_mul,pulls_add]
lemma stains_scale (W : Crowd G) (p : List (Spindle G)) (f b : Bristle G) (c : ℝ) :
    stainL W ((c • f,b)::p)=c*stainL W ((f,b)::p) := by
  unfold stainL; simp_rw [palette.cons]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  rw [← palette.mul]; congr 1; funext r
  rw [← ask_mul]; apply congr_arg W.asks; ext1 L
  unfold stitch; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc,pulls_mul]

/-- Matrices read by this functional are evaluated only on this fixed support
(before calibration and after it). -/
lemma stains_quote (W : Crowd G) (p : List (Spindle G)) (f g b : Bristle G)
    (hW : ∀ w∈W,∀ a∈w.2, ∀ d:G.ColorIndex, f d a=g d a) :
    stainL W ((f,b)::p)=stainL W ((g,b)::p) := by
  unfold stainL; rw [palette.cons,palette.cons]; apply Finset.sum_congr rfl; intro i _
  congr 1; funext L
  unfold asks
  congr 1; apply List.map_inj_left.mpr; intro a ha
  dsimp only; rw [stitch,stitch]; congr 1; apply pulls_congr; intro j
  rw [hW a ha _ (List.get_mem ..) i]

structure Prayer where
  x : E4
  k : ℕ
  mode : Sheet k

def hears (a : Prayer) : Bristle G := fun d p=> cabin d a.x a.k (fun q=>q a.mode) p

def clip (T : Finset (Pig G)) : (Canal T) →ₗ[ℝ] (Bristle G) where
  toFun f i a:= if h : a∈ T then f i ⟨_,h⟩ else 0
  map_add' f g:= by ext1 d; funext i; simp only [Pi.add_apply]; split_ifs with ht; rfl; exact (add_zero 0).symm
  map_smul' c f:= by ext1 d; funext i; simp only [Pi.smul_apply]; split_ifs with ht; rfl; exact (smul_zero _).symm

lemma first_fixed (c : G.ColorIndex) (U : Finset E4) (W : Crowd G) (p : List (Spindle G)) (f : Bristle G)
    (h : ∀ v y,y∉U → stainL W (((line ∘ toss v y),f)::p)=0) (a : Prayer) : stainL W ((hears a,f)::p)=0 := by
  classical
  let T:= (W.flatMap fun t=>t.2).toFinset
  have hk (w) (hw : w ∈ W) (i : Pig G) (hi : i∈w.2) : i∈T := List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨_,hw,hi⟩)
  let C : Canal T→ₗ[ℝ] ℝ:=
    ({ toFun u := stainL W ((u,f)::p)
       map_add' u v:= stains_add W p _ _ _
       map_smul' z u := stains_scale W p _ _ z } : Bristle G→ₗ[ℝ] ℝ).comp (clip T)
  have ht : seaside T U≤ LinearMap.ker C := by
    rw [seaside,span_le]; rintro u ⟨v,y,hy,rfl⟩
    refine Eq.trans (stains_quote W p (clip T (current T v y)) (line ∘ toss v y) f ?_) (h _ _ hy)
    intro w hw i hi d; change (if h : i ∈ T then _ else _) = _; rw [dif_pos (hk w hw i hi)]; rfl
  have he := ht (cabin_span T c U a.x a.k a.mode)
  apply Eq.trans _ (LinearMap.mem_ker.mp he)
  refine stains_quote W p (hears a) _ f (fun w hw i hi d=> ?_)
  change _=(if h:i∈T then _ else _); rw [dif_pos (hk w hw i hi)]; rfl

end YM.RG11.Rigidity
