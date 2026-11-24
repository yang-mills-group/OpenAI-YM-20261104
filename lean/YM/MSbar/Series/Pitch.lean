import YM.MSbar.Series.Prim
import Mathlib.Order.Filter.AtTopBot.Basic
/-! Pointwise interpolation of jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Set Finset Filter
open scoped BigOperators Classical
variable {X Y Z : Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z] {f h g: Form X} {F G:ℂ→X} {i j n:ℕ}
-- delay A
abbrev post (h:Bool)(A:X→ₗ[ℂ]Y):Form X→ₗ[ℂ] Form Y:= if h then sea A else act A
lemma post_prior (s:Bool) (A:X→ₗ[ℂ]Y) (h: Prior n f g): Prior n (post s A f) (post s A g):= by cases s <;> first | exact Prior.move h A | exact Prior.restrict (Prior.flow h A) (Nat.le_succ n) -- maybe if definitional

def Pitch (n:ℕ)(f:Form X)(F:ℂ→X): Prop := ∃ g:Form X, Prior n f g ∧ ∀ᶠ i:ℕ in atTop, Cap i g ∧ ∀ c:ℂ, leaf i c g=F c
lemma Pitch.of {g:Form X} (h:Cap i g)(hp: Prior n f g)(hf:∀ c:ℂ, leaf i c g=F c): Pitch n f F:= by
    refine ⟨g,hp,?_⟩; filter_upwards [eventually_ge_atTop i] with n hn; exact ⟨Cap.carry h hn,fun t=> (leaflet h hn).symm.trans (hf t)⟩
def ish (n:ℕ)(f:Form X)(c:ℂ):= leaf n c (chill n f)
namespace Pitch
lemma ish_pitch (i:ℕ)(f : Form X): Pitch i f (ish i f):= of (still i f) (Prior.symm (just i f)) fun c=> rfl
lemma eq (h:Pitch i f F)(h':Pitch i g G)(fQ:∀ c,F c=G c): f i=g i:= by
    obtain ⟨l,hl,H⟩:=h;obtain ⟨b,hb,E⟩:=h'; obtain ⟨j,⟨hf,hh⟩,hk,he⟩ := (H.and E).exists; exact (Prior.value hl).trans ((congr_fun (direct hf hk (fun z=> by rw [hh,he,fQ])) i).trans (Prior.value hb).symm)
lemma add (a:Pitch i f F)(b:Pitch i g G):Pitch i (f+g) (F+G):=by
    obtain ⟨u,hu,h⟩:=a; obtain ⟨v,hv,H⟩:=b; refine ⟨_,Prior.adding hu hv,?_⟩; filter_upwards [h,H] with j h H; exact ⟨Cap.add h.1 H.1, fun c=> by simp [h.2 c,H.2 c]⟩
lemma scale (a:Pitch i f F)(c:ℂ):Pitch i (c•f) (fun t=>c • F t) := by
    obtain ⟨u,hu,h⟩:=a; refine ⟨_,Prior.scaling hu c,?_⟩; filter_upwards [h] with j h; exact ⟨Cap.scale h.1 _, fun c=> by simp [h.2 c]⟩
lemma post (h:Pitch i f F)(s:Bool)(A:X→ₗ[ℂ] Y): Pitch i (Category.post s A f) (fun c:ℂ=>(if s then c else 1) • A (F c)):=by
    obtain ⟨g,hg,H⟩:=h; obtain ⟨j,hj,hh⟩:=H.exists; refine Pitch.of (i:=j+1) ?_ (post_prior s A hg) ?_
    · cases s; exact Cap.carry (Cap.move hj A) (Nat.le_succ _); exact Cap.step hj A
    intro c; unfold Category.post; split_ifs; rw [leaf_sea,hh]; rw [leaf_act,← leaflet hj (Nat.le_succ _),hh,one_smul]
lemma points (h:Pitch i f F)(A:X→ₗ[ℂ]Y):Pitch i (act A f) (fun c=> A (F c)):= by simpa only [Category.post,Bool.false_eq_true,↓reduceIte,one_smul] using h.post false A
lemma knot (h:Pitch i f F){g:Form Y}{G:ℂ→Y}(b:Pitch i g G)(B:X→ₗ[ℂ] Y→ₗ[ℂ] Z): Pitch i (Category.knot B f g) (fun c=> B (F c) (G c)):=by
    obtain ⟨u,hu,H⟩:=h; obtain ⟨v,hv,L⟩:=b; obtain ⟨j,hj,hh⟩:=H.exists; obtain ⟨k,hk,hb⟩:=L.exists; exact Pitch.of (Cap.spin hj hk B) (Prior.glue hu hv B) (fun c=> by rw [leaf_knots _ le_rfl hj hk,← leaflet hj (by omega),← leaflet hk (by omega),hh,hb])
end Pitch
end YM.MSbar.Category
