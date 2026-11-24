import YM.RG3.Script.Facade
import YM.RG3.Primary.Claim

/-!
# Simultaneous canonical extraction on every singleton ray

Frame/horizon chosen per mark, use SAME primary prescription and quote
atomPrice/reset & support cost separately before fusion. Don't try to read
a physical canonical coordinate off a deck where another's projection
terms have just been removed! No meaning of multicover evaluation beyond
actual source germs on the priced `presented` stencils already fitted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {V : Type} [DecidableEq V] {R:Census V} {ζ : V→Site n} {G : Gauge}
variable {e : Edition ζ R G} {P : Rep G n}
variable {D:V→ℕ} (H : Hol G) {X : (s:V)→Labels.Frame G (D s)} (L:(s:V)→ SectionData (X s)) (d:Deck R P)

namespace Edition
def only (i : ℕ)(s : V): Prop:= e.pins i=R.fire s
instance (i:ℕ)(s:V): Decidable (only (e:=e) i s) := inferInstanceAs (Decidable (_=_))
lemma single_unique (i:ℕ){u v:V}(hu:only (e:=e) i u)(hv:only (e:=e) i v):u=v := singleton_inj.mp (congrArg Subtype.val (hu.symm.trans hv))

section one
variable (e) {d}
def shaft (i:ℕ):Option V := if h:∃s,only (e:=e) i s then some h.choose else none
@[simp] lemma shaft_only {i:ℕ}{s:V}(h:only (e:=e) i s):e.shaft i=some s:=by
  unfold shaft; split
  next he=> exact congr_arg _ (single_unique i he.choose_spec h)
  next he=> exfalso; exact he ⟨_,h⟩
lemma from_shaft {i:ℕ}{s:V}(h:e.shaft i=some s):only (e:=e) i s :=by
  unfold shaft at h; split at h
  next he=> exact Option.some.inj h ▸ he.choose_spec
  contradiction
lemma nobody {i:ℕ}(h:e.shaft i=none):∀ s,¬only (e:=e) i s:=fun s he=>by have hv := e.shaft_only he; simp [h] at hv
end one

section book
variable (e)
private abbrev d0 := e.scribe d
def petition (s : V): (X s).Coeff:=Primary.comp s (d0 e d) H (X s)
def dew (s:V)(i:ℕ) := Primary.fires s (d0 e d) H (L s) i
def veil (s:V)(i:ℕ) := Primary.grows s (d0 e d) (L s) i
def tent (i:ℕ):Support n := (e.shaft i).elim (e.home i) (fun s=>veil e L d s i)
def display (i:ℕ): Config G n→ℂ:=(e.shaft i).elim (e.song i) (fun s=> dew e H L d s i)

variable [Fintype V] [Nonempty V]
/-- Reserve leading registers (one per primary), keep all old rows disjoint
on another definal subset of the ℕ addressing. Importantly .home may use
origin s different from comparison edit anchor carrying larger path roots.
-/
def shuffle {α: Type*}(f:V→α)(g:ℕ→α):ℕ→α:= Sum.elim f g ∘ numbering (V⊕ℕ)

def sprayed : Edition ζ R G where
  pure i:=e.pure i+petition (X:=X) e H d i 0
  pins := shuffle (fun i:V=>R.fire i) e.pins
  home := shuffle (fun i:V=> (L i).footprint (ζ i)) (tent e L d)
  song := shuffle (fun i:V=> Primary.signal i (d0 e d) H (L i)) (display e H L d)
  footer:= e.footer

omit [DecidableEq V] [Nonempty V] in
lemma revive {α : Type*}{i : ℕ} {x : V}(h:numbering (V⊕ℕ) i=Sum.inl x) (f:V→α)(g:ℕ→α) : shuffle f g i=f x:= by simp [shuffle,h]
omit [Nonempty V]  [DecidableEq V] in
lemma corsage {α : Type*}{i j : ℕ}(h:numbering (V⊕ℕ) i=Sum.inr (α:=V) j)(f:V→α)(g:ℕ→α) : shuffle f g i=g j:= by simp [shuffle,h]

end book

section foliage
variable {L d} {k : V→ℝ}
lemma blossom {i:ℕ}{s:V}(hs : e.shaft i=some s) :
    tent e L d i=Primary.grows s (d0 e d) (L s) i ∧ display e H L d i=Primary.fires s (d0 e d) H (L s) i:=by
  rw [tent,display,hs];exact ⟨rfl,rfl⟩
lemma grass {i:ℕ}(hs : e.shaft i=none) :
    tent e L d i=e.home i ∧ display e H L d i=e.song i:=by rw [tent,display,hs];exact ⟨rfl,rfl⟩

variable [Fintype V] [Nonempty V] (hr: ∀ s, Readable H (L s) P.p n (k s)) (hz:d.contents.origins=ζ) (he:d.Active)(h:e.Principle P.p)
include hr hz he h
omit [Nonempty V] in
lemma primed : (sprayed e H L d).Principle P.p:= by
  have ha:= authorized hz h he
  have hs s:= Primary.colored s (d0 e d) H (L s) (hr s) ha
  let o:= sprayed e H L d
  have hi i : (o.pins i).val.Nonempty ∧ (∀ j∈ (o.pins i).val, ζ j∈o.home i) ∧ P.p.Regular (o.home i) (o.song i):=by
    cases hy:numbering (V⊕ℕ) i with
    | inl j=>
      simp only [o,sprayed,shuffle,Function.comp_apply,hy,Sum.elim_inl]
      exact ⟨singleton_nonempty _,(hs j).home 0,(hs j).regular 0⟩
    | inr j=>
      simp only [o,sprayed,shuffle,Function.comp_apply,hy,Sum.elim_inr]
      cases hh:e.shaft j with
      | none=> rw [(grass H hh (L:=L) (d:=d)).1,(grass H hh).2]; exact ⟨h.hot _,h.rem _,h.reg _⟩
      | some s=> rw [(blossom H hh (L:=L) (d:=d)).1,(blossom H hh).2]; exact ⟨h.hot _,(hs s).home (j+1),(hs s).regular (j+1)⟩
  exact ⟨fun i=>(hi i).1,fun i=>(hi i).2.1,fun i=>(hi i).2.2,h.vertical⟩

-- Raw projection receipt. +2 support exponent from merger/rooted applied
-- BEFORE integration, not a claim that accessible P provides this at same
-- price. For both price and fusion & proportional inputs at θ marker disk.
variable {w:V→ℝ}
variable (a : ℝ) (m : ℕ→ℝ) (δ:ℝ)
def paidR (L:(s:V)→ SectionData (X s))(d : Deck R P)(e:Edition ζ R G) (k : V→ℝ) (s:V)(i:ℕ):=
    expense P.p.B a (Primary.stem s (d0 e d) (L s) i) (Primary.ink (F:=X s) s (d0 e d) H (k s) m i)
def Loaded (L:(s:V)→ SectionData (X s))(d:Deck R P)(e:Edition ζ R G)(k w:V→ℝ):Prop:=
    (∀ s i,e.only i s → P.p.supBounds (ζ s) (e.home i) (e.song i) (m i)) ∧
    ∀ s, SumBudget (fun i=>w s * paidR H a m L d e k s i) δ
variable {H a m δ}(hl:Loaded H a m δ L d e k w)(hw:∀i,0<w i)
-- avoid shadow context
include hl hw
omit [Nonempty V] [Fintype V] hz he h in
lemma demand (ha:P.p.supportExponent+1 ≤ a)(s:V): StemPay s (d0 e d) H (L s) (k s) w m δ:= by
  refine ⟨hl.1 s,budget_mono (hl.2 s) (fun i=>?_) (fun i=>?_)⟩
  · unfold gross ink; split
    next hh => exact mul_nonneg (hw s).le (mul_nonneg (Real.exp_pos _).le (mul_nonneg (zero_le_one.trans (atomPrice_ge_one H (X s) (hr s).nonneg)) ((hl.1 s i hh).1)))
    simp
  unfold paidR expense gross; apply mul_le_mul_of_nonneg_left _ (hw s).le
  rcases eq_or_ne (e.pins i) (R.fire s) with h|h
  · apply mul_le_mul_of_nonneg_right (Real.exp_monotone (by gcongr))
    rw [Primary.ink,if_pos (show Primary.earns s (d0 e d) i from h)]
    exact mul_nonneg (zero_le_one.trans (atomPrice_ge_one H (X s) (hr s).nonneg)) (hl.1 s i h).1
  unfold Primary.ink; rw [if_neg (show ¬Primary.earns s (d0 e d) i from h)]; simp
end foliage
end Edition
end YM.RG3.Script
