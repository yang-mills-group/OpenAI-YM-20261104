import YM.OPE.Compatible.Lines.Scope
import YM.OPE.Compatible.Lines.Spokes
import Mathlib.Data.Fin.Tuple.Sort
/-!
# Grammar: affine motion words, no hidden constants. Leaves attached at centers with offsets outside scanned variables, permits multiply by probe readouts (use translations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary
open scoped Topology BigOperators Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)(Q:Finset X)
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
structure Atom (U:Spec.Final C F S)(X V:Type) where
   n:ℕ
   hang : Fin n→ X
   shift : V→ Fin n → E4
   p:Fin n→ C.book.Token
   r: V→ Viewers U
namespace Atom
variable (A:Atom U X V) (s:X→ℝ) (i:V)(x:X→ E4)
def pose (j:Fin A.n):E4:= x (A.hang j)+A.shift i j
def read :ℂ:= observe (spectator U (A.r i)) (A.pose i x) A.p
def weight (A:Atom U X V)(i:V) (x:X→E4)(u v:Fin A.n):E4:= A.pose i x u - A.pose i x v
-- texture conditions only those involving these words
structure Quota (A:Atom U X V)(D:Origin X)(Q:Finset X)(s:X→ℝ)(i:V)(x:X→E4)(η r:ℝ): Prop where
    split u v : u≠v→ r ≤ ‖A.weight i x u v‖
    pace u v : u≠v→∀ w:Wing D Q,flex D Q w (A.hang u) (A.hang v)→ η*s (par D w.1.1)≤ ‖A.weight i x u v‖
-- shades linear
lemma shade_sub (a:ℕ)(x y:E4) : shade a (x-y)=shade a x-shade a y:= by change time (Ortho.motion (polar a) (x-y))=_; rw [map_sub]; rfl
lemma shade_le (a:ℕ)(x:E4) : |shade a x| ≤ ‖x‖:=by
    let y:=polar a; show ‖Ortho.move y x timeAxis‖ ≤ _; exact (PiLp.norm_apply_le _ _).trans_eq ((Ortho.motion y).norm_map _)
-- select before step
structure Designed (A:Atom U X V) (i:V)(x:X→E4) (g:Sight)(c:ℝ) : Prop where
    cut u v : u≠v → ∀ j:Axis,c*‖A.weight i x u v‖ ≤ |shade (g.code j) (A.weight i x u v)|
omit [PartialOrder X] [OrderBot X] [Fintype X] in
lemma poised (a:ℕ): ∃ e:Equiv.Perm (Fin A.n), Monotone (shade a ∘ A.pose i x ∘ e):=by
    let z:=shade a ∘ A.pose i x; exact ⟨Tuple.sort z, Tuple.monotone_sort z⟩
-- prove tilt common over f (unpert base x); η atom margin may separate
variable {c η r ρ M:ℝ} (H:Crown Q)(h: Bright Q s)
include H h
lemma toned (A:Atom U X V)(g:Sight)(hx: A.Quota D Q s i x η r)(hg:Designed A i x g c)(he:0<η)
    (hρ:0 ≤ ρ)(hf:0<c)(_hr:0<r)(hM:∀ j:Axis,‖FrameRead.trail (g.code j)‖ ≤ M)(hm:0 ≤ M) (hp:(Fintype.card (Wing D Q):ℝ)*(M*ρ) ≤ c/2 * η)(j:Axis) :
   ∃ e:Equiv.Perm (Fin A.n),∀ f:Wing D Q→ℝ,(∀ i, |f i|≤ρ) → broad (shade (g.code j) ∘ A.pose i (reload D Q s g x f) ∘ e) (c*r/2):=by
    obtain ⟨e,ht⟩:= poised A i x (g.code j)
    refine ⟨e,fun f hz u v hw=>?_⟩; let B (u:Fin A.n):= A.pose i (reload D Q s g x f) (e u); let z:=A.weight i x (e v) (e u); let d:= displacement D Q s g f (A.hang (e v))-displacement D Q s g f (A.hang (e u)); have he':e v≠e u:= (e.injective.ne (ne_of_gt hw)); have hg:= hg.cut (e v) (e u) he' j
    rw [weight,shade_sub,abs_of_nonneg (sub_nonneg.mpr (show FrameRead.shade (g.code j) (A.pose i x (e u)) ≤ FrameRead.shade (g.code j) (A.pose i x (e v)) from ht hw.le)),← shade_sub] at hg -- second may hits norm diff?
    have hA:B v-B u=z+d:=by unfold B z weight pose reload d; abel
    have hd: ‖d‖ ≤ c/2*‖z‖:=by
       have hv0:∀ (w:Wing D Q), flex D Q w (A.hang (e v)) (A.hang (e u))→s (par D w.fst.val)≤‖z‖/η:=fun w h=> (le_div_iff₀ he).2 (by simpa only [mul_comm η] using hx.pace _ _ he' w h)
       exact (shift_budget D (fun i=> (dim_order D H h i).le) hz hρ hM hm (by positivity) hv0).trans ((mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ) ≤ ‖z‖/η)).trans_eq (by field_simp))
    have hi: r ≤ ‖z‖:= hx.split _ _ he'; have hv': shade (g.code j) (B v-B u)=shade (g.code j) z+shade (g.code j) d:=by
       rw [hA]; change time (Ortho.motion (polar (g.code j)) (z+d))=_; rw [map_add]; rfl
    have hl:=abs_le.mp (le_trans (shade_le (g.code j) d) hd); change c* ‖z‖ ≤ shade _ z at hg; change _ ≤ shade _ (B v)-shade _ (B u); rw [← shade_sub,hv']; nlinarith only [mul_le_mul_of_nonneg_left hi hf.le,hg,hl.1]
end Atom
end YM.OPE.Arboreal.Trace
