import YM.MS.Menus.Glyph
import YM.MS.Lifting.Post
/-!
# Labels for the native prescription

One label per real homogeneous basis representative, of any physical rank. Extend
 to scales by applied adjustment `χ` fixed for all lists of insertions. Scheme-specific
 choices happen after calculating MS coefficients, never position-dependent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}(B: Deck G) {d r:ℕ}
-- pick any usable stencil dictionary. This is independent of positions. Could be more general than homogeneous levels
structure LitBook (B:Deck G) where
   stamp (u v:ℕ) (i:B.BIndex u v): Dot G Cover
   levels (u v:ℕ) (i): Aura (stamp u v i) v
   fit u v i: Fits (stamp u v i) (B.raw u v i) v u false
lemma existence : Nonempty (LitBook B):= by
   choose F hf h using fun (u v:ℕ) (i:B.BIndex u v)=> liftP (B.le (B.form u v i)); exact ⟨⟨F,hf,h⟩⟩

namespace Glyph
variable {B}
abbrev lit (V: LitBook B)(x: Glyph B d):= V.stamp x.size x.grade x.2.2
lemma memory (x:Glyph B d): x.grade ≤ d:= by have he:= x.2.1.isLt; have ht:=x.1.isLt; unfold grade; omega
-- after adopting new coupling g_*; in g_* after re-expression evaluate raw normalization including $g_*^{-r}$.

def preamble (V:LitBook B)(p:Team)(c:Glyph B d)(x:ℝ): T (Dot G Cover):= wobble G p x (Book.levels c.grade (V.stamp c.size c.grade c.2.2))
variable (V:LitBook B)(p:Team) (c:Glyph B d)
lemma pre_free (x:ℝ)(h:G.Simple): Weightless (Spectrum G) (style G p x) (preamble V p c x):= wob_weight p x ((V.levels ..).closed h)
lemma pre_c (x:ℝ)(k:ℕ): Tuned (preamble V p c x k) 0:= stood p x (fun j=> TuneModel (V.levels ..).phase (j+c.grade)) k
lemma pre_cost (x:ℝ)(k:ℕ): Limit (preamble V p c x k).val (k+c.grade):= inducedLimit (F:=Book.levels c.grade (lit V c)) (fun i hi=>Limit.up (Limit.mod _ ((i:ℤ)+(c.grade:ℤ))) (by omega)) k.le_refl
lemma pre_ready (k:ℕ): Ready (fun x:ℝ=> preamble V p c x k):= brief p (M:=fun _=>Book.levels c.grade (lit V c)) (r:=k) (q:=k+c.grade) (fun _ i hi=>Limit.up (Limit.mod _ ((i:ℤ)+(c.grade:ℤ))) (by omega)) (fun i=>Ready.const _)
lemma pre_lit (x:ℝ)(k:ℕ): Colorless (preamble V p c x k):= induced p x (fun i=>ColorMod (V.levels ..).lit (i+c.grade)) k
lemma mask_sq {A:Type}(i:ℤ)(F:Raw A ℂ): Book.mask i (Book.mask i F)=Book.mask i F:= by ext x; by_cases he:(x.length:ℤ)=i; exact enough x he ; rw [strange _ he,strange _ he]
lemma pre_floor (x:ℝ): Fits (preamble V p c x 0) c.read c.grade c.size false:= by
   unfold preamble Fits; rw [whoZero,Book.levels,Tone.grade, Nat.cast_zero, zero_add,mask_sq]; exact V.fit c.size c.grade c.2.2
end Glyph
end YM.MS.Menus
