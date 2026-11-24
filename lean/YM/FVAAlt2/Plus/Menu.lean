import YM.MS.Menus.Quantify
/-!
# Extension of native marked launch to nonhomogeneous slot cores.
The insertion of dimension d, rank r may include coordinated components with
OTHER slot numbers, including self-subtractions with lower horizon, off-shell
labels, at the SAME top stencil horizon. Therefore `Book.levels r F` is not enough!
In this module and `Plus.*` afterwards we extend the MS theorem conservatively:
SAME theorem and proof with WOBBLE of a series satisfying price/launch facts. All
low-level and continuum estimates are untouched. Each new `*Pl` theorem
closely adapts its original in `YM/MS` (see imports); when removed suffix the
file/name of its template should be easy to locate. Include minimal differences only.
No changes to definitions/proofs in supplied files.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Detect
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {B:Deck G} {d:ℕ}
structure MarkFull (F:T (Dot G Cover))(u:Law G)(w k:ℕ) : Prop where
    ono : Lifting.Fits (F 0) u k w false
    phase i : Tuned (F i) 0
    lit i : Colorless (F i)
    pay i : Book.Limit (F i).val ((i:ℤ)+(k:ℤ))
    law : G.Simple → Weightless (Spectrum G) (core G) F
structure RichBook (B:Deck G) where
    menu (d r:ℕ) (i:B.BIndex d r) : T (Dot G Cover)
    rich d r i : MarkFull (menu d r i) (B.raw d r i) d r

def extendMenu (P:LitBook B): RichBook B where
    menu d v i:= Book.levels v (P.stamp d v i)
    rich d v i:=by
       refine ⟨ ?_,fun j=>TuneModel (P.levels ..).phase (j+v), fun j=>ColorMod (P.levels ..).lit (j+v), fun i=> Limit.mod _ _,fun h=>(P.levels ..).closed h ⟩
       unfold Fits; rw [Book.levels,Tone.grade,Nat.cast_zero,zero_add,Glyph.mask_sq]; exact P.fit d v i

namespace Glyph
variable (V:RichBook B)(p:Team)(c:Glyph B d)
def preamblePl (x:ℝ): T (Dot G Cover):= wobble G p x (V.menu c.size c.grade c.2.2)

lemma pre_freePl (x:ℝ)(h:G.Simple): Weightless (Spectrum G) (style G p x) (preamblePl V p c x):= wob_weight p x ((V.rich ..).law h)
lemma pre_cPl (x:ℝ)(k:ℕ): Tuned (preamblePl V p c x k) 0:= stood p x (V.rich ..|>.phase) k
lemma pre_costPl (x:ℝ)(k:ℕ): Limit (preamblePl V p c x k).val ((k:ℤ)+c.grade):= inducedLimit (F:=V.menu c.size c.grade c.2.2) (fun i hi=> Limit.up ((V.rich ..).pay i) (by omega)) k.le_refl
lemma pre_readyPl (k:ℕ): Ready (fun x:ℝ=> preamblePl V p c x k):= brief p (M:=fun _=> V.menu c.size c.grade c.2.2) (r:=k) (q:=(k:ℤ)+c.grade) (fun _ i hi=>Limit.up ((V.rich ..).pay i) (by omega)) (fun i=>Ready.const _)
lemma pre_litPl (x:ℝ)(k:ℕ): Colorless (preamblePl V p c x k):= induced p x ((V.rich ..).lit) k
lemma pre_floorPl (x:ℝ): Fits (preamblePl V p c x 0) c.read c.grade c.size false:= by unfold preamblePl; rw [whoZero]; exact (V.rich ..).ono
end Glyph
end YM.MS.Menus
