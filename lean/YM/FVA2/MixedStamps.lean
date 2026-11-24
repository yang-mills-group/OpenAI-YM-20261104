import YM.MS.Wind.MatchM
import YangMills.WilsonProof.NativeSupport.YM.MS.Menus.Glyph
/-!
# Extending the high and low RG proofs to the **same** top stencils.

 A peculiarity of using the holographic/SectionData stencil : top Wick self contractions,
 even at coupling order zero, do NOT combine only ON-shell bare representatives. Do not
 simulate that change by readjusting the values of `fees` in the existing comparison.
 Those off-shell stencils & their link rank and a^-h factors matter. Nor change the top
 projection/graphs to avoid this issue. Generalize the UV symbols `Glyph.preamble`
 to prespecified (not retuned every order) series. Retain all real logs/dimension choices
 elsewhere. All container/flow changes here are mere re-binding of theorems polymorphic
 over stencil certificates. NO CHANGES required to PhysicalSum, Recount, or to any integration,
 estimates or master equation proofs across orders. `BookM`, `TaylorMixedOK`
 are for the contract reused below; construct the actual witnesses separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {B: Deck G} {d r:ℕ}
structure BookM (B: Deck G) where
   inkM (u v:ℕ) (i:B.BIndex u v): T (Dot G Cover)
   boundM u v i (k:ℕ) : Limit (inkM u v i k).val (k+(v:ℤ))
   tuneM u v i k : Tuned (inkM u v i k) 0
   lightM u v i k: Colorless (inkM u v i k)
   weightM u v i : G.Simple→ Weightless (Spectrum G) (core G) (inkM u v i)
   fitM u v i: Fits (inkM u v i 0) (B.raw u v i) v u false
namespace Glyph
variable (V:BookM B)(p:Team) (c:Glyph B d)
def preambleM (x:ℝ): T (Dot G Cover):= wobble G p x (V.inkM c.size c.grade c.2.2)
lemma pre_freeM (x:ℝ)(h:G.Simple): Weightless (Spectrum G) (style G p x) (preambleM V p c x):= wob_weight p x (V.weightM _ _ _ h)
lemma pre_cM (x:ℝ)(k:ℕ): Tuned (preambleM V p c x k) 0:= stood p x (V.tuneM c.size c.grade c.2.2) k
lemma pre_costM (x:ℝ)(k:ℕ): Limit (preambleM V p c x k).val (k+(c.grade:ℤ)):= inducedLimit (F:= V.inkM c.size c.grade c.2.2 ) (fun i hi=> (V.boundM c.size c.grade c.2.2 i).up (by omega)) k.le_refl
lemma pre_readyM (k:ℕ): Ready (fun x:ℝ=> preambleM V p c x k):= brief p (M:=fun _=> V.inkM c.size c.grade c.2.2 ) (r:=k) (q:=k+c.grade) (fun _ i hi=>(V.boundM c.size c.grade c.2.2 i).up (by omega)) (fun i=>Ready.const _)
lemma pre_litM (x:ℝ)(k:ℕ): Colorless (preambleM V p c x k):= induced p x (V.lightM c.size c.grade c.2.2) k
lemma pre_floorM (x:ℝ): Fits (preambleM V p c x 0) c.read c.grade c.size false:= by unfold preambleM; rw [ whoZero ]; exact V.fitM _ _ _
end Glyph
end YM.MS.Menus
