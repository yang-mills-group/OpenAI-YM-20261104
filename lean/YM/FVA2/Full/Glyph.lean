import YangMills.WilsonProof.NativeSupport.YM.MS.Menus.Glyph
import YM.MS.Menus.Bulk
/-!
# MS.Mark with allowed internal shifts (in particular the W for B^a's)

`YM.MS.Menus.LitBook` is for a single pure-rank stamp per field.
`FullBook` still uses those very fields, but before any field-frame matrix it attaches
finitely many lower-slot-rank shifts.
It doesn't try to characterize the largest class of such additions. The payoff is we'll
get **exactly the same** physical columns as in the X-space scheme, so position normalization
can be done at regulator, not after a possibly singular-in-spacing conversion back to the
pure stamps. New names in same namespaces drop into the existing Estimate & Toll engines.
No existing declaration modified.

Indexing by *slot* Laurent shifts, still all g orders; the general bound below suffices for
the comparison here (extending the supplied one), and in our application we
additionally implement with parity (see `Parity/Kit` and `Inked/Combined`).
Reminder: a lower slot count corresponds to a higher power in the bare column expansion, but after the
shared connection Taylor counting it still starts at g^0 in this mark convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G} {d r:ℕ}
/-- `frost` contains the shifts; index j.2 indexes slot counts of the attached
pieces. One example (used in our comparison): `YM.FVA2.Press.wickInput`. -/
structure FullBook (B:Deck G) extends LitBook B where
   frost (u v:ℕ) (i:B.BIndex u v) (j:Fin (u+1) × Fin v): Dot G Cover
   prepares (u v:ℕ) (i j): Aura (frost u v i j) j.2.val

namespace Glyph
variable (V:FullBook B)(p:Team)(c:Glyph B d)
abbrev Bundle (c:Glyph B d):= Unit ⊕ Fin (c.size+1) × Fin c.grade
def hand (j: Bundle c): Dot G Cover:= j.elim (fun _=> c.lit V.toLitBook) (V.frost c.size c.grade c.2.2)
def tally (j:Bundle c): ℕ:= j.elim (fun _=> c.grade) (fun i=> i.2.val)
def gallery : T (Dot G Cover):= ∑ j:Bundle c, Book.levels (tally c j) (hand V c j)
lemma gallery_floor (j:Bundle c): tally c j ≤ c.grade:= by cases j with| inl u=>exact le_rfl| inr r=> exact r.2.isLt.le
lemma galleryReady (j:Bundle c): Aura (hand V c j) (tally c j):= by cases j with| inl u=> exact V.levels ..| inr r=> exact V.prepares ..

def preambleF (x:ℝ) := (wobble G p x) (gallery V c)
lemma pre_listing (x:ℝ): preambleF V p c x= ∑ j: Bundle c, wobble G p x (Book.levels (tally c j) (hand V c j)):= map_sum ..
lemma pre_listing_coeff (x:ℝ) (k:ℕ): preambleF V p c x k= ∑ j: Bundle c, wobble G p x (Book.levels (tally c j) (hand V c j)) k:= by rw [pre_listing,Finset.sum_apply]
lemma pre_freeF (x:ℝ)(h:G.Simple): Weightless (Spectrum G) (style G p x) (preambleF V p c x):= by
   rw [pre_listing]; let Q:= actB (Spectrum G) + pairW (Spectrum G).touch ( style G p x ); change Q _=0; rw [map_sum]; exact Finset.sum_eq_zero fun j _=> wob_weight p x ( (galleryReady V c j).closed h )
lemma pre_cF (x:ℝ)(k:ℕ): Tuned (preambleF V p c x k) 0:= by rw [pre_listing_coeff]; exact Tune.sum _ fun j _=> stood p x (fun i=> TuneModel (galleryReady V c j).phase (i+(tally c j:ℤ))) k
lemma offer_cost (x:ℝ)(j: Bundle c)(k:ℕ): Limit (wobble G p x (Book.levels (tally c j) (hand V c j)) k).val (k+tally c j):= inducedLimit (F:= Book.levels (tally c j) (hand V c j)) (fun i hi=>Limit.up (Limit.mod _ ((i:ℤ)+(tally c j:ℤ))) (by omega)) k.le_refl
lemma pre_costF (x:ℝ)(k:ℕ): Limit (preambleF V p c x k).val (k+c.grade):= by rw [pre_listing_coeff,sum_stack]; exact Limit.sum _ fun j _=> (offer_cost V p c x j k).up (by obtain he:= gallery_floor c j; omega)
lemma pre_readyF (k:ℕ): Ready (fun x:ℝ=> preambleF V p c x k):= by
    simp_rw [pre_listing_coeff]; refine value_sum _ (fun j _=>?_); exact brief p (M:=fun _=>Book.levels (tally c j) (hand V c j)) (r:=k) (q:=(k:ℤ)+(tally c j:ℤ)) (fun _ i hi=>Limit.up (Limit.mod _ ((i:ℤ)+(tally c j:ℤ))) (by omega)) (fun i=>Ready.const _)
lemma pre_litF (x:ℝ)(k:ℕ): Colorless (preambleF V p c x k):= by rw [pre_listing_coeff]; exact Colorless.csum _ fun j _=> induced p x (fun i=> ColorMod (galleryReady V c j).lit (i+(tally c j:ℤ))) k
lemma pre_floorF (x:ℝ): Fits (preambleF V p c x 0) c.read c.grade c.size false:= by
   let f:= fun j:Fin (c.size+1) × Fin c.grade=> wobble G p x (Book.levels (tally c (Sum.inr j)) (hand V c (Sum.inr j))) 0; let Z:= ∑ j, f j; have he : preambleF V p c x 0 = preamble V.toLitBook p c x 0 + Z:= by rw [ pre_listing_coeff,Fintype.sum_sum_type, Fintype.sum_unique ]; rfl
   rw [he]; suffices hv:Fits Z 0 c.grade c.size false from by rw [← add_zero c.read]; exact (pre_floor V.toLitBook p c x).add hv
   have ht : Limit Z.val ((c.grade:ℤ)-1):= by unfold Z; rw [sum_stack]; refine Limit.sum _ (fun j _=> (offer_cost V p c x (Sum.inr j) 0).up ?_); obtain he:= j.2.isLt; rw [show tally c (Sum.inr j)= j.2.val from rfl]; omega
   unfold Fits; rw [maskOff (u:= (c.grade:ℤ)-1) (by omega) (Tone.oneRank ht)]; exact face_zero _
end Glyph
end YM.MS.Menus
