import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern

/-!
# Taylor expansion *inside* an integrated log molecule: insertion calculus

The insertion calculus uses the exact Cash representation with every mask,
retaining the common geometry, schedule, conditional
measures and tag/reset data. Integrands here (unmasked regular E6 convention)
are for `brush` estimates. In particular:

* No arbitrary substitutions in the RG transfer identity! We'll use these
  factors in estimating expansions of the known inputs to that identity.
* Locality even with the Gaussian marginal and its active links, and
  neighborhood measurability/regularity, are nontrivial, not to be inferred
  from costed estimates at just the completely healthy configuration.
* Aim for the real-output derivative prices in the original norms, no
  mask derivatives. `Zest` in the license is qualitative. We'll prove the
  quantitative estimates at eligible (actual) fields separately.

This factors/generalizes parts of CONNECTED_ACTIVITY_JETS_E6 (especially
`Polar.ember`, `Shield.bars`, `FlareW` and the `Captain.sextant` proof), so
we can Taylor expand the exponential *within* each member and prove estimates
including coincidence, not only take tails in the number of Heads. It should
also be useful for fluctuation-field expansions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

/-- A real integrand evaluated for one shared forest, sector/banner/tag,
field, and Gaussian vector. Typically a product of inserted exponential
moments. Keeps the original path space and masks. -/
structure Insert (T : Tube G S) where
  value : ∀ {F : Forest S.ratio}, Coat T F → Air f G → ℝ

namespace Insert

def ofConst (w : ℝ) : Insert T := ⟨fun {_} _ _ => w⟩

def mapSmooth (g : ℝ → ℝ) (f : Insert T) : Insert T :=
  ⟨fun {_} X z => g (f.value X z)⟩

def nextTo (g f : Insert T) : Insert T := ⟨fun {_} X z => g.value X z * f.value X z⟩

def joined {ι : Type*} (s : Finset ι) (u : ι → Insert T) : Insert T where
  value X z := ∏ i∈ s, (u i).value X z

def together {ι : Type*} (s : Finset ι) (u : ι → Insert T) : Insert T where
  value X z := ∑ i∈ s, (u i).value X z

/-- Composition with `course` at the moving field, retaining the true
physical fine configuration of `wrapY`. -/
def tracking (r : Insert T) (A β : ℝ) (X : Coat T F) {E : Type} (V : E → Config G c)
    (t : F.Slice G × Air f G) (i : E) : ℝ :=
  let X' := X.wrapY t.1
  r.value (vary X' (V i)) (course X' A β t.2 (V i))

end Insert

/-- Qualitative regular-log probe discipline in the priced Cash geometry.
No integral bound (even off the mask). Locality uses an empty coverage slot in
`Borough` because the two points use the same inventory parameters. Individual
kernels with other but **fixed** inventory data still have to prove locality. -/
structure Fits (H : Cash W s μ L Q o C T R) (r : Insert T) (Y : Support c) (j : ℕ) : Prop where
  regional {F : Forest S.ratio} (X X' : Coat T F) : X.x = s → X.width = o.K →
    ∀ (Y' : Support c) (z z' : Air f G), Y ⊆ Y' → Borough X X' Y' z z' ∅ ∅ R → r.value X z = r.value X' z'
  along {F : Forest S.ratio} (X : Coat T F) : X.x = s → X.width = o.K →
    ∀ (E : Type) [MeasurableSpace E] {V : E → Config G c} {Z : E → F.Slice G} {z : E → Air f G},
      Measurable V → Measurable Z → Measurable z → Measurable fun i => r.value (drive X (V i) (Z i)) (z i)
  onGauge {F : Forest S.ratio} (X : Coat T F) : X.x = s → X.width = o.K → Hue X →
    ∀ z w, r.value (sluice X z) (weep X z w) = r.value X w
  near {F : Forest S.ratio} (X : Coat T F) : X.x = s → X.width = o.K → X.manifest →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (V : E → Config G c) (x : E) {A b : ℝ}, Canary G A b →
      8 * o.a * Pressure.fiery G s L ≤ A/2 → Glass P X V x j W →
      Zest (r.tracking A R.beta X V) x j

namespace Fits
variable {r t : Insert T} {u : Support c}

lemma bigger (h : Fits H r u j) {w : Support c} (hw : u ⊆ w) : Fits H r w j :=
  ⟨fun X X' hX hx Y z z' hy => h.regional X X' hX hx Y z z' (Finset.Subset.trans hw hy),
    h.along,h.onGauge,h.near⟩

lemma ofConst (w : ℝ) : Fits H (Insert.ofConst w) u j :=
  { regional := fun _ _ _ _ _ _ _ _ _ => rfl
    along := fun _ _ _ _ _ _ _ _ _ _ _ => measurable_const
    onGauge := fun _ _ _ _ _ _ => rfl
    near := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Zest.still _ }

lemma mapSmooth (h : Fits H r u j) {g : ℝ → ℝ} (hg : ContDiff ℝ (↑j) g) :
    Fits H (r.mapSmooth g) u j := by
  constructor
  · intro F X X' hX hK Y z z' hh hB; exact congr_arg g (h.regional X X' hX hK Y z z' hh hB)
  · intro F X hX hK E _ V Z z hV hZ hz; exact hg.continuous.measurable.comp (h.along X hX hK E hV hZ hz)
  · intro F X hX hK hh z w; exact congr_arg g (h.onGauge X hX hK hh z w)
  intro F X hX hK hh E _ _ _ V x A b hA ha hp; exact (h.near X hX hK hh E V x hA ha hp).wand hg

variable {ι : Type} {s' : Finset ι} {f' : ι → Insert T}

lemma joined (h : ∀ i∈s', Fits H (f' i) u j) : Fits H (Insert.joined s' f') u j := by
  constructor
  · intro F X X' hX hK Y z z' hh hB; exact prod_congr rfl (fun i hi => (h i hi).regional X X' hX hK Y z z' hh hB)
  · intro F X hX hK E _ V Z z hV hZ hz
    exact Finset.measurable_fun_prod _ (fun i hi => (h i hi).along X hX hK E hV hZ hz)
  · intro F X hX hK hh z w; exact prod_congr rfl (fun i hi => (h i hi).onGauge X hX hK hh z w)
  intro F X hX hK hh E _ _ _ V x A b hA ha hp
  exact Zest.full s' _ (fun i hi => (h i hi).near X hX hK hh E V x hA ha hp)

lemma together (h : ∀ i∈s', Fits H (f' i) u j) : Fits H (Insert.together s' f') u j := by
  constructor
  · intro F X X' hX hK Y z z' hh hB; exact sum_congr rfl (fun i hi => (h i hi).regional X X' hX hK Y z z' hh hB)
  · intro F X hX hK E _ V Z z hV hZ hz
    exact Finset.measurable_fun_sum _ (fun i hi => (h i hi).along X hX hK E hV hZ hz)
  · intro F X hX hK hh z w; exact sum_congr rfl (fun i hi => (h i hi).onGauge X hX hK hh z w)
  intro F X hX hK hh E _ _ _ V x A b hA ha hp
  exact Zest.total s' _ (fun i hi => (h i hi).near X hX hK hh E V x hA ha hp)

lemma nextTo (h : Fits H r u j) (hp : Fits H t u j) : Fits H (r.nextTo t) u j := by
  constructor
  · intro F X X' hX hK Y z z' hh hB
    exact congr_arg₂ (·*·) (h.regional X X' hX hK Y z z' hh hB) (hp.regional X X' hX hK Y z z' hh hB)
  · intro F X hX hK E _ V Z z hV hZ hz; exact (h.along X hX hK E hV hZ hz).mul (hp.along X hX hK E hV hZ hz)
  · intro F X hX hK hh z w; exact congr_arg₂ (·*·) (h.onGauge X hX hK hh z w) (hp.onGauge X hX hK hh z w)
  intro F X hX hK hh E _ _ _ V x A b hA ha hG
  exact (h.near X hX hK hh E V x hA ha hG).paint (hp.near X hX hK hh E V x hA ha hG)

end Fits
end YM.RGLocalTaylor
