import YM.Integration.ActualOriginalDictionary
import YM.WilsonComparison.Finite.Multiplet

/-! Complete calibrated columns in the original Run's retained field basis.
The full fee sequences and the common bare-variable substitution are explicit.
The separate fixed-configuration observable identity below describes the
coefficient weights only; it is not an identification of an analytic qlocal
input, nor does it omit the substitution from the formal column identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalCalibratedColumns

open Function Finset Precision Lattice
open MS MS.Landau MS.Swirl MS.Swirl.Near MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Native MS.Book MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors
open MS.Book.Convolve MS.Book.Program MS.Native.Wilsonian
open MSBar Barr Bric Inlay Odom MS.Land MS.Menus MS.Rake
open WilsonComparison.Finite PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G) (B : MS.Local.Physical.Deck G)
    (Q : Land.Prescription B) (u : Label B) (μ : ℝ)

local notation "D" => ActualOriginalDictionary.dictionary R B

/-- The complete native formal column is a finite sum of the original fields.
The same shift Q.team mu occurs in every summand, at all coupling orders. -/
theorem reel_original :
    WilsonComparison.Finite.reel Q.team ((D).calibrated Q u) μ =
      ∑ g : Glyph B u.h,
        rates (Dot G Cover) (fun k => oil (Q.fees u.h u.item) g k μ)
          (substitute (shift Q.team μ)
            (levels g.grade
              (∑ j : (R.family.labels.level g.size).Index,
                (ActualOriginalDictionary.weight R B g.size g.grade g.2.2 j : ℂ) •
                  (ActualFiniteStencil.retained R g.size j).F))) := by
  unfold WilsonComparison.Finite.reel Dictionary.calibrated
  rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList,
    ← Finset.sum]
  apply Finset.sum_congr rfl
  intro g _
  rfl

/-- A coefficient-weighted finite observable at a fixed gauge configuration.
This is the physical component expansion of the calibrated multiplet; its
argument is not implicitly changed to a running-coupling configuration. -/
def weightedObservable (n : Side) (z : Site n) (U : Wilson.Config G n) (k : ℕ) : ℂ :=
  (((D).calibrated Q u).map
    (fun p => p.u μ k * (p.f.O n z U : ℂ))).sum

/-- Every full fee coefficient multiplies the original SectionData observable,
with no choice of a replacement lift or new physical stencil. -/
theorem weighted_observable_original
    (n : Side) (z : Site n) (U : Wilson.Config G n) (k : ℕ) :
    weightedObservable R B Q u μ n z U k =
      ∑ g : Glyph B u.h,
        oil (Q.fees u.h u.item) g k μ *
          (R.family.localSection g.size).places
            (ActualOriginalDictionary.coordinates R B g.size g.grade g.2.2) z U := by
  unfold weightedObservable Dictionary.calibrated
  rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList,
    ← Finset.sum]
  apply Finset.sum_congr rfl
  intro g _
  change oil (Q.fees u.h u.item) g k μ * (((D).cylinder g.size g.grade g.2.2).O n z U : ℂ) = _
  rw [ActualOriginalDictionary.original_section R B g.size g.grade g.2.2 n z U]

end YM.Integration.ActualOriginalCalibratedColumns
end
