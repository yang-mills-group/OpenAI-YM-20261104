import YM.Integration.WilsonThermometerMixedKernel
import YM.Integration.WilsonThermometerUnitFilingCoarse

/- The single original affine relation between the complete three physical tables
   remains true after every intervening measured kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedAncestry
open Finset Lattice RG Wilson Marker MeasureTheory MergeProof.Accent PhysicalNext.Repeat.Legato
open WilsonThermometerMixedAmplitude
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge} (R:Run G) {N per t:ℕ}
local notation "P" => Config G (R.family.side t per)→Poly (J)

theorem original (q:ℂ)(A Y F:P) (erased:Integrable A (prior G _))(raised:Integrable F (prior G _))
    (line:∀U,Line q (A U) (Y U) (F U)) {b:ℕ}(bt:b≤t):
    ∀U,Line q (gust R.family.path N per t A b bt U) (gust R.family.path N per t Y b bt U)
      (gust R.family.path N per t F b bt U):=by
  induction bt using Nat.decreasingInduction with
  | of_succ j jt ih =>
    rw [gust_step R.family.path N per t A jt,gust_step R.family.path N per t Y jt,gust_step R.family.path N per t F jt]
    exact (WilsonThermometerMixedKernel.original _ (R.family.path.levels.transition_mass j per
      (R.family.path.β N per (j+1))) q _ _ _ (gust_live R.family.path N per t A erased jt)
      (gust_live R.family.path N per t F raised jt) ih).2
  | self => unfold gust;simpa only [Nat.decreasingInduction_self] using line
end YM.Integration.WilsonThermometerMixedAncestry
end
