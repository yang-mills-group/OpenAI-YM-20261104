import YM.Integration.WilsonEpochOpenSource
import YM.Integration.WilsonEpochPhysicalStation
import YM.Integration.WilsonInversionSchur

/-! Evaluate the physical open UV columns on each actual signed inversion
cotree direction and feed their full finite product to the separately booked
interacting terminal Gaussian, including its own vacuum division. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochClosedSource

open Function Filter Lattice Wilson Source Source.Drops RG
open XSpace FVA2 FVA2.Register FVA2.Arrival
open FormalBulk08 FormalBulk08.Reef FormalBulk08.Flat FormalBulk08.Wick FormalBulk08.Roof
open FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Rial FormalBulk08.Mesa
open Stationary PowerSeries
open FormalBulk08.City Planned.PrimaryIntegral295.Place
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.InversionTop
open WilsonEpochPositionCoefficients WilsonEpochCylinderDifference
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (Y : Initialize G) (N per D : ℕ)
local notation "n" => R.family.side N per

def port {m : Side} (x : PertExtension.Orb.Dir G m) : Jets.Rays (wire G m) :=
  (Stationary.arm G m 1).symm (fun i => PertExtension.Orb.variation x
    (i.1,Exterior.axisEquiv.symm i.2))

theorem chart {m : Side} (x : PertExtension.Orb.Dir G m) (t : ℝ) :
    Stationary.input G m (t • port x) =
      PertExtension.Orb.links 1 (expLinks G _ (t • x)) := by
  rw [inversion_chart_roll]
  funext e
  change G.lieExp ((Stationary.arm G m 1) (t • port x) (e.1,Exterior.axisEquiv e.2)) * 1 = G.lieExp (t • _)
  rw [mul_one, map_smul, port, ContinuousLinearEquiv.apply_symm_apply]
  simp only [Pi.smul_apply,Equiv.symm_apply_apply]

def column (s : Folio G) : FormalBulk08.Orb.Pap (wire G n) :=
  let F := R.family.labels.level s.u.size
  let D' := max D (s.u.size + 1)
  ∑ j : F.Index, PowerSeries.C (MvPolynomial.C (F.coords (s.item Y) j).re) *
    WilsonEpochOpenSource.leaf R L a (show s.u.size < D' from
      (Nat.lt_succ_self _).trans_le (le_max_right ..)) N per s.addr j

private theorem smooth (s : Folio G) :
    ContDiffAt ℝ ∞ (fun z : Jets.Rays (wire G n) => placed R Y n s (input G n z)) 0 := by
  let F := R.family.labels.level s.u.size
  let T := R.family.localSection s.u.size
  let c := F.coords (s.item Y)
  let o := wrap n s.addr
  let v := fun j : F.Index => fun z : Jets.Rays (wire G n) => (T.places (copy F j) o (input G n z)).re
  have relation : (fun z : Jets.Rays (wire G n) => placed R Y n s (input G n z)) =
      ∑ j : F.Index, (c j).re • v j := by
    funext z
    have eq := congrArg Complex.re (ActualStencilCylinder.section_expansion T (R.makes.sections _) c n o (input G n z))
    simpa only [placed,ActualStencilCylinder.observed,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,v,copy] using eq
  rw [relation]
  rw [show (∑ j : F.Index, (c j).re • v j) =
      (fun z => ∑ j : F.Index, (c j).re • v j z) from by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply]]
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.const_smul
  let pull := fun z : Jets.Rays (wire G n) => z ∘ FormalBulk08.Lotus.tint o
  have f (z : Jets.Rays (wire G n)) : v j z = (T.places (copy F j) 0 (input G n (pull z))).re := by
    change _ = (T.places (copy F j) 0 (Lattice.translate o (input G n z))).re
    rw [T.places_trans,zero_add]
  rw [funext f]
  have hv : ContDiffAt ℝ ∞ (fun z : Jets.Rays (wire G n) =>
      (T.places (copy F j) 0 (input G n z)).re) (pull 0) := Rial.coatG T n j
  have ht : ContDiffAt ℝ ∞ pull 0 := contDiffAt_pi.mpr fun i => contDiffAt_apply ..
  exact hv.comp 0 ht

/-- The complete positive-link source column evaluated on the reflected,
signed, tree-zero field of the inversion quotient. -/
def measured (s : Folio G) : Kernel (Unit × PertExtension.Orb.Dir G n) :=
  fun u => into (Jets.glimpse (port u.2) (column R L a Y N per D s))

theorem primitive (s : Folio G) :
    measured R L a Y N per D s = InversionTop.raw (PertExtension.Orb.restrictedO (placed R Y n s)) := by
  have hr : column R L a Y N per D s = paste (fun z : Jets.Rays (wire G n) => placed R Y n s (input G n z)) :=
    WilsonEpochOpenSource.original R L a Y s (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right D _)) N per
  funext u
  unfold measured InversionTop.raw InversionTop.lift
  rw [hr]
  congr 1
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_mk,Jets.glimpse_coeff,Jets.trace_paste]
  let f := fun z : Jets.Rays (wire G n) => placed R Y n s (input G n z)
  let v := PertExtension.Orb.restrictedO (placed R Y n s) ∘ expLinks G (PertExtension.Orb.Cotree n)
  have h : (fun t : ℝ => f (t • port u.2)) = (fun t : ℝ => v (t • u.2)) := by
    funext t
    exact congrArg (placed R Y n s) (chart u.2 t)
  have hs := directions (smooth R Y N per s) (port u.2)
  change Aspiration (fun t : ℝ => f (t • port u.2)) _ at hs
  rw [h] at hs
  exact congrFun (hs.unique (directions (placed_valid R Y n s).curved.germ u.2)) k

private theorem admissible (m : Side) (ev : Even m.val) (l : List (Folio G)) :
    PertExtension.Orb.PreTest (word (placed R Y m) l) := by
  induction l with
  | nil => exact Folio.matured Y m [] ev
  | cons s l ih => exact FVA2.Change.pre_pair (placed_valid R Y m s) ih

theorem product (l : List (Folio G)) :
    word (measured R L a Y N per D) l =
      InversionTop.raw (PertExtension.Orb.restrictedO (word (placed R Y n) l)) := by
  induction l with
  | nil => exact InversionTop.raw_one.symm
  | cons s l ih =>
    have ev := even_iff_two_dvd.mpr (ActualOriginalFiniteCoefficients.side_admissible R N per).2
    exact ((congrArg₂ (·*·) (primitive R L a Y N per D s) ih)).trans
      (InversionTop.raw_mul (placed_valid R Y n s).curved (admissible R Y n ev l).curved).symm

def submitted (l : List (Folio G)) : PowerSeries ℂ :=
  let ev := even_iff_two_dvd.mpr (ActualOriginalFiniteCoefficients.side_admissible R N per).2
  lower (Folio.asset l) ((feed ev).step (vertices G n) (word (measured R L a Y N per D) l))

/-- Closed coefficient extracted from actual physical open tensors on the
original terminal prior, including arbitrary repeated independently placed
sources, the precise Laurent shift, and the original interacting vacuum. -/
theorem closed (l : List (Folio G)) : submitted R L a Y N per D l =
    into (actual R Y n l) := by
  rw [submitted,product]
  exact WilsonEpochOriginalFeed.identified R Y n _ l

end YM.Integration.WilsonEpochClosedSource
end
