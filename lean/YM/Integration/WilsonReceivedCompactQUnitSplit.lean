import YM.Integration.WilsonReceivedGeometricCellReadout
import YM.Integration.WilsonOriginalNullLanding
import YM.OPE.Portfolio.Solemn

/-! The measured unit and its complement retain every term of the actual signed Q withdrawal. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQUnitSplit
open Filter Lattice Wilson RG Labels Source Extra.Histories FVA1
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato WilsonReceivedGeometricCellReadout
open MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {i N per:ℕ}
local notation "F₀" => R.family.labels.level 0
local notation "Y₀" => R.family.params
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "S₀" => R.family.localSection 0

theorem unitSize {F:Frame G 0} (x:F.Coeff):F.coeffSize x=‖x 0‖:=by
  change ∑j,‖x j‖=_
  exact Finset.sum_eq_single 0 (fun j _ hj=>(hj (one_at (F:=F) j)).elim) (fun absent=>(absent (Finset.mem_univ 0)).elim)

def Split (W:Rep G (R.family.side i per)) (y:Site (R.family.side i per))
    (h:Coefficient (F₀) (R.family.side i per)) (B:ℝ) :Prop :=
  let α:=projection (F₀) (Y₀) W.p.threshold y h
  let z:=WilsonMeasuredSectionCorrection.subtract (F₀) h α
  z.Format y (Y₀) W ∧ z.remBound y W κ B ∧ projection (F₀) (Y₀) W.p.threshold y z=0 ∧
    (F₀).coeffSize z.x ≤ B ∧ (F₀).coeffSize α ≤ 2*B ∧
    h.density y (S₀) W=z.density y (S₀) W+(primary y α).density y (S₀) W

theorem original (simple:G.Simple) (W:Rep G (R.family.side i per)) (point:W.p=R.family.path.levels.budget i)
    (fixed:W.p.supportExponent ≤ 100) (late:Classical.choose (eventually_atTop.mp (WilsonOriginalNullLanding.local_section R 0 simple)) ≤ i)
    (fees:Fares) (y:Site (R.family.side i per)) (v:Values (Config G (R.family.side i per)))
    (h:Coefficient (F₀) (R.family.side i per)) (spent:Paid (N:=N) R W fees y v h) :
    Split R W y h (max fees.regular fees.primary) := by
  have saved:=spent.1
  have price:=spent.2.1
  have income: (F₀).coeffSize h.x ≤ max fees.regular fees.primary := by
    rw [unitSize]
    exact spent.2.2.1.trans (le_max_right ..)
  exact (Classical.choose_spec (eventually_atTop.mp (WilsonOriginalNullLanding.local_section R 0 simple))) i late per W
    point y h saved (rem_mono price (le_max_left ..)) income (Nat.zero_le _) (Nat.zero_le _) fixed

end YM.Integration.WilsonReceivedCompactQUnitSplit
