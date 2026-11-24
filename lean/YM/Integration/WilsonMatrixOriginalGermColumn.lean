import YM.Integration.WilsonMatrixOriginalIndependentColumns
import YM.Trace.Physicalv2.GermGraph

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermColumn
open Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FVA2 MS.Local.Physical MS.Menus WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (B:Deck G) {m N p:ℕ}
local notation "V" => warehouse R

/-- Spend the actual old regular remainder in the same independent raw coordinates as the captured principal. -/
theorem correction (age:R.family.ref 4 ≤ m) (live:m≤N) (q:Coefficient (R.family.labels.level 4) (R.family.side m p))
    {r:ℝ} (held:reads 4 N p m q r) :
    (∑i:Glyph B 4,‖weights V B 4 (page 4 p m q) i-weights V B 4 q.x i‖)≤
      (invoice (C:=R.family) 4 m p*r)*fare V B 4 := by
  have budget:=bounded V B 4 (page 4 p m q-q.x)
  have gap:=measured_diff 4 N p m R.makes age live held
  have same (i:Glyph B 4) := congrFun ((weights V B 4).map_sub (page 4 p m q) q.x) i
  have priced:0≤fare V B 4 := Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  calc
    _ = ∑i:Glyph B 4,‖weights V B 4 (page 4 p m q-q.x) i‖ :=
      Finset.sum_congr rfl (fun i _=>congrArg norm (same i).symm)
    _ ≤ _ := budget.trans (mul_le_mul_of_nonneg_right gap priced)

/-- The full germ, with every old regular part, has its prescribed neutral coordinate *exactly*
at capture, before any older transfer. The first numerical discrepancy is a paid old regular remainder. -/
theorem normalized (opened:Opened R.family 4 m p) (live:m≤N) (x:R.family.label 4) :
    ∃ y:R.family.label 4, let q:=(R.family.factory 4 N p).entries m y
      page 4 p m q=x ∧ reads 4 N p m q (2*stock R.family m*(R.family.labels.level 4).coeffSize x) ∧
        (∑i:Glyph B 4,‖weights V B 4 x i-weights V B 4 q.x i‖)≤
          (invoice (C:=R.family) 4 m p*(2*stock R.family m*(R.family.labels.level 4).coeffSize x))*fare V B 4 := by
  let fit:=fitting 4 N p m R.makes opened live
  let y:=fit.symm x
  let q:=(R.family.factory 4 N p).entries m y
  have eq:fit y=x:=fit.apply_symm_apply x
  have measured:page 4 p m q=x:=(fitting_apply 4 N p m R.makes opened live y).symm.trans eq
  have paid:reads 4 N p m q (2*stock R.family m*(R.family.labels.level 4).coeffSize x):= by
    have original:=graph_cost 4 N p m R.makes opened live y
    change reads 4 N p m q (2*stock R.family m*(R.family.labels.level 4).coeffSize (fit y)) at original
    rwa [eq] at original
  refine ⟨y,measured,paid,?_⟩
  simpa only [measured] using correction R B opened.post live q paid

end YM.Integration.WilsonMatrixOriginalGermColumn
