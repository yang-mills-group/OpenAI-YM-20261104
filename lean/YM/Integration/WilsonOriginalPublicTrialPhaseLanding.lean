import YM.Integration.WilsonOriginalPublicTrialPhasePaidBoard
import YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice

/-! The first simultaneous charge on a selected physical door keeps the issued
upper and lower invoices and pays its actual radii before the cutoff and period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseLanding
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(R:Run G){N m per:ℕ}{I:Type}[Fintype I][DecidableEq I]{Z:Census I}
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per (m+1)
local notation "Q" => (H).rep N per m
local notation "O" => (H).levels.clock.op m per

def first (w l:ℝ):ℝ:=min w (1/(1+2*|l|))

theorem limits {w:ℝ}(hw:0<w)(l:ℝ):
    0<first w l ∧ first w l≤w ∧ 2*first w l*l≤1:=by
  have a:0<1+2*|l|:=by positivity
  have h:0<first w l:=lt_min hw (one_div_pos.mpr a)
  refine ⟨h,min_le_left ..,?_⟩
  calc
    2*first w l*l ≤ first w l*(1+2*|l|):=by
      nlinarith [mul_nonneg h.le (sub_nonneg.mpr (le_abs_self l))]
    _ ≤ (1/(1+2*|l|))*(1+2*|l|):=
      mul_le_mul_of_nonneg_right (min_le_right ..) a.le
    _=1:=one_div_mul_cancel a.ne'

private theorem smaller {n:Side}{B:Rep G n}{X:I→Three G n}{M:Config G n→Poly Z}
    {o:I→Site n}{w w':I→ℝ}{e:ℝ}(old:MenuBoard B X M o w e 1)
    (pos:∀i,0<w i)(pos':∀i,0<w' i)(hh:∀i,w' i≤w i):
    MenuBoard B X M o w' e 1:=by
  refine ⟨old.cleared,old.fettled,?_⟩
  have peg:Repegs o B.p.B w w' 0 1 Z:=
    slighter pos pos' (fun i=>by simpa only [one_mul] using hh i) zero_le_one le_rfl
  exact old.grants.prune pos pos' peg zero_le_one (by linarith) (by norm_num)

omit [Fintype I] in
private theorem keep {n:Side}(o:I→Site n)(B:ℕ)(w:I→ℝ)(pos:∀i,0<w i):
    Repegs o B w w (1/2) 1 Z:=by
  intro i _ p _
  rw [one_mul]
  apply le_mul_of_one_le_right
  · exact Finset.prod_nonneg fun j _=>(pos j).le
  apply Real.one_le_exp
  positivity

/-- All nonlinear faces and all unoccupied Wilson activities remain on the same original push. -/
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(hm:m<N)
    (o:I→Site ((C).side (m+1) per))(w l:I→ℝ)(ν:I→ℂ)
    (X:I→Three G ((C).side (m+1) per))(Y:I→Three G ((C).side m per))
    (M:Config G ((C).side (m+1) per)→Poly Z)(pos:∀i,0<w i)(large:∀i,1≤‖ν i‖)
    (started:MenuBoard (P) X M o w ((P).p.supportExponent-3) 1)
    (rides:∀i,Ride (O) (o i) ((O).ratio.parent (o i)) (R.doors N per m hm) (ν i) (X i) (Y i) (l i))
    (slots:Occupancy o (apron (H).levels m))
    (parents:Occupancy ((O).ratio.parent ∘ o) (apron (H).levels m)):
    let restored:=fun i=>PhysicalNext.Repeat.Legato.Bandage.renal (H).levels m*first (w i) (l i)
    (∀i,0<restored i) ∧ MenuBoard (Q) (fun i=>(ν i)⁻¹ • Y i)
       ((O).push (P).beta M) ((O).ratio.parent ∘ o) restored ((H).levels.budget m).supportExponent 1:=by
  intro restored
  obtain ⟨a,b,paid⟩:=stock.exactMoon.days N per m hm
  have estate:Coursework (H) _ _ _ a b:=⟨paid.2,paid.1⟩
  have legal i:=limits (pos i) (l i)
  have healthy i:0<restored i:=mul_pos estate.poses.hats.1 (legal i).1
  have cut:=smaller started pos (fun i=>(legal i).1) (fun i=>(legal i).2.1)
  have same:(P).p.supportExponent=((H).levels.budget (m+1)).supportExponent:=
    congrArg BudgetPoint.supportExponent (R.makes.wilson.represents N per (m+1) hm).vac
  have endorsed:((H).levels.budget (m+1)).supportExponent-4≤(P).p.supportExponent-3:=by rw [same];linarith
  exact ⟨healthy,estate.send R.makes.wilson hm cut endorsed large (fun i=>(legal i).1)
    rides slots parents (fun i=>(legal i).2.2) healthy (keep _ _ restored healthy)⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseLanding
end
