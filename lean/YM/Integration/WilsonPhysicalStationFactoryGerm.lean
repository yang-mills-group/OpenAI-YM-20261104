import YM.Integration.WilsonPhysicalStationTableJump
import YM.Trace.Physicalv2.GermSplit

/-! Rebind a genuinely pushed unary to the already registered factory entry.
The two raw primary vectors incur the germ tariff on both true stored budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFactoryGerm
open Filter Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)(d N p i:ℕ)(y:R.family.label d)

def incoming (a:ℕ):store R.family d p a:=
  (R.family.factory d N p).entries a ((R.family.factory d N p).terminal.symm y)

def salary (a:ℕ):ℝ:=
  (R.family.path.levels.params a).columns*(R.family.labels.level d).coeffSize
    ((R.family.labels.level d).core (incoming R d N p y a).x)

theorem held {a:ℕ}(beginning:R.family.ref d≤a)(inside:a≤N):
    reads (C:=R.family) d N p a (incoming R d N p y a) (salary R d N p y a):=by
  let based:=R.makes.calibrated d N p (beginning.trans inside)
  exact ⟨based.format a beginning inside _,based.cap a beginning inside _⟩

theorem triangle (F:Frame G d)(x y z:F.Coeff):
    F.coeffSize (x-z)≤F.coeffSize (y-x)+F.coeffSize (y-z):=by
  change ∑a,‖x a-z a‖≤(∑a,‖y a-x a‖)+∑a,‖y a-z a‖
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun a _=> (norm_sub_le_norm_sub_add_norm_sub (x a) (y a) (z a)).trans_eq
    (congrArg (fun s=>s+‖y a-z a‖) (norm_sub_rev ..)))

theorem original (beginning:R.family.ref d ≤ i)(inside:i<N)
    (q:store R.family d p i){c:ℝ}(bought:reads (C:=R.family) d N p i q c)
    (pushed:q.density 0 (R.family.localSection d) (R.family.path.rep N p i)=
      ((R.family.S.block i).val:ℂ)^d • (R.family.path.levels.clock.op i p).push (R.family.path.β N p (i+1))
        ((incoming R d N p y (i+1)).density 0 (R.family.localSection d) (R.family.path.rep N p (i+1)))):
    page (C:=R.family) d p i (incoming R d N p y i)=page d p i q ∧
    (R.family.labels.level d).coeffSize ((incoming R d N p y i).x-q.x) ≤
      invoice (C:=R.family) d i p*(salary R d N p y i+c):=by
  have issued:=held R d N p y beginning inside.le
  have eqn:= (R.makes.calibrated d N p (beginning.trans inside.le)).unnormalized i beginning inside
    ((R.family.factory d N p).terminal.symm y)
  have identical:value (C:=R.family) d N p i (incoming R d N p y i)=value d N p i q:=
    eqn.trans pushed.symm
  have same:=same_page R.makes inside.le beginning issued bought (Filter.EventuallyEq.of_eq identical)
  refine ⟨same,?_⟩
  have old:=measured_diff d N p i R.makes beginning inside.le issued
  have fresh:=measured_diff d N p i R.makes beginning inside.le bought
  rw [←same] at fresh
  exact (triangle d _ _ _ _).trans ((add_le_add old fresh).trans_eq (mul_add ..).symm)

end YM.Integration.WilsonPhysicalStationFactoryGerm
end
