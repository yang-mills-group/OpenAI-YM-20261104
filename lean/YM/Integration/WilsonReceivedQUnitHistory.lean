import YM.Integration.WilsonReceivedCompactQUnitSplit
import YM.Integration.WilsonOriginalNullUnitHistory
import YM.Integration.WilsonCapturedPrimaryTrailSites

/-! Whole signed density at geometric capture, including the scalar of the original curved field and every subsequently filed unit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedQUnitHistory
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {m N per k:ℕ}
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ j,Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
local notation "C₀" => R.family
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

/-- The projection of an original site onto each actual mesh down to its filed stop. -/
def address (t:ℕ) (y:Site (R.family.side t per)) (j:ℕ) : Site (R.family.side j per) :=
  if h:j ≤ t then (R.family.S.toDepth h per).parent y else 0

theorem at_birth (t:ℕ) (y:Site (R.family.side t per)) : address R t y t=y := by
  rw [address,dif_pos le_rfl]
  let T:=R.family.S.toDepth (le_refl t) per
  have unit:T.count.val=1:=Nat.eq_of_mul_eq_mul_left (R.family.S.side t per).property
    (T.exact_size.symm.trans (Nat.mul_one _).symm)
  have fixed:T.embed y=y := by rw [Ratio.embed,unit,one_smul,Lattice.wrap_lift]
  exact (congrArg T.parent fixed).symm.trans (T.embed_parent _)

theorem next (t j:ℕ) (before:j<t) (y:Site (R.family.side t per)) :
    address R t y j=(R.family.path.levels.clock.op j per).ratio.parent (address R t y (j+1)) := by
  simp only [address,dif_pos before.le,dif_pos (show j+1 ≤ t by omega)]
  exact Next.Rank.Station.parent_nested _ _ _ (R.family.S.block_odd _) (R.family.S.toDepth_odd before per) _

def Returned (b n:ℕ) (ε:ℝ) (y:Site (R.family.side (b+n) per)) (v:Values (Config G (R.family.side (b+n) per)))
    (fees:Fares) (h:Coefficient (F₀) (R.family.side (b+n) per)) : Prop :=
  let B:= max fees.regular fees.primary
  let α:=(projection (F₀) R.family.params (Ψ (b+n)).p.threshold y h) 0
  let o:=address R (b+n) y b
  ∃ (z:Coefficient (F₀) (R.family.side b per)) (a:ℕ→ℂ),
    z.Format o R.family.params (Ψ b) ∧ z.remBound o (Ψ b) (κ b) (gain (C₀) b (b+n)*B) ∧
    projection (F₀) R.family.params (Ψ b).p.threshold o z=0 ∧
    ‖α‖ ≤ 2*B ∧ (∀j<n,‖a j‖ ≤ ε*gain (C₀) (b+j) (b+n)*B) ∧
    flow (C₀) 0 N per b n (fun U=>v.withdrawn U-((Ψ (b+n)).eval U:ℂ)*v.filed U)=
      z.density o (S₀) (Ψ b)+(α+∑ j∈Finset.range n,a j) • (fun U=>((Ψ b).eval U:ℂ))

include course in
theorem original (b n:ℕ) (ε:ℝ) (floor:m ≤ b) (live:b+n ≤ N) (fees:Fares) (y:Site (R.family.side (b+n) per))
    (v:Values (Config G (R.family.side (b+n) per))) (h:Coefficient (F₀) (R.family.side (b+n) per))
    (spent:Paid (N:=N) R (Ψ (b+n)) fees y v h)
    (split:WilsonReceivedCompactQUnitSplit.Split R (Ψ (b+n)) y h (max fees.regular fees.primary))
    (gates:∀j<n,∀origin,Filed (C₀) 0 N per (b+j) Ψ origin ε) :
    Returned (N:=N) R Ψ b n ε y v fees h := by
  let o:=address R (b+n) y
  let B:=max fees.regular fees.primary
  let α:=projection (F₀) R.family.params (Ψ (b+n)).p.threshold y h
  let P:=WilsonMeasuredSectionCorrection.subtract (F₀) h α
  have endSite:o (b+n)=y:=at_birth R _ y
  obtain ⟨form,cost,zero,_,coin,whole⟩:=split
  have route (j:ℕ) (hj:j<n): o (b+j)=(R.family.path.levels.clock.op (b+j) per).ratio.parent (o (b+j+1)) :=
    next R _ _ (by omega) y
  obtain ⟨z,a,zfit,zpaid,znull,fees₀,record⟩:=WilsonOriginalNullUnitHistory.original R π Γ Ψ course
    b n ε floor live o route (fun j hj=>gates j hj _) P B (endSite.symm ▸ form) (endSite.symm ▸ cost) (endSite.symm ▸ zero)
  rw [endSite] at record
  refine ⟨z,a,zfit,zpaid,znull,?_,fees₀,?_⟩
  · simpa only [α,WilsonOriginalNullUnitFlow.size] using coin
  have law:=(course.1.walk (b+n) (by omega) live).truep.valid
  have intP:Integrable (P.density y (S₀) (Ψ (b+n))) (prior G _):=(P.envelope (S₀) law cost form).integrableC _
  have intA:Integrable ((primary y α).density y (S₀) (Ψ (b+n))) (prior G _):=
    ((primary y α).envelope (S₀) law (primary_rem α (show 0<(1:ℝ) from zero_lt_one))
      (primary_format (H:=R.family.params) α)).integrableC _
  have same (j:ℕ) (lo:m ≤ j) (hi:j ≤ N) : (fun U=>((Ψ j).eval U:ℂ))=liftVac R.family.path N per j :=by
    funext U
    change ((Ψ j).eval U:ℂ)=((R.family.path.rep N per j).eval U:ℂ)
    exact_mod_cast congrFun (course.1.walk j lo hi).view U
  have entered : (fun U=>v.withdrawn U-((Ψ (b+n)).eval U:ℂ)*v.filed U)=h.density y (S₀) (Ψ (b+n)) :=
    (funext spent.2.2.2.1).symm
  change flow (C₀) 0 N per b n _=z.density (o b) (S₀) (Ψ b)+(α 0+∑j∈Finset.range n,a j) • (fun U=>((Ψ b).eval U:ℂ))
  change h.density y (S₀) (Ψ (b+n))=P.density y (S₀) (Ψ (b+n))+(primary y α).density y (S₀) (Ψ (b+n)) at whole
  rw [entered,whole,flow_add (C₀) 0 N per b n _ _ intP intA,record,WilsonOriginalNullUnitFlow.raw,
    same (b+n) (by omega) live, WilsonOriginalNullUnitFlow.vacuum (C₀) R.makes N per b n _ live,
    ←same b floor (by omega),add_smul]
  abel

end YM.Integration.WilsonReceivedQUnitHistory
