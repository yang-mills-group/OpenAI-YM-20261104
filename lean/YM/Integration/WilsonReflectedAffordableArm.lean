import YM.Integration.WilsonReflectedRestartDate
/-! The actual appointed four-hearing arm at a prechosen finite restart.
The expenses of the finite-period projection, true hard reserve and
measured primary are uniform in both later regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedAffordableArm
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonReflectedFullPanel WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonReflectedFundedHearing
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family

def projectionBill (d f:ℕ):ℝ:=|GermGraph.price (C:=C₀) d| *
    Real.exp (2*((C₀).path.levels.budget f).supportExponent)
def charge (d f:ℕ):ℝ:=8+4*stock (C₀) f+projectionBill R d f

theorem projected (d f p:ℕ):invoice (C:=C₀) d f p≤projectionBill R d f:=by
  let B:=(C₀).path.levels.budget f
  have a:0≤B.supportExponent:=B.exponent_pos.le
  have sub:0≤B.supportExponent*((C₀).side f p).val/(10*(4*(B.B:ℝ)+2)):=by positivity
  have seen:wraps B ((C₀).side f p)≤Real.exp (2*B.supportExponent):=Real.exp_le_exp.mpr (sub_le_self _ sub)
  exact mul_le_mul (le_abs_self _) seen (Real.exp_pos _).le (abs_nonneg _)

theorem purchased (d f:ℕ){ε:ℝ}(ep:0<ε):∀ᶠ K:ℕ in atTop,
    ∀j N p q (before:j≤K)(upper:K≤N)(_early:j≤f)(_late:f≤K)
      (M:(C₀).label d ≃ₗ[ℂ] (C₀).label d)(Y:(C₀).label d)(bank:ℝ),
    receipt R d j K N p q before upper (1/32) M Y bank →
    ∀b s (o:Site ((C₀).side f p)),∃A:Arm R d N p f K,
    let B:=(1+wrapCost R d j)*bank
    A.Y=Y ∧ A.w=M.symm (full R d N p j Y) ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
    A.cash ≤ ε*B ∧ A.z.remBound 0 ((C₀).path.rep N p f) (safety (C₀) f) (ε*B) ∧
    ((C₀).labels.level d).coeffSize A.z.x ≤ ε*B ∧
    ((C₀).labels.level d).coeffSize (projection ((C₀).labels.level d) (C₀).params
      ((C₀).path.rep N p f).p.threshold 0 A.z) ≤ ε*B:=by
  let T:=charge R d f
  have st:0 ≤ stock (C₀) f:=zero_le_one.trans ((C₀).path.levels.params f).columns_ge
  have pr:0≤projectionBill R d f:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have maxH:1+4*stock (C₀) f≤T:=by unfold T charge;linarith only [pr]
  have maxI (p:ℕ):invoice (C:=C₀) d f p+4≤T:=by unfold T charge;linarith only [projected R d f p,st]
  have maxT:2≤T:=by unfold T charge;linarith only [pr,st]
  have ok:0<T:=by linarith only [maxT]
  filter_upwards [WilsonReflectedRestartDate.before_cutoffs R f (div_pos ep ok)] with K paid
  intro j N p q before upper early late M Y bank file b s o
  let B:=(1+wrapCost R d j)*bank
  let S:=WilsonOriginalMicroscopicGuardedReporters.stretch R (1/32) j K
  have sp:0<S:=by unfold S WilsonOriginalMicroscopicGuardedReporters.stretch;positivity
  have hbound:((C₀).labels.level d).coeffSize (M.symm (full R d N p j Y))≤S*B:=file.2.1
  have nn:0≤B:=by by_contra! bad;exact (not_lt_of_ge ((Work.G08.size_nonneg ..).trans hbound)) (mul_neg_of_pos_of_neg sp bad)
  obtain ⟨A,ay,aw,ab,as,ao,cash⟩:=WilsonReflectedFundedHearing.purchased R d j q before upper early late file b s o
  have stK:0 ≤ stock (C₀) K:=zero_le_one.trans ((C₀).path.levels.params K).columns_ge
  have ph:0≤hike (C₀) K f rate:=Real.rpow_nonneg (div_nonneg ((C₀).S.a_pos K).le ((C₀).S.a_pos f).le) _
  have pos:0≤A.cash:=by rw [cash];exact mul_nonneg ph (mul_nonneg (by linarith only [stK]) (Work.G08.size_nonneg ..))
  have raw:A.cash≤(ε/T)*B:=calc
    _ = _ :=cash
    _ ≤ hike (C₀) K f rate*((1+4*stock (C₀) K)*(S*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (aw ▸ hbound) (by linarith only [stK])) ph
    _ = hike (C₀) K f rate*(1+4*stock (C₀) K)*S*B:=by ring
    _ ≤ _ :=mul_le_mul_of_nonneg_right (paid j) nn
  have fullExpense:T*A.cash≤ε*B:=(mul_le_mul_of_nonneg_left raw ok.le).trans_eq (by field_simp)
  have fits {c:ℝ}(h:c≤T):c*A.cash≤ε*B:=(mul_le_mul_of_nonneg_right h pos).trans fullExpense
  refine ⟨A,ay,aw,ab,as,ao,?_,rem_mono A.filed.paid (fits maxH),
    A.filed.primary.trans (fits (maxI p)),A.filed.measured.trans (fits maxT)⟩
  simpa only [one_mul] using fits (c:=1) (by linarith only [maxT])

end YM.Integration.WilsonReflectedAffordableArm
end
