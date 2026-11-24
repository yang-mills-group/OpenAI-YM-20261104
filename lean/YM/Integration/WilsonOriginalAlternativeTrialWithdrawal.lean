import YM.Integration.WilsonOriginalAlternativeTrialOptical
import YM.Integration.WilsonOriginalMicroscopicEntranceReader
import YM.Integration.WilsonOriginalAlternativeTrialEstate

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialWithdrawal
open Function Finset Lattice RG Tree Wilson Marker QuadraticLocal QuadraticLocal.Earn Multi Pressure MeasureTheory
open PhysicalNext PhysicalNext.Repeat Legato AllOrder AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal.Advent Extra.Histories Extra.Trajectories WilsonOriginalOccupiedTap
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent
open PhysicalNext.Repeat.Boulevard
open WilsonOriginalJointTrialHearing
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per m k t u:ℕ}
variable (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
variable {V:Type}[DecidableEq V][Fintype V]{J:Census V}{X I:Type}[Countable I]
local notation "F" i:max => Config G (R.family.side i per)

include course in
theorem original (mu:m ≤ u)(ut:u ≤ t)(tn:t ≤ N)(o:V → Site (R.family.side t per))
    (A:Gallery X I o (Ψ t) J)(w:V→ℝ)(wp:∀v,0<w v){E K:ℝ}
    (reg:A.E.Paid w (Ψ t).p.B (Ψ t).p.supportExponent E)
    (hard:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent K)(x:X)(s:J.Mode)(W:F u):
    let blank:=fun U:F t=>((Ψ t).eval U:ℂ) • Poly.pass (A.E.log x U)
    let residual:=fun U:F t=>((A.density x U).part s-((Ψ t).eval U:ℂ)*(Poly.pass (A.E.log x U)).part s)/((Ψ t).eval U:ℂ)
    actualTransport R.family (N:=N) residual ut W=
      ((Ψ u).eval W:ℂ)⁻¹*((gust R.family.path N per t (A.density x) u ut W).part s-
        (gust R.family.path N per t blank u ut W).part s):=by
  intro blank residual
  have rent:(gallery 0 A).K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent K:=by
    simpa only [gallery,one_mul] using WilsonOriginalOccupiedTap.paid A.K 0 (le_refl (1:ℝ)) (by simp) wp hard
  have same:(gallery 0 A).density x=blank:=funext fun U=>WilsonOriginalOccupiedWallet.origin A x U w wp rent
  have law:=(course.1.walk t (mu.trans ut) tn).truep.valid
  have pA:=QuadraticLocal.Tariff.integrable J o w wp A x ⟨reg,hard⟩ (Ψ t).p.exponent_pos.le law
  have pB:Integrable blank (prior G _):=by
    rw [←same]
    exact QuadraticLocal.Tariff.integrable J o w wp (gallery 0 A) x ⟨reg,rent⟩ (Ψ t).p.exponent_pos.le law
  have quiet:(Ψ t).eval=(R.family.path.rep N per t).eval:=(later R π Γ Ψ course (mu.trans ut) tn).view
  have low:(Ψ u).eval=(R.family.path.rep N per u).eval:=(later R π Γ Ψ course mu (ut.trans tn)).view
  have field (U:F t):((A.density x-blank) U).part s=(R.family.path.rep N per t).eval U • residual U:=by
    have nz:((Ψ t).eval U:ℂ)≠0:=by rw [quiet];exact Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson tn U).ne'
    change (A.density x U).part s-((Ψ t).eval U:ℂ)*(Poly.pass (A.E.log x U)).part s=_
    rw [Complex.real_smul,←quiet]
    dsimp only [residual]
    field_simp
  have receipt:=WilsonOriginalMicroscopicEntranceReader.normalized R ut (A.density x-blank) s (pA.sub pB) residual field W
  rw [←receipt,WilsonOriginalJointTrialHearing.difference R N per W ut _ _ pA pB s]
  unfold WilsonOriginalJointTrialHearing.read
  rw [low,mul_sub]

end YM.Integration.WilsonOriginalAlternativeTrialWithdrawal
end
