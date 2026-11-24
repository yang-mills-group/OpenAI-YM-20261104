import YM.Integration.WilsonThermometerUnitFilingCampus
import YM.Integration.WilsonThermometerRegisteredCapturedStudent

/-! The original compound earners, with all grounds and tests held fixed, on the spatial strip bought by the older campus. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingTuition
open Function Filter Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor
open RG.Shoot RG.Supply Precision Input Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Next.Foundations Push Push.AbsoluteSums Push.PriceCompiler
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WilsonThermometerUnitFilingCampus WilsonOriginalCompoundStrip WilsonWindowRootPurchase
open scoped Classical BigOperators
variable {G:Gauge}
theorem narrow {V α I:Type}[DecidableEq V]{n:Side}{P:Passport n V}{R:Census V}
    (X:I→Earn.Row P R G α){w:V→ℝ}{t:V→ℕ}{μ σ C:ℝ}{ord cap H:ℕ}
    (L:Scene.Armada X w t σ C ord cap H)(thin:μ≤σ):Scene.Armada X w t μ C ord cap H:=by
  have pay (i:I):(X i).height μ≤(X i).height σ:=by
    unfold Row.height
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right thin (by positivity))) (X i).sound.le
  have toll (i:I):0≤Poly.toll w (X i).mode:=by
    exact Finset.prod_nonneg (fun v _=>(L.positive v).le)
  refine ⟨L.toMinistry,L.positive,?_,⟨?_,L.purchases.usable⟩,L.honor⟩
  · intro x
    apply sumBudget_mono (L.suggests x) _ _ le_rfl
    · intro i
      split_ifs
      · exact mul_nonneg (toll i) (mul_nonneg (X i).sound.le (Real.exp_pos _).le)
      · exact le_rfl
    · intro i
      dsimp only
      split_ifs
      · exact mul_le_mul_of_nonneg_left (pay i) (toll i)
      · exact le_rfl
  · intro i
    apply le_trans _ (L.purchases.spend i)
    change (X i).atom.magnitude*Real.exp (μ*(X i).atom.length) ≤ (X i).atom.magnitude*Real.exp (σ*(X i).atom.length)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right thin (by positivity)))
      (Finset.sum_nonneg (fun _ _=>abs_nonneg _))

abbrev elected (Q:Request G)(R:Run G)(simple:G.Simple):=
  syllabus Q simple (fun _=>MintClock.splits) R.metals.p R.metals.K

theorem adjacent (Q:Request G)(R:Run G)(simple:G.Simple)
    (paid:WilsonThermometerUnitFilingCampus.Invoice Q simple (fun _=>MintClock.splits) R.kit)
    (i H k:ℕ)(fit:H≤R.alloy.B.a.clock.J i)(adm:k≤R.alloy.B.a.clock.J i+1):
    let μ:=width (elected Q R simple) R.metals.p.kernel (R.alloy.B.a.clock.J i) H
    let σ:=Poetry.Agenda.seed (roots simple R.metals.p R.metals.K) MintClock.splits (Burn.horizon k)
      (R.alloy.B.a.clock.J (i+1))
    0<μ ∧ μ≤σ/(16*max 1 (Q.multiplier H)) ∧ μ≤σ:=by
  intro μ σ
  let A:=R.alloy.B.a
  let j:=A.clock.J i
  let next:=A.clock.J (i+1)
  have up:j≤next:=A.fits.mono (Nat.le_succ i)
  have pace:next≤j+1:=A.fits.stepSlow i
  have cutoff:k≤j+1:=adm
  let c:Seats j:=(⟨0,by omega⟩,⟨k,by omega⟩,⟨next-j,by omega⟩)
  have stamp:raw simple (fun _=>MintClock.splits) R.metals.p R.metals.K j c=σ:=by
    change Poetry.Agenda.seed _ _ _ (j+(next-j))=Poetry.Agenda.seed _ _ _ next
    rw [Nat.add_sub_of_le up]
  let X:=elected Q R simple
  obtain ⟨_,good,_,top,_,_⟩:=WilsonOriginalCompoundStrip.date X R paid.1.1 i H fit
  have bound:X.radius R.metals.p.kernel j H≤σ:=by
    rw [←stamp]
    exact (min_le_left ..).trans ((min_le_left ..).trans ((min_le_right ..).trans ((room simple _ _ _ j).2 c)))
  have sz:0<σ:=Poetry.Agenda.stem _ _ _ _
  have amount:μ≤σ/(16*max 1 (Q.multiplier H)):=top.trans (div_le_div_of_nonneg_right bound (mul_nonneg (by norm_num) (X.grows H).le))
  have den:1≤16*max 1 (Q.multiplier H):=by linarith [le_max_left 1 (Q.multiplier H)]
  exact ⟨good,amount,amount.trans (div_le_self sz.le den)⟩

end YM.Integration.WilsonThermometerUnitFilingTuition
