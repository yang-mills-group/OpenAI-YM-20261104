import YM.Integration.ManuscriptQLocalVacuumFamily
import YM.Integration.QLocalRequestedSectorCalendar

/-! The original physical E6 chamber with the unmarked old curvature layers and the full
inherited hard gas present in the same source. The numerical reserve precedes all finite
periods and all original field and test choices. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalVacuumCash
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push Push.AbsoluteSums
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  (R : Run G) {J : Request V} (A : NumericSchedule R.family J)
  (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d)
  {η : ℝ} (I : FullPreparedInputAt F η)
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "X₁" => ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g₁ 1
local notation "billed" => I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g₁ 1
local notation "L₀" => R.alloy.B.a
local notation "j₀" => (L₀).clock.J d.level
local notation "j₁" => (L₀).clock.J (d.level+1)
local notation "x₀" => (L₀).clock.hatBeta d.level
local notation "S₀" => (L₀).clock.op d.level d.period
local notation "T₀" => ships R.alloy.B d.cutoff d.level d.period
local notation "P₀" => query R.metals.p R.metals.K (j₁) (j₀)

theorem funds (hG : G.Simple) :
    ∀ᶠ m in (atTop : Filter ℕ),∀ (d : LocalFormal.Datum R.family Γ),d.level=m →
      ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η),
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1≤
        R.family.path.levels.clock.allowance (d.level+1) := by
  let Q : Request V := { J with
    order := 2
    order_ge_two := le_rfl
    inheritedConstant := J.inheritedConstant+1
    inherited_constant_nonnegative := by linarith only [J.inherited_constant_nonnegative] }
  have hfund := (tendsto_add_atTop_nat 1).eventually (QLocalRequestedSectorIntake.affordable (J:=Q) R hG)
  have hsmall := (tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes 1 zero_lt_one)
  filter_upwards [hfund,hsmall,ManuscriptQLocalVacuumRadius.original (Γ:=Γ) R A hG J.eta_pos]
    with m bank late fee d hm F eta I
  subst m
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  have hg : 0<g:=Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have gs:g≤1:=(late d.cutoff d.period d.below).le
  have hrow : ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1 ≤ g^(3-J.eta) := by
    have h:=fee d rfl F 1 (by simpa only [abs_one,one_mul] using gs)
    simp only [abs_one,one_mul] at h
    apply h.trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_add hg]
    congr 1
  have hj : (2:ℝ)≤J.order := by exact_mod_cast J.order_ge_two
  have hpow : (3:ℝ)-J.eta≤(J.order:ℝ)+1-J.eta := by linarith
  have cast:=Real.rpow_le_rpow_of_exponent_ge hg gs hpow
  have hi:=I.inherited_bound.trans (mul_le_mul_of_nonneg_left cast J.inherited_constant_nonnegative)
  have hQ: (J.inheritedConstant+1)*g^(3-J.eta)≤R.family.path.levels.clock.allowance (d.level+1) := by
    simpa only [Q,Nat.cast_ofNat,show (2:ℝ)+1=3 by norm_num] using bank d.cutoff d.period d.below
  apply (add_le_add hi hrow).trans
  exact (le_of_eq (by ring)).trans hQ

theorem intake (hi : Retained.NativeIntake I)
    (old : Intake (teller J (P₀)) (T₀) (x₀) (QLocalInheritedPhysicalInlet.rep I))
    (pay : billed ≤ (L₀).clock.allowance (d.level+1)) :
    Intake (teller J (P₀)) (T₀) (x₀) (X₁) := by
  have hβ:=Application.clock_next (L₀) d.level d.period
  have he : incomingE G (S₀).patch.L (x₀)=(L₀).clock.allowance (d.level+1) := by
    unfold incomingE
    rw [←hβ]
    rfl
  have hk : incomingK G (S₀).patch.L (x₀)=(L₀).clock.forcedAllowance (d.level+1) := by
    unfold incomingK Delay.fineMonitor
    rw [←hβ]
    rfl
  have h:=(ManuscriptQLocalVacuumFamily.bought I hi 1).1
  refine ⟨old.ready,⟨old.received.path,old.received.clip,old.received.temp⟩,
    ⟨old.cap.paths,?_⟩,old.exponent,old.height,old.sizes,old.window⟩
  rw [he,hk]
  obtain ⟨w,hv,hw⟩ := h.boundE
  exact {h with boundE:=⟨w,hv,fun u=>budget_loosen (hw u) pay⟩}

variable (Δ : Daisy.Charity.RG12.Decal G) (extra : Stage→ℕ→ℝ) (γ : ℝ)
  (paid : QLocalRequestedSectorCalendar.Paid J Δ extra γ R.kit)

theorem original (hG : G.Simple) :
    ∀ᶠ m in (atTop : Filter ℕ),∀ (d : LocalFormal.Datum R.family Γ),d.level=m →
      ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η),Retained.NativeIntake I →
      let lev:=R.alloy.B.a
      let j:=lev.clock.J (d.level+1)
      let i:=lev.clock.J d.level
      let b:=paid.choose j i
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let Y:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
      ∃ H : Cash b.W (lev.clock.hatBeta d.level) b.μ (lev.clock.op d.level d.period).patch.L
        (target J (R.kit.target j i)) b.order b.c (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧ Crossed J γ R A d b H
          (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) := by
  have h₀:=(tendsto_add_atTop_nat 1).eventually (QLocalRequestedSectorIntake.affordable (J:=J) R hG)
  filter_upwards [funds (Γ:=Γ) R A hG,h₀] with m charge old d hm F η I hi
  subst m
  have e:=QLocalRequestedSectorIntake.intake R I hi
    (I.inherited_bound.trans (old d.cutoff d.period d.below))
  exact QLocalRequestedSectorCalendar.source_for_on (J:=J) (Δ:=Δ) (extra:=extra) (γ:=γ)
    (R:=R) (paid:=paid) (A:=A) (z:=d) _ (intake R A d F I hi e (charge d rfl F I)) rfl rfl _
    (ManuscriptQLocalVacuumFamily.bought I hi 1).1.boundE

end YM.Integration.ManuscriptQLocalVacuumCash
