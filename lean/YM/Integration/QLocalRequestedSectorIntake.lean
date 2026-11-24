import YM.Integration.QLocalInheritedPhysicalInlet
import YM.Integration.QLocalRequestedHeir

/-! Native E6 intake on the actual physical tube for the submitted inherited
    action and the complete original vacuum hard bank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.QLocalRequestedSectorIntake
open Filter Function Lattice Wilson Pressure RG Marker Precision
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push.AbsoluteSums
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalInheritedPhysicalInlet QLocalRequestedHeirQuote
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J} {z : LocalFormal.Datum R.family Γ}
    {F : AnalyticInput J A z} {η : ℝ} (I : FullPreparedInputAt F η)
local notation "a₀" => R.alloy.B.a
local notation "m₀" => z.level
local notation "j₁" => (a₀).clock.J (m₀+1)
local notation "j₀" => (a₀).clock.J (m₀)
local notation "x₀" => (a₀).clock.hatBeta (m₀)
local notation "S₀" => (a₀).clock.op (m₀) z.period
local notation "Y₁" => R.family.path.rep z.cutoff z.period (m₀+1)
local notation "p₁" => A.inputNorm (m₀)
local notation "T₀" => ships R.alloy.B z.cutoff (m₀) z.period
local notation "P₀" => query R.metals.p R.metals.K (j₁) (j₀)

theorem intake (hi : Retained.NativeIntake I) (paid : I.inherited≤(a₀).clock.allowance (m₀+1)) :
    Intake (teller J (P₀)) (T₀) (x₀) (rep I) := by
  have hc := (R.T.sticks z.cutoff z.period).prices (m₀+1) (Nat.zero_le _) z.below
  have old := Application.intake_at R.alloy.B z.cutoff (m₀) z.period z.below (Y₁) hc.1 hc.2
  have ht : (p₁).threshold=(Y₁).p.threshold := I.wellFormed.threshold.trans
    (congrArg BudgetPoint.threshold (I.carrier.point.trans hc.1.point.symm))
  have hβ := Application.clock_next (a₀) (m₀) z.period
  have he : incomingE G (S₀).patch.L (x₀)=(a₀).clock.allowance (m₀+1) := by
    unfold incomingE
    rw [←hβ]
    rfl
  have hk : incomingK G (S₀).patch.L (x₀)=(a₀).clock.forcedAllowance (m₀+1) := by
    unfold incomingK Delay.fineMonitor
    rw [←hβ]
    rfl
  have original := lawful I hi old.cap.paths
  refine ⟨funds J old.ready,⟨old.received.path,I.carrier.clip.trans old.received.clip,ht.trans old.received.temp⟩,
    ⟨original.paths,?_⟩,(A.input_norm _).reserve.symm,old.height,?_,old.window⟩
  · rw [he,hk]
    obtain ⟨w,hv,hw⟩ := original.labels.boundE
    exact {original.labels with boundE := ⟨w,hv,fun u=>budget_loosen (hw u) paid⟩}
  change (p₁).B=radiusB (betaF G (x₀) (S₀).patch.L)
  rw [←hβ]
  exact (A.input_norm _).block

omit [DecidableEq V] [Fintype V] in
/-- A common late scale for every cutoff, period and admissible full input.
    The physical field order supplies a strict surplus over the E6 intake. -/
theorem affordable (hG : G.Simple) : ∀ᶠ m : ℕ in atTop, ∀ N period, m≤N →
    J.inheritedConstant*Pert.Asymptotics.regulatorRun R.family N period m^((J.order:ℝ)+1-J.eta)≤
      R.family.path.levels.clock.allowance m := by
  let L := R.family.path.levels
  let s := (J.order:ℝ)+1-J.eta
  let d := s-11/5
  have hj : (2:ℝ)≤J.order := by exact_mod_cast J.order_ge_two
  have hd : 0<d := by dsimp [d,s]; linarith [J.eta_lt_half]
  have hs : 0 ≤ s := by dsimp [d] at hd; linarith
  let k := J.inheritedConstant*(2:ℝ)^s
  have drop := (Multi.Wage.small_hat hG L).rpow_const (Or.inr hd.le)
  have h : Tendsto (fun m => k*Currency.weight L d m) atTop (𝓝 0) := by
    simpa only [Currency.weight,Real.zero_rpow hd.ne',mul_zero] using
      (tendsto_const_nhds (x:=k) (f:=atTop)).mul drop
  filter_upwards [h.eventually_le_const zero_lt_one] with m ht N period hm
  have pay := (Currency.g_weight (C:=R.family) (q:=period) R.makes hm s hs).2
  calc
    _ ≤ J.inheritedConstant*((2:ℝ)^s*Currency.weight L s m) :=
      mul_le_mul_of_nonneg_left pay J.inherited_constant_nonnegative
    _ = (k*Currency.weight L d m)*Currency.weight L (11/5) m := by
      have split : Currency.weight L s m=Currency.weight L d m*Currency.weight L (11/5) m := by
        rw [show s=d+11/5 by dsimp [d]; ring,Currency.weight_add]
      rw [split]
      dsimp only [k]
      ring
    _ ≤ _ := mul_le_of_le_one_left (Currency.weight_pos L _ _).le ht

theorem admitted (hG : G.Simple) : ∃ M : ℕ, ∀ z : LocalFormal.Datum R.family Γ, M≤z.level →
    ∀ {F : AnalyticInput J A z} {η : ℝ} (I : FullPreparedInputAt F η), Retained.NativeIntake I →
      let a := R.alloy.B.a
      Intake (teller J (query R.metals.p R.metals.K (a.clock.J (z.level+1)) (a.clock.J z.level)))
        (ships R.alloy.B z.cutoff z.level z.period) (a.clock.hatBeta z.level) (rep I) := by
  obtain ⟨M,hm⟩ := eventually_atTop.1 (affordable (J:=J) R hG)
  refine ⟨M,?_⟩
  intro d hd F η I hi
  exact intake R I hi (I.inherited_bound.trans (hm (d.level+1) (by omega) _ _ d.below))

end YM.Integration.QLocalRequestedSectorIntake
end
