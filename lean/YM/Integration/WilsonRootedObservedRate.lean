import YM.Integration.WilsonRootedLightSelection
import YM.Integration.ManuscriptQLocalObservedComponents

/-! Evaluate the signed high-star sum on the original physical conditional law
at arbitrary coarse fields, with one charge across tests and finite truncations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedObservedRate
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy MergeProof LocalLTE RGLocalTaylor
open Org GapsLocal.Renew ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonOriginalMarkedExistence
open scoped Topology BigOperators Classical

universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
    {R : Run G} {J : Request V} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A d} {η : ℝ}
    (I : FullPreparedInputAt F η) {book : Booking G} (H : WilsonRootedSubmittedTail.CashAt I book)

def Observed (price : ℝ) : Prop :=
  let lev := R.alloy.B.a
  let Q := R.kit.target (lev.clock.J (d.level+1)) (lev.clock.J d.level)
  ∀ (Z : BudgetPoint), Z.threshold = Pressure.temp (lev.clock.hatBeta d.level) →
    Z.order ≤ J.outputFieldOrder → Z.power ≤ J.outputDistanceOrder →
    ∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
      let M := (ManuscriptQLocalMarkedRoster.promised
        (ManuscriptQLocalMarkedHeightRun.rosterBudget I) base x E K).terms
      ManuscriptQLocalObservedComponents.Tested H Chi.canonical M Z F.inputRadii
        (ManuscriptQLocalMarkedHeightTail.matrix H M)
        (fun z => Height.tiredN H (ManuscriptQLocalMarkedHeightRun.length J) z.1)
        (expense J Q).earn price

theorem original {u v : ℝ} (paid : WilsonRootedSubmittedTail.Submitted I H u) (hv : u ≤ v) :
    Observed I H v := by
  obtain ⟨a,b,C',d',rv,s,z,B,e,q,k,N,_,host,_,test⟩ := paid
  intro Z ht hord hpower base x E K
  let M := (ManuscriptQLocalMarkedRoster.promised (ManuscriptQLocalMarkedHeightRun.rosterBudget I)
    base x E K).terms
  let keep := fun z : Fan.Stars H (fun i => (M i).M) => Height.tiredN H (ManuscriptQLocalMarkedHeightRun.length J) z.1
  apply ManuscriptQLocalObservedComponents.paid H Chi.canonical M N host Z ht hord J.outputDistanceOrder hpower
    F.inputRadii (ManuscriptQLocalMarkedHeightRun.rosterBudget I).radii
    (ManuscriptQLocalMarkedHeightTail.matrix H M) keep
  intro root
  have sale := test base x E K root
  apply Push.AbsoluteSums.budget_mono ⟨sale.1,sale.2.1,sale.2.2.trans hv⟩
  · intro z
    by_cases live : ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i => (M i).M) z
    · simpa only [live, and_true, keep, M] using sale.1 z
    · simp [live]
  · intro z
    by_cases live : ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i => (M i).M) z
    · simp only [live, and_true, keep, M, le_refl]
    · simpa only [live, and_false, if_false, zero_mul, ite_self, keep, M] using sale.1 z

variable (R)

theorem power (hG : G.Simple) (p q : ℕ) (order : q ≤ p) {τ : ℝ} (pos : 0 < τ) :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m < N →
      let g := Pert.Asymptotics.regulatorRun R.family N per (m+1)
      (2*g)^(p+1) ≤ τ*g^q := by
  let B : ℝ := 2^(p+1)
  have bp : 0 < B := by dsimp [B]; positivity
  have ep : 0 < min 1 (τ/B) := lt_min zero_lt_one (div_pos pos bp)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (Currency.g_small hG R.makes _ ep)] with m small N per hm
  let g := Pert.Asymptotics.regulatorRun R.family N per (m+1)
  have gp : 0 ≤ g := (Currency.g_pos R.makes N per (m+1) hm).le
  have gs : g ≤ min 1 (τ/B) := (small N per hm).le
  have bound : B*g ≤ τ := calc
    _ ≤ B*(τ/B) := mul_le_mul_of_nonneg_left (gs.trans (min_le_right _ _)) bp.le
    _ = τ := by field_simp
  calc (2*g)^(p+1) = (B*g)*g^p := by rw [mul_pow, pow_succ g]; ring
       _ ≤ τ*g^q := mul_le_mul bound (pow_le_pow_of_le_one gp (gs.trans (min_le_left _ _)) order)
          (pow_nonneg gp _) pos.le

variable (A) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit)

def SignedOn (q : ℕ) (τ : ℝ) : Prop :=
  ∀ᶠ m in (atTop : Filter ℕ), ∀ (d : LocalFormal.Datum R.family Γ), d.level=m →
    ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η), Retained.NativeIntake I →
    let lev := R.alloy.B.a
    let i := lev.clock.J d.level
    let j := lev.clock.J (d.level+1)
    let book := paid.choose j i
    let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let S := lev.clock.op d.level d.period
    let Q := R.kit.target j i
    ∃ H : WilsonRootedSubmittedTail.CashAt I book,
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
      Observed I H (τ*g^q) ∧
      (∀ M ≤ S.patch.J, ∃ a : ℝ, Laminate.Known H (toll J) a 1 (Height.asset (expense J Q))
        J.outputFieldOrder J.outputDistanceOrder M) ∧
      ∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
        QLocalMarkedSourceCalendar.Priced (ManuscriptQLocalMarkedHeightRun.rosterBudget I) H base x E K

theorem charged (hG : G.Simple) (admit : WilsonRootedLightSelection.Admitted (Γ:=Γ) R A extra γ paid)
    (q : ℕ) (order : q ≤ J.order) {τ : ℝ} (pos : 0 < τ) : SignedOn (Γ:=Γ) R A extra γ paid q τ := by
  unfold SignedOn
  filter_upwards [admit,power R hG J.order q order pos] with m sold small d hm F η I hi
  obtain ⟨H,ren,cross,high,low,phases,_⟩ := sold d hm F I hi
  subst m
  exact ⟨H,ren,cross,original I H high (small d.cutoff d.period d.below),low,phases⟩

theorem selected (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit),
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin Real.log ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R ∧
      ∀ (Γ : Marker.Census V) (A : NumericSchedule R.family J) (q : ℕ), q ≤ J.order →
        ∀ τ > 0, SignedOn (Γ:=Γ) R A extra γ paid q τ := by
  obtain ⟨R,T,W,paid,salary,light,marks,checkout,correlations,funded,bill,admit⟩ :=
    WilsonRootedLightSelection.logarithmic.{u} hG hε J extra γ hγ
  exact ⟨R,T,W,paid,salary,light,marks,checkout,correlations,funded,bill,
    fun Γ A q hq τ ht => charged R A extra γ paid hG (admit Γ A) q hq ht⟩

end YM.Integration.WilsonRootedObservedRate
end
