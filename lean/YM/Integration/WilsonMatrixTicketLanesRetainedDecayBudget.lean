import YM.Integration.WilsonMatrixTicketLanesReportedPrepaid
import YM.RGComparison.Core16.Silk.Wages

/-! Prepay the decay rate itself on the same physical campaign, before any volume or field is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedDecayBudget
open Function Filter Set Finset Real Lattice RG Wilson Tree Precision RG.Supply
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Next.Foundations Push.PriceCompiler Input
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel RGComparison.Core16.Silk
open RGComparison.Core16.Forge RGComparison.Core16.Lumen
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
variable {G : Gauge}

/-- The local price for the complete connected two-quadratic response. Both its prefactor and its
inverse spatial rate are charged at the same original stage, uniformly in all later volumes. -/
def Offer (G : Gauge) (cap : ℕ) (H : Patch) (K : KernelChoices) (x : ℝ) :=
  ∃ (P : Oven H) (X : P.Form G) (C : ℝ),P.Offers X K ∧ (cap:ℝ)+1 ≤ X.Q ∧
    0≤C ∧ 256*C≤2+log x ∧ (shade X)⁻¹≤2+log x ∧ Silk.Past X C 0 2 2

private theorem reserve (cap : ℕ) {H : Patch} {K : KernelChoices} (branches : H.Branches K G) :
    ∀ᶠ x : ℝ in atTop,Offer G cap H K x := by
  obtain ⟨P⟩:=Oven.builtafter H
  obtain ⟨X,width,accept⟩:=P.fund branches ((cap:ℝ)+1) (by positivity)
  obtain ⟨C,c₀,enough⟩:=Silk.silence accept.good 0 2 2
  have rising:=tendsto_atTop_add_const_left _ (2:ℝ) tendsto_log_atTop
  filter_upwards [rising.eventually_ge_atTop (256*C),rising.eventually_ge_atTop (shade X)⁻¹] with x fee rate
  exact ⟨P,X,C,accept,width.symm.le,c₀,fee,rate,enough⟩

private theorem patches (s : Sheet G) (D : Rolls s) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ H : Patch,H.L=D.L k → H.J=k → Offer G k H s.kernel x := by
  by_cases live : ∃ H : Patch,H.L=D.L k ∧ H.J=k
  · obtain ⟨H,h₁,h₂⟩:=live
    filter_upwards [reserve k (s.has H)] with x issued
    intro H' length date
    suffices H=H' from this ▸ issued
    cases H;cases H';dsimp only at *;grind
  exact Eventually.of_forall fun _ H length date=>False.elim (live ⟨H,length,date⟩)

def Paid (G : Gauge) : Prediction G:=fun {_} {_} {A} _=>∀cap,∀ᶠ m : ℕ in atTop,
  Offer G cap (A.B.a.clock.op m 0).patch A.B.a.clock.kernel (A.B.a.clock.hatBeta m)

private theorem prepaid (s : Sheet G) (price : MapPrices) : Prepaid (@Paid G) s price := by
  intro targets expenses flags program wages baton wants
  refine ⟨fun _=>0,?_⟩
  intro l hl D w u Z post scouts θ stages P V quarter
  let demand (k : ℕ) (x : ℝ):Prop:=∀H : Patch,H.L=D.L k → H.J=k → Offer G k H (ThroughLaunch.raise s l).kernel x
  obtain ⟨W,hVW,_,grant⟩:=delay_extra V demand (fun _ _ _=>True) (patches (ThroughLaunch.raise s l) D) (fun _ _=>by simp)
  refine ⟨W,hVW,?_⟩
  intro U hWU table wait priced B
  dsimp only
  intro η q exchange aux rider booth b shelter works divides cap
  filter_upwards [B.a.fits.deep.eventually_ge_atTop cap] with m later
  let k:=B.a.clock.J (m+1)
  let H:=(B.a.clock.op m 0).patch
  have side : H.L=D.L k:=Push.PriceCompiler.block_eq B.valid m
  obtain ⟨P,X,C,off,width,rest⟩:=(grant U hWU).1 k (B.a.clock.hatBeta m) (B.valid.pays m) H side rfl
  rw [B.valid.kernel]
  refine ⟨P,X,C,off,?_,rest⟩
  exact (add_le_add_left (Nat.cast_le.mpr (later.trans (B.a.fits.mono (Nat.le_succ m)))) _).trans width

/-- These two numerical costs can be combined with all other existing original campaign costs. -/
theorem allPrices : FundedPredictionSupply.AllPrices (@Paid G):=fun s _=>prepaid s _

end YM.Integration.WilsonMatrixTicketLanesRetainedDecayBudget
