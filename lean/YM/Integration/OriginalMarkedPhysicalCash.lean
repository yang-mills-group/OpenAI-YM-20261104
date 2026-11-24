import YM.Integration.QLocalRequestedSectorCalendar

/-! The complete signed sector market on the original physical representation at its
presold input support and independently requested output orders and support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedPhysicalCash
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} (J : Request V)

/-- The original old inlet is accepted in the new offer at its actual support exponent. -/
theorem retell {c f : Side} {S : StepData c f} {P : Teller G} {T : Tube G S} {x : ℝ}
    {Y : Rep G f} (old : Intake P T x Y) (matched : J.inputSupport=Y.p.supportExponent) :
    Intake (teller J P) T x Y :=
  ⟨funds J old.ready,old.received,old.cap,matched,old.height,old.sizes,old.window⟩

variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {Δ : Daisy.Charity.RG12.Decal G}
    {C : Libretto G J.outputFieldOrder} {b : Booking G} {D : Patch} {x γ : ℝ}
    {c f : Side} {S : StepData c f}

/-- The same booked target, progress order, full stamped tube, and original representation. -/
def Available (_win : Window J Δ Q C b D x γ) (T : Tube G S) (Y : Rep G f) : Prop :=
  ∃ H : Cash b.W x b.μ D.L (target J Q) b.order b.c T Y,
    Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧ ConnectedActivityE6.SliceRows.Stamp T ∧
    Δ.rub (teller J P) (target J Q) (expense J Q) D.L b.W b.μ b.order (teller J P).below D.J x

theorem window (win : Window J Δ Q C b D x γ) (T : Tube G S) (Y : Rep G f)
    (works : Works (teller J P) D.L x S T) (stamp : ConnectedActivityE6.SliceRows.Stamp T)
    (entry : Intake (teller J P) T x Y) : Available J win T Y := by
  obtain ⟨H,renew⟩ := (win.ledger.2 _ _ _ T works).2 stamp Y entry
  exact ⟨H,renew,stamp,win.analytic⟩

variable [DecidableEq V] {Γ : Census V} (δ : Daisy.Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ)
    (η : ℝ) (R : Run G) (paid : QLocalRequestedSectorCalendar.Paid J δ extra η R.kit)
    (z : LocalFormal.Datum R.family Γ)
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "S₀" => R.alloy.B.a.clock.op z.level z.period
local notation "T₀" => ships R.alloy.B z.cutoff z.level z.period
local notation "win₀" => QLocalRequestedSectorCalendar.selected J δ extra η R paid z

/-- The incumbent action and every old forced address stay on the literal chosen `R.T`. -/
theorem actual (matched : J.inputSupport=(Y₁).p.supportExponent) :
    Available J (win₀) (T₀) (Y₁) := by
  have hc:=(R.T.sticks z.cutoff z.period).prices (z.level+1) (Nat.zero_le _) z.below
  have old:=Application.intake_at R.alloy.B z.cutoff z.level z.period z.below (Y₁) hc.1 hc.2
  have entry:=retell J old matched
  apply window J (win₀) (T₀) (Y₁) _ _ entry
  · exact ⟨entry.ready,rfl,by rw [add_comm 1]; exact R.alloy.B.a.fits.sizeT _ _⟩
  · exact PhysicalNext.Repeat.Opera.protocol (n:=z.period) R.alloy.B z.below R.kit.pledging.conducts.full

/-- The physical support-100 campaign admits every previously contracted output request. -/
theorem purchased (contract : J.inputSupport=100)
    (original : ∀i, (R.alloy.B.a.params i).supportExponent=100) : Available J (win₀) (T₀) (Y₁) := by
  apply actual J δ extra η R paid z
  have hp : (R.family.path.rep z.cutoff z.period (z.level+1)).p = R.family.path.levels.budget (z.level+1) :=
    (R.makes.wilson.represents z.cutoff z.period (z.level+1) z.below).vac
  rw [hp]
  exact contract.trans (original (z.level+1)).symm

end YM.Integration.OriginalMarkedPhysicalCash
