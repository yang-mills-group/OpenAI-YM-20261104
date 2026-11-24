import YM.Integration.WilsonOriginalCensusChronologicalMoney

/-! One purchase for the actual two-print accounts at every date of a fixed optical collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterCouplingClock
open Filter Lattice Wilson RG Pert.Asymptotics
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonOriginalDatedFieldsAtBoard
open scoped Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "g" N:max per:max i:max => regulatorRun R.family N per i

def wallet (f:ℕ):Degree:=⟨f,0⟩
def raw (d:ℕ):Degree:=⟨2,d⟩
def debt (f d:ℕ):Degree:=⟨f+2,d⟩
def work (n P f d:ℕ):ℕ:=P+(debt f d).pole*n

include simple in
theorem original (n cost P f d:ℕ)(C:ℝ)(cp:0 ≤ C):
    ∀ᶠ b:ℕ in atTop,∀{N per K i:ℕ},b ≤ i → i+1 ≤ K → K ≤ N → R.family.S.a b/R.family.S.a K ≤ (H b)^cost →
    0 < g N per b ∧ 3*(g N per b) ≤ 1 ∧ 0 < g N per i ∧ g N per i ≤ 1/2 ∧
    0 < g N per (i+1) ∧ g N per (i+1) ≤ 1/2 ∧
    (C*(H i)^f ≤ ((g N per b)^(wallet f).pole)⁻¹) ∧
    (C*(H i)^2*((g N per i)⁻¹)^d ≤ ((g N per b)^(raw d).pole)⁻¹) ∧
    (C*(H i)^(f+2)*((g N per i)⁻¹)^d ≤ ((g N per b)^(debt f d).pole)⁻¹) ∧
    C*(g N per (i+1))^(work n P f d+1+(wallet f).pole+1) ≤ (g N per b)^(work n P f d+1+(wallet f).pole) ∧
    C*(g N per (i+1))^(work n P f d+1+1) ≤ (g N per b)^(work n P f d+1):=by
  filter_upwards [restored R simple (wallet f) C cp cost,restored R simple (raw d) C cp cost,
    restored R simple (debt f d) C cp cost,
    WilsonOriginalOpticalCouplingFares.gain R simple cost (work n P f d+1+(wallet f).pole) C cp,
    WilsonOriginalOpticalCouplingFares.gain R simple cost (work n P f d+1) C cp,
    WilsonOriginalCensusChronologicalMoney.thermal R simple,WilsonOriginalOpticalCouplingBand.cold R simple 3]
    with b paidWallet paidRaw paidDebt payRent payJets heat frost
  intro N per K i bi ik live ratio
  have bt:=heat (i:=b) (N:=N) (per:=per) le_rfl (by omega)
  have it:=heat (i:=i) (per:=per) bi (by omega : i ≤ N)
  have ft:=heat (i:=i+1) (per:=per) (by omega) (by omega : i+1 ≤ N)
  have cool:=mul_le_mul_of_nonneg_right (frost N per (by omega)) bt.1.le
  rw [inv_mul_cancel₀ bt.1.ne'] at cool
  refine ⟨bt.1,cool,it.1,it.2,ft.1,ft.2,?_,?_,?_,?_,?_⟩
  · simpa only [pound,wallet,pow_zero,mul_one] using paidWallet bi (by omega : i ≤ K) bi (by omega : i ≤ K) live ratio (per:=per)
  · exact paidRaw bi (by omega) bi (by omega) live ratio (per:=per)
  · exact paidDebt bi (by omega) bi (by omega) live ratio (per:=per)
  · exact payRent (i:=i+1) (by omega) ik live ratio
  · exact payJets (i:=i+1) (by omega) ik live ratio

end YM.Integration.WilsonOriginalFullRosterCouplingClock
end
