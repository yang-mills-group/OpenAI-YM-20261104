import YM.Integration.WilsonMatrixTicketLanesVacuumKeptTable
import YM.Integration.WilsonMatrixTicketLanesVacuumPanel

/-! The actual earlier hard score, its two proper lower marginals, and
all five pieces integrated over the single signed physical Ward test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumKeptWave
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker OPE.Therm
open IterationFour.Vacuum PhysicalNext.Repeat.Legato WilsonInvariantActionRegisteredHearing
open WilsonInvariantActionPriorHearing WilsonMatrixTicketLanesRegisteredHearing WilsonRegisteredPriorTables
open WilsonMatrixTicketLanesVacuumPanel
open RG.Supply Pressure Extra.Histories PhysicalNext.Repeat
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared GapsLocal.Renew
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {N per m:ℕ} (interior:m+1<N) (d:ℕ)
local notation "Ω" => Config G (R.family.side m per) × Config G (R.family.side (m+1) per)
local notation "Sites" => Fin 2 → Site (R.family.side N per)
local notation "μ" => prior G (R.family.side m per)
local notation "P" => R.family.path.rep N per m
local notation "Z" => partition G (R.family.side N per) (R.family.path.β N per N)
local notation "D" => WilsonMatrixTicketLanesVacuumKeptTable.deposited R interior d
local notation "W" i:max => score R interior (hard R interior i)
local notation "live" => Nat.lt_trans (Nat.lt_succ_self m) interior

def lower (i:ℕ) (a b:readings Ω):ℝ:=
  let I:=conditional R (p:=per) live
  let L:=earlier R (p:=per) live
  let α:=L (I a)
  let β:=L (I b)
  let c:=L (I (a*b))-α*β
  Z⁻¹*∫V,(D i 1 V/(P).eval V)*
    (row R (N:=N) (a*b) V-α*row R (N:=N) b V-β*row R (N:=N) a V+(α*β-c)*(P).eval V) ∂μ

def all (i:ℕ) (a b:readings Ω):ℝ:=
  let J:=joint R (p:=per) live
  let α:=J a
  let β:=J b
  let c:=J (a*b)-α*β
  Z⁻¹*∫V,(D i (a*b) V-α*D i b V-β*D i a V+(α*β-c)*D i 1 V) ∂μ

private theorem add (birth:R.family.ref 4 ≤ m + 1) (v:Fin 2→R.family.label 4)
    (φ:Test 2) (χ:ℂ→L[ℝ]ℝ) (A B:Sites → readings Ω → readings Ω→ℝ):
    panel R live birth v φ χ A+panel R live birth v φ χ B=
      panel R live birth v φ χ (A+B):=by
  unfold panel
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  unfold channel
  dsimp only [Pi.add_apply]
  ring

theorem fixed (h:OriginalMarkedRunAction.Comparison R (p:=per) interior d)
    (birth:R.family.ref 4 ≤ m + 1) (v:Fin 2→R.family.label 4) (φ:Test 2) (χ:ℂ→L[ℝ]ℝ) (select:Sites→ℕ):
    let w:=fun x=>W (select x)
    signed R .previousCovariance live birth v φ χ w+signed R .previousCumulant live birth v φ χ w=
      panel R live birth v φ χ (fun x=>lower R interior d (select x)) ∧
    signed R .all live birth v φ χ w=
      panel R live birth v φ χ (fun x=>all R interior d (select x)):=by
  intro w
  unfold signed
  rw [add R interior]
  constructor
  · apply congrArg (panel R live birth v φ χ)
    funext x a b
    exact WilsonMatrixTicketLanesVacuumKeptTable.earlier R interior d h (select x) a b
  · apply congrArg (panel R live birth v φ χ)
    funext x a b
    exact WilsonMatrixTicketLanesVacuumKeptTable.response R interior d h (select x) a b

theorem purchased (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (n:ℕ):
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,∀j:m+1<N,∀birth:R.family.ref 4 ≤ m + 1,
    ∀v:Fin 2→R.family.label 4,∀φ:Test 2,∀χ:ℂ→L[ℝ]ℝ,∀select:(Fin 2→Site (R.family.side N per))→ℕ,
    let l:m<N:=Nat.lt_trans (Nat.lt_succ_self m) j
    let w:=fun x=>score R j (hard R j (select x))
    signed R .previousCovariance l birth v φ χ w+signed R .previousCumulant l birth v φ χ w=
      panel R l birth v φ χ (fun x=>lower R j n (select x)) ∧
    signed R .all l birth v φ χ w=panel R l birth v φ χ (fun x=>all R j n (select x)):=by
  obtain ⟨b,paid⟩:=eventually_atTop.mp (OriginalMarkedRunAction.calendar R simple marks fee n)
  filter_upwards [eventually_ge_atTop b] with m ready N per j birth v φ χ select
  exact fixed R j n (paid (m+1) (by omega) N per j) birth v φ χ select

end YM.Integration.WilsonMatrixTicketLanesVacuumKeptWave
