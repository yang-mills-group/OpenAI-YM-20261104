import YM.FVAAlt2.Pipeline.Stays
import YM.FVAAlt2.Winder.Medium
/-! # IP.Conc.Color Gauge & Road spool. Program data and adaptive lengths not re-bought
 by adversarial p-witness. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline.Crown
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm
open Lattice RG Precision Comparison.RG02.Bulk Oracle Circuit
open PowerSeries
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
open Budget.FVAAlt2.Wind Budget.FVAAlt2.Wind.Pine
variable {G:Gauge} {X:Type} {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side} {Γ: History G}
open Period.Field
variable {C:Circuit M N}(Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (K: Comparison.RG02.Bulk.Chain Γ)(P: SeriesT C Q Γ)
variable (L:Page M→ Binding.Scale)(p:ℕ) -- period
variable (Γ) -- sometimes explicit
lemma periods (x:ℕ): Tendsto (fun p=> (Γ.S.side x p).val) atTop atTop:= tendsto_atTop_mono (f:=fun i:ℕ=>(Γ.S.period i).val) (fun _=> Nat.le_mul_of_pos_right _ (Γ.S.denominator x).property) Γ.S.period_strict.tendsto_atTop
variable {Γ}
def HaloA (i:ℕ): Arch (Foot G) atTop (fun w=> Pin (Γ.S.side i w) G):= arcP (linksQ G) _ (periods Γ i)
local notation:max "U_" p:max k:max => P.stepData C Γ p k
local notation:max "F_" p:max k:max => Halo.bios ( P.stepData C Γ p k )
local notation:max "K_" p:max k:max => ( P.readyKin C Γ K p k )
abbrev Fore (u:Flap M) := HaloA (Γ:=Γ) ( P.vol u.next+1 )
abbrev After (u:Flap M) := HaloA (Γ:=Γ) ( P.vol u.next )
abbrev StepA (u:Flap M) := (Fore P u).allSum (After P u)
local notation:max "d_" p:max i:max=> ( Arm.Pred (U_ p i) (F_ p i) (K_ p i) )
local notation:max "e_" p:max i:max=> ( Arm.night (U_ p i) (F_ p i) (K_ p i) )
include Φ in
lemma flex (k:Flap M): Arch.Baked ( Fore P k ) ( After P k ) ( C.sails Y G k ) fun p=> d_ p k:=by
 refine ⟨ fun w i=> funext ((See.stay Y Φ K P w k).1.1 i),fun w i=> funext (( See.stay Y Φ K P w k ).1.2 i) ⟩
-- Φ not in type! use include.
lemma flexZ (k:Flap M): Arch.Baked (Fore P k) (Fore P k) ( C.pulses Y G Φ k ) fun p=> e_ p k:= ⟨ fun w i=> funext ((See.stay Y Φ K P w k).2.1 i), fun w i=> funext ((See.stay Y Φ K P w k).2.2 i) ⟩
open Quadratic
lemma priced (G:Gauge)(k:Flap M): Billed ( C.sails Y G k ) ∧ Billed (swap ( C.sails Y G k )):= by
 let B:= C.honored Y k.prev; let H:= C.predicted Y k; exact ( overrides (C.pactP k) _ _ G H.rows B.card.pos.le H.costV ).buys B.card.pos.le
lemma pricedZ (k:Flap M): Billed ( C.pulses Y G Φ k ) ∧ Billed (swap (C.pulses Y G Φ k)):=by unfold Circuit.pulses; rw [t_warm]; exact ⟨ heatP .., heatP .. ⟩
open Lift
lemma tendersK (k:Flap M):
  aster atTop ( ( C.devices Y G Φ L k ).line ) (fun i=> shore ( (StepA P k).spring i ) ( (StepA P k).spring i ) (Arm.spins (U_ i k) (F_ i k) (K_ i k)) ) ∧
  aster atTop ( ( C.devices Y G Φ L k ).driftL ) (fun i=> shore ( (StepA P k).spring i ) ((StepA P k).spring i) (Arm.driftM (U_ i k) (F_ i k) (K_ i k)) ) :=
 ⟨Arch.Trust.petal (flexZ Y Φ K P k) (pricedZ Y Φ k).1 (pricedZ Y Φ k).2 (After P k),Arch.Trust.hose (flex Y Φ K P k) (priced Y G k).1 (priced Y G k).2 ⟩
end YM.RegulatorIR.FVAAlt2.Pipeline.Crown
