import YM.QuadraticLocal.Campaign.Homes
import YM.Integration.WilsonRootedKioskOccupiedSlip

/-! The receiving ledger for a fresh source, its complete prior and the common
measured Wilson vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBornLedger
open Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Affinity QuadraticLocal.Earn
open scoped Classical
variable {G:Gauge} {n:Side} {V I J:Type} [DecidableEq V] [Fintype V]
  (W:Rep G n) (P:Passport n V) (R:Census V)
  {Film:V→Type} [∀v,AddCommGroup (Film v)] [∀v,Module ℝ (Film v)]
  (A:∀v,Set (Film v)) (K:∀v,Submodule ℝ (Film v))
  (born:Lamps (Wallet A) I G W.p P.origin R) (filed:Lamps (Wallet A) J G W.p P.origin R)
  (w u:V→ℝ) (regular hard:ℝ) (Y:Wallet A → Config G n → Poly R)

def priced : Prop := ∃ (C:Type),Countable C ∧ ∃ next:Tint.Incoming P W (Wallet A) C R,
   next.old.Paid w W.p.B (W.p.supportExponent+1+1) regular ∧
   next.hard.Paid u W.p.B W.p.supportExponent hard ∧
   Taut P.support A K next.old ∧ Crown P.support A K next.hard ∧
   let O : Gallery (Wallet A) (I⊕J⊕C) P.origin W R := ⟨born.join (filed.join next.old),next.hard⟩
   (∀ t U,O.density t U=Poly.pass (WilsonRootedKioskOccupiedSlip.bare born t U)*Y t U) ∧
   ∀ t U,(O.density t U).part R.quiet=(W.eval U:ℂ)

end YM.Integration.WilsonOriginalBornLedger
