import YM.Integration.WilsonOriginalBornLedger
import YM.Integration.WilsonOriginalSignedFreshPermit
import YM.Integration.WilsonMixedReceivedShifts

/-! The original second tap accepts a separately addressed born source after projecting
the entire previously filed first tap onto the old test. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedWalletSecondPost
open Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Shelter
open Finset Function Push Push.AbsoluteSums Next.Foundations QuadraticLocal.Travel
open Kiosk Canopy WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open WilsonMixedTestTableau WilsonMixedPassportRows
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {V I₀ I₁ J₁ T:Type} [DecidableEq V] [Fintype V]
  [Countable I₀] [Countable I₁] [Countable J₁] [Countable T]
  {C:Census V} (P Q:Passport n V) (W:Rep G n) {F₀:Activities G n}
  {E F:V → Type} [∀v,AddCommGroup (E v)] [∀v,AddCommGroup (F v)]
  [∀v,Module ℝ (E v)] [∀v,Module ℝ (F v)]
  (A:∀v,Set (E v)) (B:∀v,Set (F v)) (K:∀v,Submodule ℝ (E v)) (L:∀v,Submodule ℝ (F v))
  (old:Finset V) (zeroA:∀v,0∈A v)
local notation "projected" => left A B old zeroA
local notation "joint" => passport (owner P Q old)
local notation "wallet" => Wallet (actors A B)
variable {incoming output spare:ℝ}
  (H:Hard (Wallet A) W.p F₀.forced F₀.K P.origin C)
  (D:Kiosk.Second W.p F₀ W.activities incoming output W.p.supportExponent spare)
  (M:ShiftRows (Wallet A) J₁ G W.p P.origin C)
  (crown:Crown P.support A K H)
  (shifts:∀i U,Stencil P.support A K (M.place i).val (fun t=>M.soap t i U))
  (born:Lamps (Wallet (actors A B)) I₀ G W.p (passport (owner P Q old)).origin C)
  (filed:Lamps (Wallet (actors A B)) I₁ G W.p (passport (owner P Q old)).origin C)
  (debt:Lamps (Wallet (actors A B)) T G W.p (passport (owner P Q old)).origin C)

local notation "movedHard" => WilsonMixedReceivedHard.posted (Q:=Q) A B K old zeroA H crown
local notation "movedShifts" => WilsonMixedReceivedShifts.posted (Q:=Q) A B K old zeroA M shifts
local notation "growing" => W.p.supportExponent
local notation "fullWidth" => (growing+1+1)

include D crown shifts
omit [Countable I₁] in
theorem received {w u:V→ℝ} (hw:∀v,0<w v) (hu:∀v,0<u v) (fits:∀v∈old,u v ≤ w v)
    {fromOld fromBorn analytic regular fresh:ℝ}
    (first:H.Paid w W.p.B (growing+1) incoming)
    (previous:M.Budget w W.p.B (growing+1) fromOld)
    (earned:filed.Paid u W.p.B fullWidth analytic) (rent:debt.Paid u W.p.B fullWidth regular)
    (paid:born.Paid u W.p.B fullWidth fresh) (gross:Gross born u W.p.B (growing+1) fromBorn)
    (onBorn:Taut (joint).support (actors A B) (pieces K L) born)
    (onFiled:Taut (joint).support (actors A B) (pieces K L) filed)
    (onDebt:Taut (joint).support (actors A B) (pieces K L) debt)
    (slack:0<spare) (extra:ℝ) (Y μ : Wallet A → Config G n → Poly C)
    (read:ReadZone (Wallet A) W.p F₀ H Y μ)
    (phase:∀t U,μ (projected t) U=filed.log t U+debt.log t U+M.log (projected t) U)
    (empty:∀t U,(μ t U).part C.quiet=0) (quiet:∀t U,(Y t U).part C.quiet=(W.eval U:ℂ))
    (positive:∀U,W.eval U≠0) :
    let h:=WilsonRootedKioskFreeRadius.radius extra fromOld fromBorn spare
    WilsonOriginalBornLedger.priced W joint C (actors A B) (pieces K L) born filed
      u (Stoop.radius u h) regular output (fun t=>Y (projected t)) := by
  intro h
  have one:1 ≤ h:=(le_max_left 1 extra).trans (le_max_left _ _)
  have upper:(fromOld+fromBorn)/spare ≤ h:=le_max_right _ _
  have room:h⁻¹*fromOld+h⁻¹*fromBorn ≤ spare:=by
    rw [←mul_add,mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ (zero_lt_one.trans_le one)).mpr (by simpa only [mul_comm] using (div_le_iff₀ slack).mp upper)
  have more:0 ≤ fullWidth:=by linarith [W.p.exponent_pos]
  have low:growing ≤ fullWidth:=by linarith
  have allOld:=Lamps.joinPaid earned rent
  have regularFee:=Lamps.joinPaid (born.tenure u hu paid low) ((filed.join debt).tenure u hu allOld low)
  have held:=WilsonMixedReceivedHard.paid (Q:=Q) A B K old zeroA H crown hw hu fits first
  have oldShift:=WilsonMixedReceivedShifts.paid (Q:=Q) A B K old zeroA M shifts hw hu fits previous
  have newShift:=WilsonOriginalSignedFreshPermit.shade_gross born gross
  have observed : ReadZone (wallet) W.p F₀ (movedHard) (fun t=>Y (projected t)) (fun t=>μ (projected t)) :=
    fun t U=>read (projected t) U
  have lines (t) (U) : μ (projected t) U= born.shade.log t U +
      (born.join (filed.join debt)).log t U+(movedShifts).log t U := by
    exact WilsonOriginalSignedFreshPermit.phase_add (phase t U) (Lamps.shade_log born t U)
      (Lamps.joinLog t U (paid.sums more hu ..) (allOld.sums more hu ..))
      (Lamps.joinLog t U (earned.sums more hu ..) (rent.sums more hu ..)) rfl
  have outcome:=WilsonRootedKioskPostedPortfolio.received (movedHard) D born.shade (born.join (filed.join debt))
    (movedShifts) (Stoop.radius u h) (fun v=>div_pos (hu v) (zero_lt_one.trans_le one)) W.p.exponent_pos.le
    (Stoop.leaves u (movedHard) hu one held)
    (Stoop.tighten u (born.join (filed.join debt)) hu one regularFee)
    (WilsonRootedKioskFreeRadius.moved (movedShifts) hu one oldShift)
    (WilsonRootedKioskSlipCharge.cost born.shade hu one newShift) room
    (fun t=>Y (projected t)) (fun t=>μ (projected t)) observed lines hu
    (by linarith [W.p.exponent_pos]) newShift (fun t=>empty (projected t)) (fun t=>quiet (projected t)) positive
  have collars:=WilsonMixedFreshMergerCrown.posted (actors A B) (pieces K L) (joint).support
    (movedHard) D (filed.join debt) born (movedShifts)
    (WilsonMixedReceivedHard.collared (Q:=Q) A B K L old zeroA H crown)
    (Polish.Static.spawn onFiled onDebt) onBorn
    (WilsonMixedReceivedShifts.collared (Q:=Q) A B K L old zeroA M shifts)
  refine ⟨T,inferInstance,⟨debt,_⟩,rent,outcome.1.wages,onDebt,collars.hard,?_,outcome.2.2⟩
  intro t U
  have eq:=(congrFun (outcome.2.1 t) U).symm
  unfold WilsonRootedKioskWithdrawal.output at eq
  rw [WilsonOriginalSignedFreshPermit.shade_bare,neg_neg] at eq
  exact eq

end YM.Integration.WilsonMixedWalletSecondPost
