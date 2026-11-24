import YM.Integration.WilsonMixedWalletMeasuredRestamp
import YM.Integration.WilsonMixedReceivedRendered
import YM.QuadraticLocal.Earn.Temp

/-! Re-enter the independently filed, measured old-plus-born roster.  The
incoming for its next physical block uses the actual hard wallet of the second
tap.  The equality includes the signed rough configurations. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedWalletFiledInput
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums Next.Foundations ConnectedActivityE6
open WilsonMixedTestTableau WilsonMixedPassportRows
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V I J N:Type} [DecidableEq V] [Fintype V]
  {P Z:Passport n V} (W:Rep G n) {R:Census V} {F F₁:V → Type}
  [∀v,AddCommGroup (F v)] [∀v,Module ℝ (F v)] [∀v,AddCommGroup (F₁ v)] [∀v,Module ℝ (F₁ v)]
  (A:∀v,Set (F v)) (B:∀v,Set (F₁ v)) (K:∀v,Submodule ℝ (F v)) (L:∀v,Submodule ℝ (F₁ v))
  (old fresh:Finset V) (apart:Disjoint old fresh) (zA:∀v,0∈ A v) (zB:∀v,0∈B v)
  (born:Lamps (Wallet (actors A B)) I G W.p (passport (owner P Z old)).origin R)
  (X:J → Row P R G (Wallet A)) (Q:N → Row Z R G (Wallet B))
local notation "joint" => passport (owner P Z old)
local notation "angle" => Coat.gStep W.beta
local notation "prior" => rendered X W.p angle
local notation "new" => rendered Q W.p angle
local notation "previous" => WilsonMixedReceivedLamp.regular (P:=P) (Q:=Z) (W:=W) A B old zA prior
local notation "filed" => WilsonMixedFaceLog.routed X Q old fresh apart (left A B old zA) (right A B fresh zB)
local notation "width" => (W.p.supportExponent+1+1)
variable {w wX wQ:V → ℝ} {feeX feeQ regular hard support:ℝ} (h:ℝ) (one:1 ≤ h)
  (nativeHard:Hard (Wallet A) W.p W.activities.forced W.activities.K P.origin R)
  (eligible:Crown P.support A K nativeHard)
  (stock:Tableau K A X) (newStock:Tableau L B Q)
  (positiveOld:∀v,0<wX v) (positiveNew:∀v,0<wQ v)
  (oldRent:(rendered X W.p (Coat.gStep W.beta)).Paid wX W.p.B (W.p.supportExponent+1+1) feeX)
  (freshRent:(rendered Q W.p (Coat.gStep W.beta)).Paid wQ W.p.B (W.p.supportExponent+1+1) feeQ)
  (active:born.Paid w W.p.B (W.p.supportExponent+1+1) support)
  (fit:∀ v∈old,w v ≤ wX v)
  (birth:∀t U,born.log t U=(rendered Q W.p (Coat.gStep W.beta)).log (right A B fresh zB t) U)
  (Y:Wallet (actors A B) → Config G n → Poly R)
  (admitted:WilsonOriginalBornLedger.priced W (passport (owner P Z old)) R (actors A B) (pieces K L) born
    (WilsonMixedReceivedLamp.regular (P:=P) (Q:=Z) (W:=W) A B old zA (rendered X W.p (Coat.gStep W.beta)))
    w (Stoop.radius w h) regular hard Y)

include eligible stock newStock oldRent freshRent active positiveOld positiveNew fit birth admitted one in
theorem received {t:V → ℕ} {s b:ℝ} {r load k:ℕ}
    (grant:Scene.Armada filed w t s b r load k) {sigma toll:ℝ}
    (atDate:Invoice.Supports W.p sigma width angle s toll) :
    ∃ (C:Type), Countable C ∧ ∃ next:Tint.Incoming joint W (Wallet (actors A B)) C R,
      Scene.Armada filed (Stoop.radius w h) t s (h⁻¹*b) r load k ∧
      Tableau (pieces K L) (actors A B) filed ∧
      next.old.Paid (Stoop.radius w h) W.p.B width (h⁻¹*regular) ∧
      next.hard.Paid (Stoop.radius w h) W.p.B W.p.supportExponent hard ∧
      Taut (joint).support (actors A B) (pieces K L) next.old ∧
      Crown (joint).support (actors A B) (pieces K L) next.hard ∧
      (∀ t₀ U,(Tint.Patrol.picture filed next).density t₀ U =
        Poly.pass (WilsonRootedKioskOccupiedSlip.bare born t₀ U)*Y t₀ U) ∧
      ∀ t₀ U,((Tint.Patrol.picture filed next).density t₀ U).part R.quiet=(W.eval U:ℂ) := by
  obtain ⟨C,counted,next,paid,hardPaid,enrolled,cleared,full,quiet⟩:=admitted
  letI : Countable C:=counted
  have positive:=grant.positive
  have nonnegative:0 ≤ width:=by linarith [W.p.exponent_pos]
  have signed:=WilsonMixedReceivedLamp.heard (Q:=Z) A B K L old zA (prior) nativeHard eligible
    (stock.line W.p angle) positiveOld nonnegative oldRent
  have projected:=WilsonMixedReceivedLamp.paid (Q:=Z) A B old zA (prior) positive fit oldRent
  have both:=Scene.Armada.paid filed w t grant W.p atDate
  have same (t₀:Wallet (actors A B)) (U:Config G n) :
      ((rendered filed W.p angle).join next.old).log t₀ U=(born.join ((previous).join next.old)).log t₀ U := by
    rw [Lamps.joinLog _ _ (both.sums nonnegative positive t₀ U) (paid.sums nonnegative positive t₀ U),
      Lamps.joinLog _ _ (active.sums nonnegative positive t₀ U) ((Lamps.joinPaid projected paid).sums nonnegative positive t₀ U),
      Lamps.joinLog _ _ (projected.sums nonnegative positive t₀ U) (paid.sums nonnegative positive t₀ U),
      signed.2,birth]
    rw [WilsonMixedReceivedRendered.previous A B K L X Q W.p angle old fresh apart zA zB stock newStock t₀ U
      (oldRent.sums nonnegative positiveOld _ U) (freshRent.sums nonnegative positiveNew _ U)]
    abel
  have field (t₀:Wallet (actors A B)) (U:Config G n) :
      (Tint.Patrol.picture filed next).density t₀ U=
      (⟨born.join ((previous).join next.old),next.hard⟩:Gallery (Wallet (actors A B)) _ (joint).origin W R).density t₀ U := by
    unfold Gallery.density
    change _ • (Poly.pass (((rendered filed W.p angle).join next.old).log t₀ U)*_) =
      _ • (Poly.pass ((born.join ((previous).join next.old)).log t₀ U)*_)
    rw [same t₀ U]
    rfl
  refine ⟨C,counted,next,grant.stored one,WilsonMixedTestTableau.original A B K L X Q old fresh apart zA zB stock newStock,
    Stoop.tighten w next.old positive one paid,hardPaid,enrolled,cleared,fun t₀ U=>(field t₀ U).trans (full t₀ U),?_⟩
  exact fun t₀ U=>(congrArg (fun a:Poly R=>a.part R.quiet) (field t₀ U)).trans (quiet t₀ U)

end YM.Integration.WilsonMixedWalletFiledInput
