import YM.MS.Vane.Bee
import YM.WiderProfiles.Rake.Hour
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Vane/Bee.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I E W:Type}{G:Gauge}{P:Geo I}{x E':ℝ} {b:Bool}{F H:Glade G I}{X: I→QP}{Y:Recount G}{n k l h:ℕ}[DecidableEq W]{s:Finset W}
 {K L:Planet G I}
local notation "℧"=> Gulf P
lemma lighting_wide (hs:Sheet (℧).price 1 (plug L))(hx:WCoverSep P X)(hp:Here false true ℧ F (rateS ℧ n))(he:Here false true ℧ H ( rateS ℧ k )) : Bud P (n+k) 0 (regionC (fun _=>planeF) X L F H):= by
    intro j; obtain ⟨a,ha,hA⟩:= hx.floor; refine Lease.sticks ( PulseQ (v:=fun i=>P.roots i.1) (A:=X ∘ Sigma.fst) hs hp he (fun _=>zero_le_one) ( rateC _ _ ) (rateC _ _ ) (fun _=>exp_pos _) (fun i=> hA i.1) (fun i=> le_trans ( le_of_eq ( near i ) ) ( exp_monotone ( authority i|>.2 ))) (hx.pay ℧ (fun _ => rfl) (fun _ => le_rfl)) ha j ) ?_; intro i; rw [dotzero, dotzero, roll, Pi.one_apply,one_mul, ← stock,zero_add, add_zero, Nat.zero_add]; -- dotzero hidden eta etc.
end YM.MS.Vane
