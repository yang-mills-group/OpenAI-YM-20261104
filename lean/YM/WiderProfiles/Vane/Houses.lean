import YM.MS.Vane.Houses
import YM.WiderProfiles.Rake.Hour
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Vane/Houses.lean`.
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
variable { I W: Type}{G:Gauge}{P: Geo I}{S:Belt I}{x:ℝ}{K L K' L': Planet G I} {b c:Bool}{F H X Y:Glade G I}
 {ξ:I→QP} {d r k:ℕ}
local notation "Ϋ"=> Gulf P
lemma River_wide {a b c:Stem P→ℝ}(hc: WCoverSep P ξ)(he: Flow Ϋ K a)(hg: Here false true Ϋ F b)(hv: Here false true Ϋ H c)(ht:nn a)(hm:nn b)(hN:nn c)(l:ℕ): Here false false Ϋ ( regionC (fun _=>planeF) ξ K F H ) ( fun p=>a p*(b p*c p) * ( ( Gulf P ).price.length p / P.roots p.1 ) ^ l ) := by obtain ⟨C,hC,hW⟩:= hc.floor; apply PulseQ (A:=fun p=> ξ p.1) he hg hv ht hm hN (fun p=> exp_pos _) (fun i=> hW i.1) (qp_le) (hc.pay (Gulf P) (fun _ => rfl) (fun _ => le_rfl)) hC
lemma boats_wide (hc: WCoverSep P ξ)(he:Flow Ϋ L 1)(hf: Flow Ϋ (L-L') (chips (Gulf P))) (hu: Here false true Ϋ F (rateS Ϋ d))(hH:Here false true Ϋ H ( rateS Ϋ d )) (hp: Here false true Ϋ ( F-H ) (chips Ϋ*rateS Ϋ d ))( hv: Here false true Ϋ Y (rateS Ϋ r))( ht: Here false true Ϋ ( X-Y ) (chips Ϋ*rateS Ϋ r)) (hw:Warm H false)(hw':Warm F false)(hV:Warm X false)(hV': Warm Y false)(hb: BackF L)(hh:BackF L'): Bud P (d+r) eps_gain ( regionC (fun _=>planeF) ξ L F X-regionC (fun _=>planeF) ξ L' H Y ) := by
   intro k; refine parkD hu hH hp hv ht hw hw' hV hV' hb hh (fun _=>Coherent) ?_ ?_ ?_; all_goals intro B T h1 h2
   · apply Lease.sticks (River_wide hc he h1 h2 (fun _=>zero_le_one) (rateC _ _) (joy cul (rateC _ _)) k ); intro p; trans chips Ϋ p * life P (d+r) k 0 p; apply le_of_eq; rw [show k= (0:ℕ)+k from (by simp), stock 0, ← (by simpa using roll (P:=P) (x:=0) (η:=0) d r 0 0 p : life P d 0 0 p*life P r 0 0 p=life P (d+r) 0 0 p )]; try simp only [Pi.one_apply,Pi.mul_apply];
     rw [congr_fun (dotzero (P:=P) d) p, congr_fun (dotzero (P:=P) r) p,zero_add]; ring
     exact (congr_fun (alter P (d+r) k) p).ge
   · apply Lease.sticks (River_wide hc he h1 h2 (fun _=>zero_le_one) (joy cul (rateC _ _)) (rateC _ _) k ); intro p; trans chips Ϋ p * life P (d+r) k 0 p; apply le_of_eq; rw [show k=(0:ℕ)+k from (by simp), stock 0, ← (by simpa using roll (P:=P) (x:=0) (η:=0) d r 0 0 p : life P d 0 0 p * life P r 0 0 p=life P (d+r) 0 0 p )]; try simp only [Pi.one_apply,Pi.mul_apply];
     rw [congr_fun (dotzero (P:=P) d) p, congr_fun (dotzero (P:=P) r) p,zero_add]; ring
     exact (congr_fun (alter P (d+r) k) p).ge
   apply Lease.sticks (River_wide hc hf h1 h2 cul ( rateC _ _ ) ( rateC _ _ ) k); intro p; trans chips Ϋ p * life P (d+r) k 0 p; apply le_of_eq; rw [show k=(0:ℕ)+k from (by simp), stock 0, ← (by simpa using roll (P:=P) (x:=0) (η:=0) d r 0 0 p : life P d 0 0 p*life P r 0 0 p=life P (d+r) 0 0 p ) ]; 
   rw [congr_fun (dotzero (P:=P) d) p, congr_fun (dotzero (P:=P) r) p,zero_add]; ring
   exact (congr_fun (alter P (d+r) k) p).ge
end YM.MS.Vane
