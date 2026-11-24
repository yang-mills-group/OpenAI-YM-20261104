import YM.MS.Vane.Trigger
import YM.WiderProfiles.Vane.Zever
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Vane/Trigger.lean`.
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
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D: Glade G I}{X:I→ℂ}{d h:ℕ}{ζ:ℝ}
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
variable (h₂:WTour K L P x b B A R)(hx:WTour K' L' P x c B' A' R)
    (M: Arch ( Gulf P ) K L B A R) (M':Arch ( Gulf P ) K' L' B' A' R)(N:Arch (West P) K L B A R)(N': Arch ( West P ) K' L' B' A' R)(Z:ArcS ( Gulf P ) K L K' L' B B' A A' R)(Z':ArcS ( West P ) K L K' L' B B' A A' R)
include h₂ M N
lemma closure_wide (H:Fields x m0 K L B A U)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) 0 ( U S n ):= by
    obtain he:= motion_wide h₂ H hp n; obtain hu:= recall_wide h₂ M N H hp n; obtain ⟨hv,hz⟩:= saleable he hu; have H':= moon_wide h₂ H M hp n|>.1; rw [dotzero] at H'; exact ⟨ hv,hz,titel H' hu he ⟩
include hx M' N' Z Z'
lemma trade_wide (H:Fields x m0 K L B A U) (H': Fields x m0 K' L' B' A' V)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) eps_gain ( U S n-V S n ):= by
   let T:WChase P x m0 R b K L B A U:= ⟨ h₂,H ⟩; let T':WChase P x m0 R c K' L' B' A' V:= ⟨ hx,H' ⟩; obtain hm:= economics_wide T T' Z M M' N N' Z' S hp n; obtain ht:= tokens_wide T T' M M' Z S n hp|>.1; rw [dotzero, ← alter] at ht; have hv:= Fits.subFit ( motion_wide h₂ H hp n ) ( motion_wide hx H' hp n ); obtain ⟨ hU,hW⟩:= saleable hv hm; exact ⟨ hU,hW,titel ht hm hv ⟩
end YM.MS.Vane
