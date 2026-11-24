import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Cluster
import YM.WiderProfiles.Rake.Hour
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Rake/Cluster.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open Book.Convolve Geo
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}
def WMesh (P:Geo I)(x:Position W I): Prop:= ∀ i j:W,i≠j→ WCoverSep P (x i - x j)
variable {x:Position W I}{P:Geo I}{K L:Planet G I}{X Y: Dance G I W}{F:Site G I}{s t:Finset W}{w:W}{G':W→ Site G I}{b:Bool}
lemma space_wide (h:WMesh P x) (ht:t∈picks s): WCoverSep P ( rootX x t-rootX x s ):= by obtain ⟨hh,hT,H⟩:= n_small ht; let p:=s\ t; have hx:= H.1; rw [unfT x ht,rootX, rootX,dif_pos hT,dif_pos hx]; refine h _ _ ?_; intro he; exact (( mem_sdiff.mp ( min'_mem p hx)).2) ( he ▸ min'_mem t hT )
end YM.MS.Rake
