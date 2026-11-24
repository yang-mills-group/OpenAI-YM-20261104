import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
import YM.WiderProfiles.Rake.Cluster
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Rake/Sequence.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{ P: Geo I}{B:Local.Physical.Deck G}{O:Land.Booked B}{M: Land.MS_Data G O}
variable (V:LitBook B) (P:Geo I)(T: Prescription B)(M: Land.MS_Data G O)
structure WTour (K L: Planet G I)(P:Geo I)(x:Position W I) (b:Bool)(Y:Site G I)(H: W→ Site G I)(sizes:W→ℕ): Prop where
    plot: WMesh P x
    ground: Stage K L P b
    energy i : 0< i → Tip P b true 4 ( Y i )
    obey i n: Tip P b false (sizes i) (H i n)
    register s: Ven (fun _=> planeF ) K L Y (H s)
variable {P}{x:Position W I} (R: WMesh P x) (labels:W→ Label B) -- declare x
include R
omit [LinearOrder W] in
lemma builder_wide : WTour (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) P x false (approach P M) (rowM P M ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterD .., fun _ _=> tagD P M _, fun i n=>tagF P M (labels i) n,fun i=>VeniceD P M ( labels i ) ⟩
end YM.MS.Rake
