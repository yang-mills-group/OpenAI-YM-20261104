import YM.Qlocal.Feud.Tango
import YM.Qlocal.Davenport
import YM.Qlocal.Horn
/-!
 # Actual group maps used in the seed & output drift
 uniform Lecturing from the REAL Wilson patch & exponential. No dimensions in derivative prices.
 This is *actual-torus analytic continuation on the whole group chart family* (not a
 positivity estimate on curvature-path/orientation half deck). Field dims in polynomials denomin later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
namespace Campus
open Quipu.Sonnet
variable (F:Forest S.ratio) (h:PaintSupply G k b)
local notation "E"=> Apex c G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "U"=> (E × Y)
local notation "I"=> ℝ × (E × Y)
local notation "Z"=> Positions (Uniform.Joint F G)
local notation "W"=> ℝ×E
include h F
noncomputable abbrev spaceL:I→L[ℝ]Z:=(Lapis.combineH (G:=G) F).toContinuousLinearMap ∘L ContinuousLinearMap.snd ℝ ℝ _
noncomputable abbrev omni (G:Gauge) (F:Forest S.ratio) (x:ℝ×(Apex c G × Poll.Body (Precision.Key F G))) := Work.F03.live F ((Binding.gaugeL (G:=G) F x).2)
omit h in
lemma wall (x:I): omni G F x= fine G F (spaceL F x):= rfl
-- same h.H used to pay.Weights.W⟶Rank.Local. no zoom cost on θ field in group itself unscaled.
abbrev speedV (G:Gauge)(k:ℕ)(b:ℝ):=1+composeCost k (fineCost G k b) 1
local notation "δ"=> composeCost k (fineCost G k b) 1
lemma hikes : 1≤ speedV G k b:= le_add_of_nonneg_right (by unfold composeCost; have hp:= h.1; have hh:0≤ fineCost G k b:= (fine_supply F h).2.1; positivity)
omit h in
lemma gaugeLFee : ‖spaceL (G:=G) F‖≤1:= by
 unfold spaceL; apply (ContinuousLinearMap.opNorm_comp_le ..).trans; exact mul_le_of_le_one_left (norm_nonneg _) (feesComb (G:=G) F)|>.trans (ContinuousLinearMap.norm_snd_le ..) -- wrong param? opNorm mul.
lemma human (x:I)(hx:‖x‖≤1): Weather (omni G F) x∧ Mode (omni G F) x k (speedV G k b):= by
 let g:= spaceL (G:=G) F; let d:=δ; have hh:‖g x‖≤1:= (ContinuousLinearMap.le_of_opNorm_le g (gaugeLFee F) x).trans (by simpa only [one_mul] using hx)
 have hg(i): Allows k (fun v=> G.mat (omni G F v i)) x d:= by simp_rw [wall]; exact ((fine_supply F h).2.2 i (g x) hh).comp (allows_linear (gaugeLFee F) hh)
 refine ⟨fun i=>(hg i).analytic,(zero_le_one.trans (hikes F h)),fun j=>?_⟩; have ho:Brush k d 1 (fun v=>G.mat (omni G F v j)) x:= Brush.offer.2 ⟨((hg j).analytic.of_le le_top),(hg j).norm_le⟩; simpa only [speedV,mul_one] using! thicken (f:=fun v=> omni G F v j) ho
omit F
abbrev outerV (G:Gauge)(k:ℕ)(b:ℝ):=1+outerCost G k b
noncomputable def oracle (G:Gauge) (n:Side)(x:ℝ× Apex n G): Config G n:= Desk.night x.2
lemma whole (x:W)(hx:‖x‖≤1): Weather (oracle G c) x ∧ Mode (oracle G c) x k (outerV G k b):= by
 have he:=h.1; let X(i : Bond c): (ℝ × Apex c G) →L[ℝ] G.Color:= ContinuousLinearMap.proj (φ:=fun _ : _=>G.Color) (i.1, _root_.YM.Exterior.coord i.2) ∘L ((tint G _).toContinuousLinearMap ∘L ContinuousLinearMap.snd ℝ ℝ (Apex c G)) -- Exterior? coords.
 let s:= shade G
 let d:= outerCost G k b
 have hp i:‖X i‖ ≤ shade G:= ContinuousLinearMap.opNorm_le_bound _ (shade_pos _).le fun y=> (le_trans (norm_le_pi_norm ((tint G _) y.2) ((i:Bond c).1,_root_.YM.Exterior.coord i.2)) <| (tint_le (y.2)).trans (mul_le_mul_of_nonneg_left (norm_snd_le y) (shade_pos _).le))
 have ht (i): Allows k (fun v=> G.mat (oracle G c v i)) x d := by
    have hZ : ‖X i x‖ ≤ s:= (ContinuousLinearMap.le_of_opNorm_le (X i) (hp i) x).trans (mul_le_of_le_one_right (shade_pos _).le hx); simp_rw [oracle,Desk.night,Work.F03.represent_link]; exact (h.2 (X i x) hZ).comp (allows_linear (hp i) hZ)
 refine ⟨fun i=>(ht i).analytic,add_nonneg zero_le_one ((outer_pos G _ h.1).le),fun i=>?_⟩; have ho := thicken (f:=fun v=>oracle G c v i) (Brush.offer.2 ⟨(ht i).analytic.of_le (show (↑k:WithTop ℕ∞) ≤ ω from le_top),(ht i).norm_le⟩); simpa only [outerV,mul_one] using! ho
end Campus
end YM.Qlocal.Feud
