import YM.OPE.Compatible.Oasis.Pure
import YM.OPE.Compatible.Kyoto.Orbs
import YM.OPE.Compatible.Oasis.Ball
import YM.OPE.Compatible.Kyoto.Ploy
import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Cloud
import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Opal
import YM.OPE.Compatible.Kyoto.TreeQ
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Upper rate of the discrepancy between coefficient observations

The two lower bounds on the coarse period supply the threshold in
`ships` and the reciprocal-period estimate in `SlopeW`. For matched
coefficient densities and `-11/10 < v < v'`, `StaveK` uses these bounds
and the two stage grants to bound the fine-to-coarse operator discrepancy
at upper rate `v'` on the coarse clock.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J :Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
namespace MatchZ

section
open Lass.Zest Lass PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel
variable {Ξ:Medal P' G K.K P'.J} {P₀:Teller G}
variable {E:ConnectedActivityE6.Target G P₀} {Q:Side}{W C κ:ℝ}{o:ConnectedActivityE6.Target.Order G W}
variable (F:I→Mug P' p p' T j R Ξ)
variable {Q:ℕ}
open Limn CardinalQ Labels Source Cameo Spells Yolk Pill
open Next.Scheduling
variable {X₀:Uniform G P'}
variable (N:Foyer L hs a l (d+6)){hp:highStage L hs a N≤ P'.J}{hz:highStage L hs a N ≤ j}
variable {M:Cab T j p}{β:I→ℝ}{l₀:Filter I}
variable {T1 T2:RG.Stage}(W:∀ i, Pillar X₀ (F i) (β i)) (h:Tendsto β l₀ atTop) (hc:∀ i,Aud X₀ (F i) T1 T2 (β i) (W i))
local notation "ζ"=> Eve W
local notation "Γ"=>βM ζ
variable (hZ:Mag P'.J j)(hb:P'.L=N.pay.st.S.L^m)
variable (Y₀:BankW L hs a N hp p)(C₀:BankW L hs a N hz p')

section
variable {A:Labels.Frame G l}{S:SectionData A}{U₀:Hol G}
variable {M:∀i,A.Coeff → Coefficient A (F i).f}{Q:∀i,A.Coeff → Coefficient A (F i).c}
variable (P₁:∀ i,Torch S U₀ 0 (F i|>.pW) (M i) d (salary (now (β i) G P')))(P₂:∀ i,Torch S U₀ 0 (F i|>.pV) (Q i) d (salary (β i)))
variable (hk:∀ i, Grant (z:=now (β i) G P') (P₁ i) T1)(hi:∀ i,Grant (z:=β i) (P₂ i) T2)
variable (p0':Spells.Pad G) (b1:I→ A.Coeff→L[ℂ] A.Coeff) (ha:Receipt β l₀ b1) (hm:∀ i v,(Q i (b1 i v)).density 0 S (F i|>.pV)= ((P'.L.val:ℝ)^l) • ((F i|>.hostS.Z).push (F i|>.pW.beta) ((M i v).density 0 S (F i|>.pW))))
variable (hp': l+6 ≤ d)(hq':-(11/10:ℝ)<v)(hK:v<v')(hWh: ∀ i, RequestZ (P':=P') (j:=j) N (hazard N hz) hp' v v' hK hq' I (Real.log (now (β i) G P')) ≤ (F i).c.val)(hL:∀ i: I, Real.exp (-(v*Real.log (now (β i) G P'))) ≤ (F i).c.val)
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
local notation "φ"=> βM (Eve W)
include hc hWh in
lemma ships : ∀ᶠ i in l₀, RequestZ (P':=P') (j:=j) N (hazard N hz) hp' v v' hK hq' I (fate (Eve W) i) ≤ (F i).c.val:= by
        have hΩ:= horn F W hc; exact Eventually.of_forall (fun i=> (congr_arg (fun s=>RequestZ (P':=P') (j:=j) N (hazard N hz) hp' v v' hK hq' I (Real.log s)) (congr_fun hΩ i)).trans_le (hWh i))
include h hc hL in
lemma SlopeW : Wage (Eve W) l₀ (fun i=> (((F i).c.val:ℝ))⁻¹) v:=by
       have p0:= helm F W h hc; have hΩ:= horn F W hc
       refine (RateLE.exp v p0.tense).of_norm_le (Eventually.of_forall fun i=>?_); rw[Real.norm_of_nonneg (by positivity:(0:ℝ)≤ (((F i).c.val:ℝ))⁻¹)]; have ht:= inv_anti₀ (Real.exp_pos _) (hL i); rw [Real.exp_neg,inv_inv] at ht; unfold fate; rw [hΩ]; exact ht
include h hc P₁ P₂ hk hi ha hm hp' hq' hWh hK hL hZ hb Y₀ C₀
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option maxHeartbeats 200000 in
lemma ℳStave {x y z:ℝ}  (ht:Zeph.StackP R x y z): Wage (Eve W) l₀ (fun i=> (ClockVal N C₀ (F i).row.coarse S p0' (P₂ i) (Clock.gap (F i).pV.beta)).comp (b1 i) - (Adventure N Y₀ C₀ P'.L (Stint N (F i).row Ξ) (F i).row.fine (F i).row.coarse (Chase.σW (Eve W) i)).comp (ClockVal N Y₀ (F i).row.fine S p0' (P₁ i) (Chase.σW (Eve W) i))) v':=by
        exact TapeWork F (E:=X₀.E) (M:=M) (N:=Q) (ε:=fun i=>Clock.gap (F i).pV.beta) W (helm F W h hc) X₀.γ (fun i=> (hc i).flare) hZ (f_Price F W h hc) N Y₀ C₀ (Hort F W h hc) ht P₁ P₂ (plyQ F W h hc P₁ hk) (pierQ F W h hc P₂ hi) (hΔm F W h hc) (Eventually.of_forall fun i=>(hc i).scope) p0' (SlopeW F W h hc hL) hq' hp' hK (ships F N W hc hp' hq' hK hWh (hz:=hz)) (y_Price F W h hc) hb b1 ha (Eventually.of_forall hm)
lemma StaveK : Wax β l₀ (fun i=> (ClockVal N C₀ (F i).row.coarse S p0' (P₂ i) (Clock.gap (F i).pV.beta)).comp (b1 i) - (Adventure N Y₀ C₀ P'.L (Stint N (F i).row Ξ) (F i).row.fine (F i).row.coarse (Clock.gap (F i).pW.beta)).comp (ClockVal N Y₀ (F i).row.fine S p0' (P₁ i) (Clock.gap (F i).pW.beta))) v':=by
        let p0:= helm F W h hc; obtain ⟨c,r,t,HT⟩:= Zeph.LiftFee H; have he:= Ωζ p0.high h (Hort F W h hc|>.Currency) (ℳStave F N W h hc hZ hb Y₀ C₀ P₁ P₂ hk hi p0' b1 ha hm hp' hq' hK hWh hL HT)
        apply he.congr; filter_upwards with i; have ht:Chase.σW (Eve W) i = Clock.gap (F i).pW.beta:= rfl; exact congr_arg (fun s:ℝ=> (ClockVal N C₀ (F i).row.coarse S p0' (P₂ i) (Clock.gap (F i).pV.beta)).comp (b1 i) - (Adventure N Y₀ C₀ P'.L (Stint N (F i).row Ξ) (F i).row.fine (F i).row.coarse s).comp (ClockVal N Y₀ (F i).row.fine S p0' (P₁ i) s)) ht

end
end
end MatchZ
end
end YM.OPE.Stroke
