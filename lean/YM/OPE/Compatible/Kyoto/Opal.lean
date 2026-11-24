import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Zag
import YM.OPE.Compatible.Kyoto.Fiscal
import YM.OPE.Compatible.Kyoto.Room
/-!
# From coefficient estimates to an operator estimate

`End_p` bounds the upper exponential rate of a linear map on a finite
coordinate space from the rates of its values on the coordinate basis.
`Wage_obs` applies this to the difference between the coarse observation
and the transported fine observation, using their real and imaginary parts.
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
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial
open Spells Lass Lass.Zest Ibis Labels Source Pill
variable {L:PriceBook H T}{a:Axis}
variable (V:Foyer L hs a l (d+6))
set_option quotPrecheck false
local notation "K!"=> Cab T
local notation "W!"=> V.pay.st
variable {he:highStage L hs a V ≤ i} {hp:highStage L hs a V ≤ j}
variable (X:BankW L hs a V he p)
variable (Y:BankW L hs a V hp p')
variable {A: Labels.Frame G l}{U₀:Hol G}{S:SectionData A}
variable (R':Spells.Pad G)
section
variable (W:Tracts G (d+6) V.pay.st.τ →L[ℝ] Tracts G (d+6) V.pay.st.τ)
variable (F:Cab T i p)(E:Cab T j p')
local notation "Kκ"=>X.cart
local notation "Jι"=>Y.cart
variable {P:A.Coeff → Coefficient A n}{Q:Rep G n}
variable (P₁:Torch S U₀ 0 Q P d b)
set_option maxHeartbeats 200000 in
lemma leap (V1:ℝ)(u:A.Coeff)(M:Side): Adventure V X Y M W F E V1 (ClockVal V X F S R' P₁ V1 u)=Garm (dims V) ((M.val:ℝ)^l • doublet (τΡ Kκ F Jι E W V1) (Swing V X P₁ F R' V1 u)):=by
       let U:= Swing V X P₁ F R' V1 u; let p:=τΡ X.cart F Y.cart E W V1; let s:= Adventure V X Y M W F E V1; let x:= (M.val:ℝ)^l; have hp: s (Garm (dims V) U)= Garm (dims V) (x • doublet p U):= (congr_arg (fun y=>x • y) (Ωp (dims V) p U)).trans ((Garm (dims V)).map_smul x (doublet p U)).symm
       exact (congr_arg s (LaidS V X P₁ F R' V1 u)).trans hp
end
section
open ContinuousLinearMap
lemma End_p [Fintype J] [DecidableEq J][NormedAddCommGroup E][NormedSpace ℂ E]{v:ℝ} (R:I→(J→ℂ)→L[ℂ] E){f: Filter I}{x:I→ℝ}(hx:Tendsto x f atTop)(h:∀ j:J,RateLE f x (fun i=> R i (Pi.single j 1)) v) : RateLE f x R v:=by
        apply RateLE.of_norm_le (RateLE.sum (f:=fun j i=>‖R i (Pi.single j 1)‖) (S:=univ) hx (fun i _ => (h i).norm)); refine Eventually.of_forall fun i=>opNorm_le_bound (R i) (sum_nonneg fun _ _=> norm_nonneg _) (fun u=>?_); let A:=fun j:J=>u j • Pi.single (M:=fun _:J=>ℂ) j 1; nth_rw 1 [show u=∑ i,A i from funext fun i=>by unfold A;rw[Finset.sum_apply];simp[Pi.single_apply]]; rw [_root_.map_sum]; apply (norm_sum_le ..).trans; rw [sum_mul]; refine sum_le_sum (fun i' _=>?_); unfold A; rw [_root_.map_smul,norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i') (norm_nonneg _)
end
section
variable (κ:Side)(M:I→ Tracts G (d+6) V.pay.st.τ →L[ℝ] Tracts G (d+6) V.pay.st.τ)
variable (P:I→ Cab T i p)(Q:I→Cab T j p')
variable {n m:I→Side}{f':∀ i,Rep G (n i)}{q:∀ i,Rep G (m i)}{Z:∀i,A.Coeff → Coefficient A (n i)}{D:∀i,A.Coeff → Coefficient A (m i)} {η θ:I→ℝ}(x:∀ i,Torch S U₀ 0 (f' i) (Z i) d (η i))(y:∀ i,Torch S U₀ 0 (q i) (D i) d (θ i))
variable {f:Filter I}{t s ℓ:I→ℝ}{v:ℝ}(g:I→ A.Coeff→L[ℂ] A.Coeff)
local notation "δ"=>τΡ
include g
set_option synthInstance.maxHeartbeats 220000 in
set_option maxHeartbeats 200000 in
lemma Wage_obs (ht:Tendsto ℓ f atTop)(hu:∀ a:A.Index,∀ z:ℂ→L[ℝ]ℝ, RateLE f ℓ (fun i=> FaithV V Y (y i) (Q i) R' (s i) (g i (CastX (X:=A) a)) z- (κ.val:ℝ)^l • (τΡ X.cart (P i) Y.cart (Q i) (M i) (t i) (FaithV V X (x i) (P i) R' (t i) (CastX (X:=A) a) z))) v): RateLE f ℓ (fun i=> (ClockVal V Y (Q i) S R' (y i) (s i)).comp (g i) - (Adventure V X Y κ (M i) (P i) (Q i) (t i)).comp (ClockVal V X (P i) S R' (x i) (t i))) v:=by
        let A':= BoxQ (dims V); let B:= CanA (dims V); let Q'(i):= τΡ X.cart (P i) Y.cart (Q i) (M i) (t i);
        refine End_p _ ht (fun a=>?_ ); let c:=CastX (X:=A) a; let R₁(i):= Swing V X (x i) (P i) R' (t i) c; let R₂(i):=Swing V Y (y i) (Q i) R' (s i) (g i c); let k':ℝ:=(κ.val:ℝ)^l
        let χ0(i):=R₂ i-k' • doublet (Q' i) (R₁ i)
        have hx:RateLE f ℓ χ0 v:=by intro e he; filter_upwards [hu a Complex.reCLM _ he, hu a Complex.imCLM _ he] with i hh hz; change ‖(_,( _:B))‖≤ _; rw[Prod.norm_def]; exact max_le hh hz
        apply (hx.linear ht (Garm (dims V)).toContinuousLinearEquiv.toContinuousLinearMap).congr; filter_upwards with i; change Garm (dims V) (χ0 i)= ClockVal V Y (Q i) S R' (y i) (s i) (g i c) - Adventure V X Y κ (M i) (P i) (Q i) (t i) (ClockVal V X (P i) S R' (x i) (t i) c); exact (_root_.map_sub (Garm (dims V)) (R₂ i) (k' • doublet (Q' i) (R₁ i))).trans (congr_arg₂ ((·-·):A' → A' → A') (LaidS V Y (y i) (Q i) R' (s i) (g i c)).symm (leap V X Y R' (M i) (P i) (Q i) (x i) (t i) c κ).symm)
end
end YM.OPE.Stroke
