import YM.Qlocal.Flute
import YM.AllOrder.Wheel.Travel
/-! Price uniform over all compact-collar bootstrap queries. Mature a posed trace_mark + exogenous gauge weights (Auth.R σ pre!!) -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
namespace Horn
section logs
variable {ι:Type*}{T:Catch.Clock ι}{X:ι→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)] {Y:∀ i,X i}{Z:∀ i,X i→ℝ}
local notation "C"=> T.Meter
local notation "H"=> Catch.Cover T k 0 (fun _=>1)
-- logarithm near S>0 tech, clump.L.Rescale
lemma lodged (hp:H Z Y)(he:∀ᶠ i in T.rail,1/(2:ℝ) ≤ Z i (Y i)):
   H (fun i=> Real.log ∘ Z i) Y:= by
 let s (i:ι):= Z i (Y i); have hm: C s 0:=(hp.value.smaller (Eventually.of_forall (fun i=> le_of_eq (by simp [Real.norm_eq_abs,s])))); have h0:∀ᶠ i in T.rail, 0<s i:= he.mono fun _ hi=> lt_of_lt_of_le (by norm_num) hi
 have hC:C (fun i=> (s i)⁻¹) 0 :=(Clock.Meter.const T 2).smaller ?_; swap; · filter_upwards [he,h0] with i hi hx; rw [abs_of_pos (inv_pos.mpr hx)]; exact ((inv_le_comm₀ hx (by norm_num : (0:ℝ)<(2:ℝ))).2 (by have he : (2:ℝ)⁻¹ ≤ s i:= (by simpa only [one_div] using hi); simpa only [inv_inv] using! he)).trans (le_abs_self _) -- inv_le_comm? fix
 have hl : C (fun i => ‖Real.log (s i)‖) 0:= (hC.add hm).smaller ?_; swap; ·
    filter_upwards [h0] with i hi; rw [Real.norm_eq_abs,abs_abs,abs_of_pos (add_pos (inv_pos.mpr hi) hi)]; apply abs_le.mpr; rw [neg_le]; rw [←Real.log_inv]; have h' := inv_pos.mpr hi; exact ⟨by linarith [Real.log_le_sub_one_of_pos h'], by linarith [Real.log_le_sub_one_of_pos hi]⟩ -- inspect `rw` inv-log wrong?
 let v(i:ι):= (s i)⁻¹ • Z i; have hL: Tendsto (fun i=> v i (Y i)) T.rail (𝓝 (1:ℝ)):= tendsto_const_nhds.congr' (h0.mono fun i hi=> (inv_mul_cancel₀ hi.ne').symm)
 have h1 := (hp.smul hC).weak (b:=0) (by norm_num)
 have ha:H (fun i=> Real.log ∘ v i) Y:= (Cover.comp le_rfl h1 (Cover.loc (K:=fun i=> v i (Y i)) (Real.contDiffAt_log.mpr one_ne_zero) hL)).weak (by simp)
 -- equality log at ZERO when Z=0 may not! nearpoint. need eventuallyEq around Y.
 let Q:=fun i (_:X i)=> Real.log (s i); have heC:= ha.add (Cover.fixed (a:=0) (T:=T) (U:=fun i=>ℝ) _ (Eventually.of_forall fun _=>zero_le_one) hl)
 intro e hE; filter_upwards [heC e hE,h0, hp 1 (by norm_num)] with i hi hz hv; refine hi.shimmy ?_; filter_upwards [hv.smooth.continuousAt.eventually (lt_mem_nhds hz)] with u hu; change Real.log _= Real.log ((s i)⁻¹ * Z i u)+ Real.log (s i); rw [Real.log_mul (inv_pos.mpr hz|>.ne') hu.ne', Real.log_inv]; abel
lemma steps (hp:H Z Y) : H (fun i=> road ∘ Z i) Y:= by
 let h:H (fun i (_:X i)=>(1:ℝ)) Y:= Cover.fixed (fun _=> (1:ℝ)) (Eventually.of_forall (fun _=>zero_le_one)) (Meter.const T ‖(1:ℝ)‖)
 exact lodged (Z:=fun i=> ramp ∘ Z i) (h.add hp |>.add ((hp.powerC 2).weak (by simp))) (Eventually.of_forall fun i=> ramp_ge (Z i (Y i)))
end logs
open Aux Aux.Name
variable {ι:Type*}{S':Catch.Clock ι}{P:Patch}{T:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J T (k+3)}
local notation "I"=>Aux.Name G P T u κ v k F
variable (Q:ι→ Aux.Name G P T u κ v k F) (R:∀ i, reed G (Q i|>.f))
set_option quotPrecheck false
local notation "X[" i "]"=> (Q i).X
set_option quotPrecheck false
local notation "Z"=>fun i:ι=> ℝ×(X[i] × Poll.Body (Q i).Vx)
local notation "L"=> S'.rail
local notation "μ"=> S'.Meter
def song (A:I)(R:reed G A.f) (z:ℝ×(A.X × Poll.Body A.Vx)) := Comparison.RG02.Bulk.posed A.data A.Fs R (Binding.gaugeL A.Fs z)
/-- Flute geometric budget at the projection; smooth bounds bought BEFORE tests and radii,
  independent of sector and supplementary path. Volume continues as in Name.Proper. Only using *insertion value*
  `allReal` on fields & masks actually contributing to estimation, no assumption derived proximity. Q of arbitrary uniform type (includes independent test choices, direction and time variable as long as spending is budgeted in the Fleet). Doesn't provide punctured matching. -/
structure Lane (R : ∀ i, reed G (Q i|>.f)) (S':Catch.Clock ι)(ℓ q:ℕ) : Prop where
 tells : ∀ i, Flute (R i) q -- for all clock.S.Thrift
 militia : ∀ p,0 < (p:ℝ)→ ∀ᶠ i in S'.rail,∀ z,‖z‖<1→ Brush ℓ (S'.cost i^p) 1 (song (Q i) (R i)) z
 allReal : ∀ p,0<(p:ℝ)→∀ᶠ i in S'.rail, ∀ x:Config G (Q i).f, flags (Q i).price.threshold x=∅ → |R i (Q i).Θ x| ≤ S'.cost i^p
variable (h : Lane Q R S' j q)
local notation "n[" i "]"=> (Q i|>.Θ)
local notation "A[" i "]"=> song (Q i) (R i)
include h
lemma music {α:Type*}(S0:Catch.Clock α) (f:α→ι)(he:S'.Fare (U:=S0) f): Lane (Q ∘ f) (fun i=> R (f i)) S0 j q:= by
 refine ⟨fun i=> h.tells _,?_,?_⟩; all_goals intro p hp; -- timeout? macro.
 · filter_upwards [he.tends.eventually (h.militia p hp),he.same] with i hi hI; rw [hI]; exact hi
 filter_upwards [he.tends.eventually (h.allReal p hp),he.same] with i hi hI; rw [hI]; exact hi
lemma cap {a:∀ i,(Z i)} (hg:∀ᶠ i in L,‖a i‖<1): Catch.Cover (V:=Z) S' j 0 (fun _=>1) (fun i=> A[i]) a:= by intro e he; filter_upwards [hg,h.militia e he] with i hi hx using hx _ hi
lemma owns (t:ℝ) {y:∀ i,(Z i)}(hg:∀ᶠ i in L,‖y i‖<1): Catch.Cover (V:=Z) S' j 0 (fun _=>1) (fun i=> build (Q i|>.Fs) (R i) t) y:= by
 have hx: μ (fun i=> ‖y i‖) 0:= Meter.smaller (Meter.const S' 1) (hg.mono fun i hi=> by rw [abs_of_nonneg (norm_nonneg _)]; exact hi.le.trans (le_abs_self _)); let v(i:ι):= ContinuousLinearMap.fst ℝ ℝ (X[i] × Poll.Body (Q i).Vx)
 have hv(i:ι):‖v i‖≤1:= ContinuousLinearMap.norm_fst_le ..; have hf: Catch.Cover (V:=Z) S' j 0 (fun _=>1) (fun i=> ⇑(v i)) y:= (Cover.comp_lin («L»:=v) hx (le_refl (0:ℝ)) (Meter.smaller (Meter.const S' 1) (Eventually.of_forall fun i=>by rw [abs_of_nonneg (norm_nonneg _)]; exact (hv i).trans (le_abs_self _)))).weak (by simp) -- specify args
 exact (((hf.powerC 2).mul (steps («Z»:=fun i=> (t • ⇑(v i))*A[i]) ((((hf.smul (Meter.const S' t)).mul (cap Q R h hg)).weak (by simp))))).weak (by simp))
lemma timing (hp:Proper Q S') (t:ℝ): Flood (fun i=> changes (Q i|>.forest) (Q i|>.shape) (R i) t (Age.scope (Burn.horizon κ+2))) S' j:= by
 let s i:= Metric.ball (0: Z i) 1; let T':= (S'.book s); let he:= S'.bookF s; let V (i:ι):= changes (Q i|>.forest) (Q i|>.shape) (R i) t (Age.scope (Burn.horizon κ+2)); have hm(i:ι):= h.tells i; let hG := music Q R h T' Sigma.fst he; refine ⟨Eventually.of_forall fun i=> slope _ _ _ (Q i|>.legal) (R i) t (hm i), fun e hv=> ?_⟩
 have hl : ∀ᶠ i:(Σ i:ι,{x:Z i//x∈ s i}) in T'.rail, ‖i.2.1‖ < 1:= Eventually.of_forall fun i=> mem_ball_zero_iff.mp i.2.2
 have hh:= owns (Q ∘ Sigma.fst) (fun i=> R i.1) hG t (y:=fun i=> i.2.1) hl; have hT:= Name.Proper.gas (T:=T') (Q∘ Sigma.fst) (Name.Proper.sail Q hp _ _ he) j (fun i=> i.2.1) hl
 have hz: (∀ᶠ i in S'.rail, ∀ y∈s i, Brush j (S'.cost i ^e) 1 (V i) y):=(S'.booked s _).mp ((hT.sub hh) _ hv); filter_upwards [hz] with i hi q hx using hi q (mem_ball_zero_iff.mpr hx)
end Horn
end YM.Qlocal.Bind
