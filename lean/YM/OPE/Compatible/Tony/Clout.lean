import YM.OPE.Compatible.Tony.Prone
/-!
# Span languages. Attention from heat-up schedules.
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
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
open GlowPack Silt.Phere Ibis Owl Lass Lass.Zest Spells Yolk Pill Dial Merchant Merchant.Sleeve
section
variable {L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i':ℕ)(he:highStage L hs a V ≤ i')
variable (S:Stage)(X:BankW L hs a V he S.clip) (P:Pad G)
set_option quotPrecheck false
set_option maxHeartbeats 200000
local notation "F*"=> solar G (l+6+6) V.pay.st.τ
variable {n:I→Side}{φ:Filter I}{β:I→ℝ} {ξ:ℝ}{r:ℕ}
variable (A:∀ i, HillZ (T:=T) S i' r l ξ (β i) (n i))
variable (g:ℂ→L[ℝ]ℝ)
open Next.Scheduling
local notation "Γ"=> Counters β
local notation "p'"=> fun i=> portrait V i' he S P (A i) g
open CardinalQ
noncomputable def Mender (A:HillZ (T:=T) S i' r l ξ u c): ℕ:= Xbt i' S A+r+ coverJ u
abbrev RichHill (B:HillZ (T:=T) S i' r l ξ u c):Prop:= Board c (Mender i' S B+2)
include A
variable (ht:Tendsto β φ atTop)
include ht
local notation "Z"=>fun i:I=>Mender i' S (A i)
lemma Asc_more :Receipt β φ (fun i=>(Mender i' S (A i):ℝ)):=by
       let h:=torν i' S A ht; let t:= carth ht; unfold Mender Xbt PinB; push_cast; let f(p:ℝ): Receipt β φ (fun _=>p):=Score.steady p t; apply Score.plus (Score.plus _ (f _) t) (show Receipt _ _ _ from ?_) t; rotate_left
       · exact coverPs ht
       exact (f (1:ℝ)).plus ((f _).product ((f _).product ((f _).plus ((f _).product ((f 4).product ((f 4).product h.flour))) t))) t
variable (hr: ∀ i,Ramp V i' he (β i) ≤ (n i).val)
include hr
lemma hill_forecast: ∀ᶠ i in φ, RichHill i' S (A i):=by
       have he: Wax β φ (fun i=>((Z i:ℝ))) 0:=waitG ht (Asc_more i' S A ht); have hv:Wax β φ (fun i=>2*((Z i:ℝ)+2)) 0:= ((RateLE.const _ (carth ht)).mul (he.add (RateLE.const _ (carth ht)) (carth ht))).mono (by norm_num); filter_upwards [hv 1 zero_lt_one, ht.eventually_gt_atTop 0] with i hx hy; have hp:2*((Z i:ℝ)+2) ≤ β i:=by
            have h:(1:ℝ)*Γ i=Real.log (β i):=one_mul _; rw [h,Real.exp_log hy,Real.norm_of_nonneg (by positivity)] at hx;exact hx
       have hk: ↑(2*((Z) i+2)) < ((Nat.ceil (Real.exp (β i))):ℝ):=by push_cast; exact (hp.trans_lt (lt_of_le_of_lt le_rfl (show β i < Real.exp (β i) from (lt_add_one _).trans_le (Real.add_one_le_exp _)))).trans_le (Nat.le_ceil ..)
       exact lt_of_lt_of_le (show 2*((Z) i+2)< Nat.ceil (Real.exp (β i)) from by exact_mod_cast hk) ((Nat.le_add_right ..).trans (hr i))
omit hr
lemma hillFresh (hp:∀ i,RichHill i' S (A i)): Scaffold φ Γ n (Z) r:=by
       have hW : RateLE φ Γ (fun i:I=> (((Z) i+1:ℕ):ℝ)) 0:=by push_cast; exact (waitG ht (Asc_more i' S A ht)).add (RateLE.const _ (carth ht)) (carth ht)
       refine ⟨⟨carth ht,hW, fun i=>?_⟩,⟨fun a c hc=>?_⟩,hp⟩;swap
       · have hu:Tendsto (fun i:I=> c*Γ i) φ atTop:= Tendsto.const_mul_atTop hc (carth ht); filter_upwards [hu.eventually_ge_atTop a,(carth ht).eventually_ge_atTop (0:ℝ)] with i hi hv
         have hQ: Γ i^2 ≤ (Z i:ℝ):= (Nat.le_ceil _).trans (show ((coverJ (β i)):ℝ) ≤ _ from Nat.cast_le.mpr (show _≤ Mender i' S (A i) from Nat.le_add_left ..)); exact (mul_le_mul_of_nonneg_right hi hv).trans (by nlinarith [mul_le_mul_of_nonneg_left hQ hc.le])
       let m:= (Z) i; have hZ: r ≤ m:= le_trans (show r ≤ Xbt i' S (A i)+r from Nat.le_add_left ..) (Nat.le_add_right ..); exact ⟨Nat.lt_succ_of_le hZ,tip (hp i) (Nat.le_succ _),tip (hp i) (show r+1 ≤ m+2 from by omega)⟩
end
end YM.OPE.Stroke
