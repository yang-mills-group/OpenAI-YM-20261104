import YM.Qlocal.Moonset.Royal
/-!
Cumulative radius accounting. Use on any marks in the accepted arrays; factors charged at
all levels. Also supplies full forced pricing on these terms at output, incl after diversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual.Season
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe ConnectedActivityE6 Coat PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt Program Program.Hull
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
variable {Ω ι V : Type} [DecidableEq V][Fintype V][Nonempty V] (B:Marker.Census V) {G:Gauge}
    (X:Run G){Δ:ℕ→Prop} {m k p N j k' z n i l : ℕ} {δ r θ u v w E C ℓ: ℝ}
local notation "a"=> X.alloy.B.a
set_option quotPrecheck false
local notation "A"=> X.alloy
local notation "Y"=> X.alloy.B.a.clock.hatBeta
local notation "κ"=> Fintype.card (Gauges.Atlas.Notice B)
local notation "Z"=> fun i=>Real.log (Y i)
local notation "τ"=> Studio.loss X B
open Parabola Dialect Calendars
namespace Studio
-- cumulated scaled reading. no ratio on couplings hidden in this multiplicative cost.
noncomputable abbrev scale (m j:ℕ):ℝ:= ∏ i∈Finset.Ico m j,loss X B i
local notation "ζ"=> scale B X
private lemma capP (x:ℝ) : 0< Cove.caps x := lt_min (Real.exp_pos _) (Real.exp_pos _)
lemma loss_one (i:ℕ) : 1 ≤ Studio.loss X B i := by
 unfold loss Rev.vial; let b:= Banknote.breadQuota («A»:=X.alloy) (m:=i); have hb:0<b:= capP _; have hκ:0 ≤ (κ:ℝ)*b:=mul_nonneg (Nat.cast_nonneg _) hb.le
 exact one_le_mul_of_one_le_of_one_le (by change 1 ≤ b+2; linarith) (by change 1 ≤ 1+κ*b+3; linarith)
lemma kept (m j:ℕ) : 1 ≤ Studio.scale B X m j:= Finset.one_le_prod fun i _=> Studio.loss_one B X i
open Rev
noncomputable def tagScale (m j:ℕ) (T:Ray B):= Rev.respire T (Studio.scale B X m j) -- uses loss defined for all m
lemma scale_r (hm:m<j): scale B X m j=Studio.loss X B m * scale B X (m+1) j := by unfold Studio.scale; rw [Finset.prod_eq_prod_Ico_succ_bot hm]
lemma air_shift (T:Ray B) (he:m<j) : Studio.tagScale B X m j T= Studio.tax X m (Studio.tagScale B X (m+1) j T):= by
 funext s; unfold tagScale Studio.tax Rev.respire; rw [scale_r B X he,mul_inv,mul_pow,mul_assoc]
lemma the_tag (T:Ray B) : Studio.tagScale B X m m T=T:= by ext1 i; unfold Studio.tagScale Rev.respire scale; simp
lemma ready (u:Ray B)(ht:Rental u) (m j:ℕ) : Rental (Studio.tagScale B X m j u) ∧ Studio.tagScale B X m j u≤ u:= Rev.breathing _ ht _ (kept B X m j)
lemma redeem (T:Ray B)(v:Rental T)(r:ℕ)(hr:Program.Certificate.Rank r B)(i:B.Mode) : T i≤ (scale B X m j)^r * Studio.tagScale B X m j T i:= by
 have hv:=kept B X m j; unfold Studio.tagScale Rev.respire; rw [←mul_assoc]; nth_rw 1 [← one_mul (T i)]
 refine mul_le_mul_of_nonneg_right ?_ (v.pos _|>.le)
 apply le_trans _ (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hv (hr i)) (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hv)) _)); rw [inv_pow,mul_inv_cancel₀ (pow_pos (zero_lt_one.trans_le hv) _ |>.ne')]

-- budget across close intervals. routine but important: factor depends on declared day K(B), not on total reflected copy count: for fixed local demand ONLY. Arbitrary-alphabet use must instead carry discounted radii unrecovered.
private lemma years (g:G.Simple) : Tendsto (fun i=> Real.sqrt (Real.log (Y i))) atTop atTop:= Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (Corrected.Grows.beta a g))
private lemma dayLog (g:G.Simple) : ∀ᶠ z:ℕ in atTop, ∀ (m j:ℕ), z ≤ m → m<j → Hull.Close X.alloy.B.a z j → Real.log (Studio.loss X B m) ≤ 8*Real.sqrt (Hull.year (a) z):= by
 let d i:= Real.sqrt (Z i); let M j:=Real.exp (d j); have hc v:1 ≤ M v:=Real.one_le_exp (Real.sqrt_nonneg _); filter_upwards [Hull.over_year («A»:=X.alloy) g,( (Real.tendsto_exp_atTop.comp (years X g)).eventually_ge_atTop ((3:ℝ)*(κ+4)))] with i hi hp m j hx hh hw; have he':Hull.year a (m+1) ≤2*Hull.year a i:= (Real.log_le_log (zero_lt_one.trans ((a).fits.delayed _)) (grown X.metals X.rolls (A) hh)).trans (hi j (hx.trans hh.le) hw)
 have hM : d (m+1) ≤ 2*d i:= by nlinarith only [Real.sq_sqrt ((Real.log_pos ((a).fits.delayed (m+1))).le), Real.sq_sqrt ((Real.log_pos ((a).fits.delayed i)).le), Real.sqrt_nonneg (Z i), Real.sqrt_nonneg (Z (m+1)), show Z (m+1) ≤2*Z i from he',Real.log_pos ((a).fits.delayed i)]
 have hν : M (m+1) ≤ (M i)^2:= (Real.exp_monotone hM).trans_eq (by unfold M; rw [show 2*d i=d i+d i from two_mul _, Real.exp_add,pow_two])
 let b:= Banknote.breadQuota («A»:=X.alloy) (m:=m); have hb: b ≤ (M i)^2:= le_trans (b:= M (m+1)) (min_le_left ..) hν
 have hs₁ : (κ:ℝ)+4≥4:= by linarith only [Nat.cast_nonneg (α:=ℝ) κ]
 have hB : loss X B m ≤ (M i)^8:= by
    let z:= M i; have hz:z≥1:=hc i; have ha :0 < b:= capP _; have hv:=one_le_pow₀ (n:=2) hz; have hK: 3*((κ:ℝ)+4) ≤ z:= hp; let t : ℝ := (κ:ℝ)+4;
    have h :b + 2 ≤3*z^2:=by linarith only [hv,hb]
    have h' : 1+(κ:ℝ)*b+3 ≤ t*z^2:= by unfold t; have ht:=mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) κ); nlinarith only [ht,hv];
    change _ ≤ z^8;
    refine (mul_le_mul h h' (show 0 ≤ 1+(κ:ℝ)*b+3 by positivity) (by positivity)).trans ?_
    rw [show 3*z^2*(t*z^2)= (3*t)*z^4 by ring]; exact (mul_le_mul_of_nonneg_right hK (sq_nonneg (z^2)|>.trans_eq (by ring))).trans ((show z*z^4=z^5 from (by ring)).trans_le (pow_le_pow_right₀ hz (by norm_num : 5≤8)))
 apply (Real.log_le_log (zero_lt_one.trans_le (loss_one ..)) hB).trans; rw [Real.log_pow, show Real.log (M i)=_ from Real.log_exp (d i)]; exact le_of_eq (by norm_num [d])
variable (g:G.Simple)
include g
lemma gain {b:ℝ}(k:ℕ)(hb:0 < b): ∀ᶠ i in atTop,∀ j≥i, Hull.Close X.alloy.B.a i j → (Studio.scale B X i j)^k ≤ (Y i)^b:= by
 let y:= Y; let z:= fun i=> Real.sqrt (Z i); let w i:=Real.sqrt (z i); have hz:Tendsto z atTop atTop:=years X g; have hv:Tendsto w atTop atTop:= Real.tendsto_sqrt_atTop.comp hz
 filter_upwards [dayLog B X g,hv.eventually_ge_atTop (8*(k:ℝ)/b)] with i hi hl j hj he
 let u r:= Real.log (Studio.loss X B r); have hF k':0 < year a k':= Real.log_pos ((A).B.a.fits.delayed _); have hQ k':0 < Studio.loss X B k':= zero_lt_one.trans_le (Studio.loss_one B X k')
 have hs:= (Finset.sum_le_sum (s:=Finset.Ico i j) (f:=u) (fun x (hh:x∈ Finset.Ico i j)=> hi _ _ (mem_Ico.mp hh).1 (mem_Ico.mp hh).2 he)); rw [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at hs
 rw [show Studio.scale B X i j=∏ x∈Finset.Ico i j,Real.exp (u x) from prod_congr rfl (fun x hx=> (Real.exp_log (hQ x)).symm),← Real.exp_sum,← Real.exp_nat_mul, Real.rpow_def_of_pos (zero_lt_one.trans ((a).fits.delayed _))]; apply Real.exp_monotone
 refine le_trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k)) ?_
 have hl' : 8*(k:ℝ) ≤ w i*b:= (div_le_iff₀ hb).1 hl
 have ht : 0 ≤ z i := Real.sqrt_nonneg _; have hv: (w i)^2=z i:=Real.sq_sqrt ht; have hC: (z i)^2=Real.log (Y i):= Real.sq_sqrt (hF i).le
 change (k:ℝ)*(((j-i:ℕ):ℝ)*(8*z i))≤ _
 calc
   _ ≤ (k:ℝ) * (w i * (8*z i)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (by positivity)) (Nat.cast_nonneg _)
   _ = (8*(k:ℝ)) * (w i * z i) := by ring
   _ ≤ (w i*b)*(w i*z i) := mul_le_mul_of_nonneg_right hl' (mul_nonneg (Real.sqrt_nonneg _) ht)
   _ = _ := by rw [← hC]; nth_rw 1 [show w i * b * (w i*z i)= (w i)^2*z i*b from (by ring)]; rw [hv]; ring
end Studio
end YM.Qlocal.Actual.Season
