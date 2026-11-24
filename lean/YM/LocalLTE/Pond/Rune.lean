import YM.LocalLTE.Pond.Sway
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
open Time
variable (G) (L:Side)(Q:Stage)(u:ℝ){a b:ℝ}{m:ℕ}(hc:Price.Penny m a b Q G)
local notation "p"=> (Time.probe Q)
local notation "H"=>tH (Time.probe Q)
local notation "¥"=> Time.base G Q
local notation "ℱ"=> (fun x=>betaF G x L)
-- purchase y comparison. hc pre.Commit t≥ growth last. α abs ≤ K (D fixed after L). small forecast bail.
variable (j:ℕ)
def snowT (k:ℕ)(G:Gauge)(L:Side)(u:ℝ)(a:ℝ)(x:ℝ)(Q:Stage):= -- Eshock.p chain weight.A upper.th^e small. Use p threshold≤1
    let β:= betaF G x L; let E:=β^Urns.dust k; let p₀:= (Time.probe Q)
    let HG:=3*a*β^(Pastel.chip 0); let V:=|u|+1
    let s:= Real.exp (-(Q.width/4)*radiusB x)
    E*(resetFee G p₀* HG)+(turnFee p₀*1*(s*lowBase G Q.clip p₀ Q.width Q.paths)+(turnFee p₀*(1*E))*(anchoredFee p₀ lowCount*lowerSize Q.clip Q.paths)) +Price.tH p₀*(turnFee p₀* V*(s*highBase G p₀ Q.width Q.paths)+(turnFee p₀*(V*E))*(anchoredFee p₀ highCount*(Q.paths+Q.paths)))
lemma tails (p₀:RG.Stage)(q:ℝ) : Rate G L q fun t=> Real.exp (-(p₀.width/4)*radiusB t):=by
     refine (Rate.cutoff (G:=G) (L:=L) (a:=q) (show 0<p₀.width/4 from div_pos p₀.width_pos (by norm_num))).compare (Eventually.of_forall fun x=>?_)
     rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x by exact_mod_cast Nat.div_le_self ..) (by have he:=p₀.width_pos; linarith)
lemma snowStorm (k:ℕ)(a:ℝ): Rate G L (Urns.dust k) (fun x=> snowT k G L u a x Q) := by
    let r x:= ((ℱ x)^(Urns.dust k)); let v:=Urns.dust k
    have hr: Rate G L v r:= Rate.power
    have hx := Price.tails G L Q v
    have he: Rate G L v (fun x=> r x*(resetFee G p*(3*a*(ℱ x)^(chip 0)))):= ((hr.mul (((Rate.power (G:=G) (L:=L) (a:=chip 0)).mul_left (3*a)).mul_left _)).weaken (by norm_num [chip]))
    unfold snowT; exact (he.add (((hx.mul_right _).mul_left _).add (((hr.mul_left 1).mul_left _).mul_right _))).add ((((hx.mul_right _).mul_left _).add (((hr.mul_left _).mul_left _).mul_right _)).mul_left _)
include hc
lemma weatherB (j:ℕ) : ∀ᶠ t in atTop,∀ (P:BudgetPoint), Time.Same Q P→P.threshold=Pressure.temp t → P.B = Pressure.radiusB t →
    ∀ (Δ α:ℝ), let β:= betaF G t L; let V:=β^(chip (j+1)); let d:=β^(chip 0); let κ:=2*a*V
    P.threshold^2*|Δ| ≤ a*d+κ → |α| ≤ |u| → Price.tH P*regularNeed G P Q.clip Q.width Q.paths 0 κ+ vest P Δ α (β^Urns.dust j) (a*d+κ) Q.clip G Q.width Q.paths≤ b*V:=by
     have hp₀:=hc.1; have hb:= (Time.base_nonneg G Q).1; have hv:0<H:=Real.exp_pos _
     have hz := Sienna.contraction G L (a:=1) hp₀ (Price.snowStorm G L Q u j a) (show Urns.dust j < chip (j+1) by unfold Urns.dust; linarith)
     filter_upwards [hz, Price.calm G L (3*a),Work.E09.betaF_growth G L|>.eventually_ge_atTop (1:ℝ)] with t hx h hT P hP ht hB Δ α β V d k hΔ hα
     have hβ:0<β:= zero_lt_one.trans_le hT; have hk:0≤k:=mul_nonneg (mul_pos zero_lt_two hp₀).le (Real.rpow_nonneg hβ.le _)
     have hA:a*d+k≤3*a*β^(chip 0):= by
        have he: chip (j+1) ≤ chip 0:= by unfold chip; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) j]
        linarith only [mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT he) hp₀.le] -- edit locals
     have he: |Δ|≤1:= by
        apply le_of_mul_le_mul_left _ (sq_pos_of_pos P.threshold_pos); rw [mul_one]; exact hΔ.trans (hA.trans (h P ht))
     have ha:(P.threshold)^3 ≤ (1:ℝ) := pow_le_one₀ P.threshold_pos.le P.threshold_le
     have hh:|α+Δ|≤|u|+1:=(abs_add_le ..).trans (add_le_add hα he)
     obtain ⟨hl,hH,hK,hb',hk'⟩:= Price.validS G Q hP
     have hl':=turnFee_pos (Time.probe Q); have hh₁: (|α+Δ| *P.threshold^3)≤ |u|+1:= (mul_le_of_le_one_right (abs_nonneg _) ha).trans hh -- need spaces
     have hz': |Δ| *P.threshold^2≤1:= mul_le_one₀ he (pow_nonneg P.threshold_pos.le _) (pow_le_one₀ P.threshold_pos.le P.threshold_le)
     have hu: vest P Δ α (β^Urns.dust j) (a*d+k) Q.clip G Q.width Q.paths≤ Price.snowT j G L u a t Q:=by
        unfold vest snowT; simp only [Price.slope]; rw [hk',hl,hK,hH,hb',hB];
        obtain ⟨hX,hY,_⟩:= budget_pos (Time.probe Q) G Q.clip Q.width_pos Q.paths_pos.le
        have ht' (i:ℕ): anchoredFee P i= anchoredFee p i:=by unfold anchoredFee; rw [hP.2.2]; rfl
        rw [ht',ht']; have hf:0≤resetFee G p:=mul_nonneg (Real.exp_nonneg _) (loss_pos ..).le
        have hx:0≤ β^Urns.dust j:= Real.rpow_nonneg hβ.le _; have hh₂:0≤ anchoredFee p lowCount*lowerSize Q.clip Q.paths:= by unfold anchoredFee lowerSize; have he:=Q.clip.quadratic_pos; have he':=Q.paths_pos; positivity
        have hh₃:0≤anchoredFee p highCount*(Q.paths+Q.paths):= by unfold anchoredFee; have hx:=Q.paths_pos; positivity
        gcongr -- edit
     rw [Time.table G Q hP,hH,abs_zero,zero_mul,mul_zero,add_zero]; refine (add_le_add_right hu _).trans ?_; rw [one_mul] at hx
     have hw : (H)*(Time.base G Q)*(2*a)+a ≤ b:= by
        have he: (H)*(Time.base G Q) ≤ (1+H)*(1+Time.base G Q):=by nlinarith only [hb,hv]
        have hh : 1 ≤ (1+H)*(1+Time.base G Q):= one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right hv.le) (le_add_of_nonneg_right hb)
        linarith only [mul_le_mul_of_nonneg_right he hp₀.le, hp₀, hc.2.2.2.1, mul_le_mul_of_nonneg_right hh hp₀.le]
     have ht':0 ≤ V:=Real.rpow_nonneg hβ.le _; linarith only [hx, mul_le_mul_of_nonneg_right hw ht']

end YM.AnalyticBridge.VerifiedReset.Collection.Price
