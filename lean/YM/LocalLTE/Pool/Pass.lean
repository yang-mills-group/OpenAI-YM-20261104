import YM.LocalLTE.Pool.Rates
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
open Topology Timing 
open Real (log exp)
open Payments RG.Shoot
variable (A:Stage) (η:ℝ) (L:Side)
-- strengthen K soft room. θ at startup.
lemma rates (p':Stage) (η:ℝ) (he:0 ≤ η): ∀ᶠ s:ℝ in atTop,∀ p:BudgetPoint,p.threshold=Timing.temp s→p.B=Timing.balls s→p.supportExponent=p'.supportExponent →
    let K':= Timing.M s; let v:= Timing.quota s; let H:= exp (-K') * (exp v -1)
    Loan p (exp s/2) K' K' v ∧ Rates p.B (Timing.normK s) H (Frost.soft p η (exp s)) K':=by
    let b:= Time.probe p'; let X:=Frost.chum b; have ht : Tendsto (fun s:ℝ=>Timing.M s * soft b η (exp s)) atTop (𝓝 0):=by -- log product
       let g (s:ℝ):= (log s)^2+s*(chip 0); have hx: Tendsto g atTop atBot:=by
          refine tendsto_atBot_mono' atTop (f₁:=fun x :ℝ=> (-1:ℝ)/2*x) (?_) (tendsto_id.const_mul_atTop_of_neg (by norm_num))
          filter_upwards [Timing.small (ε:=1/2) (by norm_num), eventually_ge_atTop (0:ℝ)] with s h hs; change g s ≤_; unfold g; rw [Coup.chip_zero]; linarith
       have hz (x:ℝ):Timing.M x * Frost.soft b η (exp x)=(2*η*X)*Real.exp (g x):=by unfold soft g X Timing.M; rw [← Real.exp_mul,Real.exp_add]; ring
       simp_rw [hz]; simpa using (Real.tendsto_exp_atBot.comp hx).const_mul (2*η*X)
    have hk:Tendsto (fun s=> Timing.M s*(Timing.quota s)) atTop (𝓝 0) := by
       have h' : Tendsto (fun x:ℝ=> x * exp (-x/2)) atTop (𝓝 0):= by
         -- mathlib .mul_exp...
         let f x:=x*(Real.exp (-(x:ℝ)))
         have he:Tendsto f atTop (𝓝 0):= by
            have hx := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (1:ℕ)
            simpa [f] using! hx
         have hz (x:ℝ): x*exp (-x/2)=2*f ((2:ℝ)⁻¹*x):= by unfold f; ring_nf
         simp_rw [hz]; simpa using (he.comp (tendsto_id.const_mul_atTop (show 0<(2:ℝ)⁻¹ by positivity))).const_mul 2
       exact h'.comp Timing.growing
    filter_upwards [Timing.loan p'.supportExponent, Timing.many, Timing.growing.eventually_ge_atTop 1,ht.eventually (ge_mem_nhds zero_lt_one),hk.eventually (ge_mem_nhds zero_lt_one), Real.tendsto_log_atTop.eventually_ge_atTop 3] with s hH hh hM hT hx hz p hP hB hE K' v H
    let a:=Timing.quota s; have ha:0 ≤ a:= (Real.exp_nonneg _); have hp: 0<K':= zero_lt_one.trans_le hM; have hb:0≤exp v-1:= sub_nonneg.mpr (Real.one_le_exp ha)
    let t:= soft p η (exp s); have ht:0 ≤ t:=by unfold t soft chum; have hp: 0<kiosk (p.supportExponent+1) 1:= Real.exp_pos _; positivity
    have hv:t=soft b η (exp s):=congr_arg (·*(2*(η*(exp s)^chip 0))) (sameCost (M:=0) (η:=η) p p' hE).2
    have hy:t ≤1:=(le_mul_of_one_le_left ht hM).trans (by rw [hv]; exact hT)
    have hc : ((p.B+p.B+1:ℕ):ℝ)^4 ≤ K'/4:=by apply le_trans _ hh; rw [hB]; gcongr <;> omega
    let W:= Payments.inflation H t K'; have hw:W= exp v-1+2*t:= by unfold W Payments.inflation H; rw [← mul_assoc, ← Real.exp_add,add_neg_cancel, Real.exp_zero,one_mul] -- edit
    have hz' : exp v-1≤2*a:= by
       refine (le_abs_self _).trans ((Real.abs_exp_sub_one_le ?_).trans_eq (by rw [abs_of_nonneg ha])); rw [abs_of_nonneg ha]; exact Real.exp_le_one_iff.mpr (by apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) zero_le_two)
    have hN: ((p.B+p.B+1:ℕ):ℝ)^4*W ≤1:=by
       rw [hw]; apply (mul_le_mul_of_nonneg_right hc (add_nonneg hb (mul_nonneg zero_le_two ht))).trans; have hv':K'*t≤1:=hv ▸ hT; linarith only [hx, hv', mul_le_mul_of_nonneg_left hz' hp.le] -- let defs
    refine ⟨(hH p hP hB hE).1, hp.le,mul_nonneg (Real.exp_nonneg _) hb, ht,hy,hN,?_⟩
    have he:W ≤1:=by apply le_trans ?_ hN; exact le_mul_of_one_le_left (hw.symm ▸ add_nonneg hb (mul_nonneg zero_le_two ht)) (one_le_pow₀ (by simp))
    change Real.exp (-K')*(Real.exp W-1) ≤ _
    calc
      _ ≤ Real.exp (-K') * Real.exp 1:= mul_le_mul_of_nonneg_left ((sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr he)) (Real.exp_nonneg _)
      _ ≤ _ := by
        rw [← Real.exp_add]; unfold Timing.normK; rw [Real.exp_le_exp]; have ht := Real.add_one_le_exp (4/5*(log s)^2); have hj : 1 ≤ exp ((log s)^2/5) := Real.one_le_exp (by positivity); unfold K' Timing.M
        rw [show exp ((log s)^2)=exp ((log s)^2/5)*exp (4/5*(log s)^2) by rw [← Real.exp_add]; congr 1; ring]; nlinarith
end YM.WilsonStartup.Frost
