import YM.MSbar.Atlas.Bills
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6
open Heath Bulk Finset
variable (l: Side)(G)(A:Stage)
-- variables at a step may sample from these gates uniformly in every projection.Gates charged
-- *after* choosing pre threshold, not analyses with volume dependent δ.
def bbP (x:ℝ):= Vac.Numbers.P x
def cue (x:ℝ):= (Real.sqrt x)⁻¹
def lbt (x:ℝ):= 2*bbP x
def ability (x:ℝ):= cue x ^ ((11:ℝ)/5)
def courage (G:Gauge)(l : Side)(x:ℝ):= Real.exp (-(bbP (betaF G x l)))
lemma temp_shape (x:ℝ): temp x=cue x*bbP x:=rfl
variable {G}
lemma cues (G:Gauge)(L : Side): Rate G L (-(1/2)) (cue∘tip G L):=by
    apply Rate.power.congr; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow];rfl
lemma ability_rate (G:Gauge)(L:Side): Rate G L (-(11/10)) (ability∘tip G L):=by
    apply Rate.power.congr; filter_upwards [Delay.shift_pos G L] with x hx
    rw [Function.comp_apply]; unfold ability cue; rw [Real.sqrt_eq_rpow,Real.inv_rpow (Real.rpow_nonneg hx.le _),← Real.rpow_mul hx.le, Real.rpow_neg hx.le]; ring_nf
lemma shiftedLog (G:Gauge)(l:Side): ∀ᶠ x in atTop, radiusB x ≥1 ∧ 1<x∧ 1<betaF G x l∧x/2 ≤ betaF G x l∧ betaF G x l ≤ 2*x∧ Real.log (betaF G x l) ≤ 2*Real.log x:=by
    let k:= G.slopeConstant*Real.log (l.val);filter_upwards [eventually_gt_atTop (4:ℝ), eventually_gt_atTop (2*|k|)] with x he hh
    have hv:= abs_le.mp (show |k| ≤ x/2 by linarith only [hh]); have h : x/2 ≤ betaF G x l:=by unfold betaF; linarith
    have hX: betaF G x l ≤ 2*x :=by unfold betaF; linarith
    have hx: 1<x :=by linarith
    exact ⟨Nat.ceil_pos.mpr (sq_pos_of_pos (Real.log_pos hx)),hx,by linarith,h,hX,(Real.log_le_log (by linarith) (show betaF G x l ≤ x^(2:ℕ) by nlinarith)).trans_eq (by rw [Real.log_pow];norm_num)⟩
lemma gross_scale (G:Gauge) (l:Side) : ∀ᶠ x:ℝ in atTop, (fun i=> tip G l i) x^(-1:ℝ) ≤ 1 := by
    filter_upwards [shiftedLog G l] with x h; exact le_trans (Real.rpow_neg_one .. |>.le) (inv_le_one_of_one_le₀ h.2.2.1.le)
lemma nearshift (G:Gauge)(l:Side)(b:ℝ) : ∃ C:ℝ, 0<C∧∀ᶠ x in atTop,x^b ≤ C* betaF G x l ^ b := by
    by_cases hh:0≤b
    · refine ⟨(2:ℝ)^b,by positivity,(shiftedLog G l).mono fun x h=>?_⟩
      rw [← Real.mul_rpow (by positivity) (by linarith only [h.2.2.1])]; exact Real.rpow_le_rpow (by linarith only [h.2.1]) (by linarith only [h.2.2.2.1]) hh
    have hB:=lt_of_not_ge hh
    refine ⟨(1/2:ℝ)^b,by positivity,(shiftedLog G l).mono fun x h=>?_⟩
    have ha :0<betaF G x l:=zero_lt_one.trans h.2.2.1; rw [← Real.mul_rpow (by positivity) ha.le]; exact Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) ha) (by linarith only [h.2.2.2.2.1]) hB.le
-- for shifted.B positive offset no blow.Flow Rate using slack.The universal zero block (1) counts.Let code
lemma loose (G:Gauge) {p:ℝ→ℝ} {a:ℝ} (h:Rate G ⟨1,one_pos⟩ a p) (l:Side): Rate G l a p:=by
    intro x hx; let b:=(x+a)/2; have h₁:a<b:=by unfold b; linarith
    have hx': b<x:=by unfold b;linarith
    obtain ⟨C,hC,hT⟩:=nearshift G l b
    have hp : Rate G l b (fun x=> C*betaF G x l^b):= Rate.power.mul_left _
    filter_upwards [h _ h₁,hT,hp x hx',Delay.shift_pos G l] with p h hg hR hz
    have hk:=h.trans (show _≤ C*betaF G p l^b from ?_)
    · exact hk.trans ((le_abs_self _).trans hR)
    simpa [Pressure.betaF] using hg
lemma macroG (G:Gauge)(L:Side): Rate G L (-(1/2)) temp := loose G pf L
where
 pf : Rate G ⟨1,one_pos⟩ (-(1/2)) temp := by simpa [fiery, Pressure.betaF] using Rate.flame (G:=G) (L:=⟨1,one_pos⟩)
lemma microG (G:Gauge)(L:Side): Rate G L 0 bbP := loose G (Rate.monitor.congr (Eventually.of_forall fun i=>by simp [bbP,Delay.fineMonitor,Pressure.betaF])) L
lemma valor (G:Gauge)(L:Side) : Pole G L (courage G L):=fun a=> by unfold courage; simpa [courage,bbP,Delay.fineMonitor] using Rate.monitor_cutoff (G:=G) (L:=L) (a:=a) (δ:=1) one_pos (γ:=1) one_pos
lemma Pole.first (G:Gauge)(a:ℝ)(ha:0<a):Pole G ⟨1,one_pos⟩ (fun x=> Real.exp (-a*radiusB x)):= by simpa [Pole,Pressure.betaF] using Pole.cape ⟨1,one_pos⟩ G ha
end YM.MSbar.Heath.Stock
