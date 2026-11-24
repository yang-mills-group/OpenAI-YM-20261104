import YM.MSbar.Atlas.Lamp
import YM.MSbar.Atlas.Essay
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
variable (P:Patch)(K:KernelChoices)(J:Voice G) (A B:Stage)(p:Palisade)
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
local notation "v"=> (courage G (P.L))
lemma solders (g:Clear G J)(hm:0<p.gap)(ha:0<p.a)(hp:0<p.density): ∀ᶠ x in atTop,∀ {c f:Side} (R:Rep G f)(Y:Rep G c),FaceValue B (tip G P.L x) R → FaceValue A x Y→ Tinted A B x P K p J R Y (v x) (snow G P x) (v x):=by
    let z:=Ξ;let p₀:= -(6/5:ℝ); let e:= -(48/100:ℝ); have hb := (char P G).tick; have ht:Rate G P.L e (arch ∘ z):=Rate.power; have hq: Rate G P.L p₀ (steps G p ∘ z):=Rate.power.mul_left _
    have hv:=(((hb.mul_right 4|>.mul_right (Fintype.card G.ColorIndex:ℝ)).mul (ht.mul_left J.C)).mul hq); have hz := Work.E09.betaF_growth G P.L
    have hC :Rate G P.L (-(1/2)) (fun x=>whale P G K (z x) (temp (z x)) (base J (z x))) :=by
       have hx: Rate G P.L (-(1/2)) (fun x=>base J (z x)):= (flog P (G:=G)).mul_left _
       unfold whale; simp_rw [div_eq_mul_inv]; exact (((hx.mul_right _).add ((Rate.flame (G:=G) («L»:=P.L)|>.mul_left _).mul_left _)).add Rate.flame)
    filter_upwards [shiftedLog G L, torch P J p g hm ha hp,hv (p₀+-(2/5)) (by norm_num [e,p₀]), walks P B p G,
       hz.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (necklace P)), ((flog P (G:=G)).mul_left (shade G)).below (by norm_num) _ g.depth,tale P J g,hC (-(49/100)) (by norm_num), turtle P K J A B,
       interim P K J B p g] with x hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hu
    intro c f R Y hb ha
    have h0:=zero_lt_one.trans hb.enough
    refine ⟨hb.enough,hx2,?_,fun i hi=>hx4 R hb i hi,hx5,(le_abs_self _).trans hx6, ?_,?_,fun h g=>hx9 _ _ h g ha hb,hu _ hb⟩
    · change _ ≤ increments (Ξ x)*(Ξ x)^(-(2/5:ℝ)); unfold increments
      rw [← Real.rpow_add h0]; exact (le_abs_self _).trans hx3
    · exact ha.threshold ▸ hx7
    rw [hb.threshold]; exact (le_abs_self _).trans hx8
-- Estimates after laps
lemma odometer (G:Gauge) : Rate G P.L (7/10) (fun x => (digits G p (tip G P.L x):ℝ)) := by
    let z:=tip G P.L; let k:= -(6/5:ℝ); have hv:= wi G p
    have ht : Rate G P.L (-(1/2)+6/5) (fun x=> distance (z x)*(stockMove G p (z x))⁻¹):= Rate.mul (met P (G:=G)) ((Rate.power (G:=G) («L»:=P.L) (a:=6/5)|>.mul_right (unit G p)⁻¹|>.mul_right ((2:ℝ)⁻¹)).congr ?_)
    swap; · filter_upwards [Delay.shift_pos G L] with x hx; rw [stockMove, steps, increments]; simp [Real.rpow_neg hx.le,z,tip,mul_assoc,mul_left_comm,mul_comm] -- maybe defeq
    rw [show -(1/2:ℝ)+6/5=7/10 by norm_num] at ht
    apply ht.compare; filter_upwards [shiftedLog G L] with x hx; rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)]
    let y:= z x; have hi:1<y:=hx.2.2.1; rw [← div_eq_mul_inv]; apply le_trans _ (le_abs_self _); apply Nat.floor_le; change 0≤ distance y/stockMove G p y; unfold distance stockMove steps increments; have hk:=Real.log_pos hi; have hh:=zero_lt_one.trans hi; positivity
lemma endLap (G:Gauge) : Pole G P.L (fun x=> Real.exp (rpay (tip G P.L x)* digits G p (tip G P.L x))) := by
    let f:=tip G P.L; let g x:= stockMove G p (f x); let m:= unit G p; have hM:0 < m:=wi G p
    have h : Rate G P.L (-(6/5)) g:= (Rate.power.mul_left (unit G p)).mul_left 2
    have hv : ∀ᶠ x:ℝ in atTop, 2*g x ≤ distance (f x):=by
       filter_upwards [((Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L)).eventually_ge_atTop 1),shiftedLog G P.L,h.mul_left 2 (-(1/2)) (by norm_num)] with x h hx hv
       apply (le_abs_self _).trans (hv.trans ?_); exact le_mul_of_one_le_right (Real.rpow_nonneg (by linarith only [hx.2.2.1]) _) h
    intro a b _
    let w:= |b|; filter_upwards [(Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G P.L)).eventually_ge_atTop (32*m*w), hv,shiftedLog G P.L] with x hx h ht
    let y:= tip G P.L x; let p0:= increments y; let d:=distance y; let H:= digits G p y; let c:= g x; have hy:1<y:=ht.2.2.1; have hg :0<y:=by linarith
    have hi:0< p0:=Real.rpow_pos_of_pos hg _; have hd:c=2*(m*p0):=rfl; have hC:0<c:=by rw [hd]; positivity
    have ha : (d/c)-1 ≤ H:= le_of_lt (Nat.sub_one_lt_floor _); have hE: d ≤ 2*c*(H:ℝ):=by
       have hf : d/c ≤ H+1 :=by linarith only [ha]
       have hs:= (div_le_iff₀ hC).mp hf; change 2*c ≤ d at h; linarith only [hs,h]
    have hL:0<Real.log y:=Real.log_pos hy; have hu:0<d:=mul_pos (Real.rpow_pos_of_pos hg _) hL; have he: y*d^2=(Real.log y)^2:=by unfold d distance; rw [Real.rpow_neg hg.le, ← Real.sqrt_eq_rpow]; field_simp; rw [Real.sq_sqrt hg.le] -- may
    rw [abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hg]; apply Real.exp_monotone; change rpay y * H≤Real.log y*b
    have hQ:= mul_le_mul_of_nonneg_left hE (show 0≤y*d from mul_nonneg hg.le hu.le); rw [hd] at hQ
    apply le_of_mul_le_mul_left (a:=m) _ hM; have ht:= mul_le_mul_of_nonneg_right (neg_abs_le b) (mul_nonneg hL.le hM.le); unfold rpay; change m * (-(y/8*(p0*d))* ↑H)≤ m* _
    have hv : m *(-(y/8*(p0*d))* ↑H) ≤ -(Real.log y)^2 /32:=by linarith only [hQ,he]
    have hb := mul_le_mul_of_nonneg_right (show 32*m*|b| ≤ Real.log y from hx) hL.le; refine hv.trans ?_; linarith only [hb, ht]
end YM.MSbar.Heath.Stock
