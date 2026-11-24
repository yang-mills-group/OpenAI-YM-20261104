import YM.LocalLTE.Newborn.Evo
/-! Rate conversion: for the chosen order, both inlet scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open LocalLTE.Inset Org
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open ClockB Urns
open LocalLTE.Fan LocalLTE.Fan.Pastel Coat
variable {G:Gauge}(L:Side)(p M:ℕ)
-- x to 2*z band covers both adjacent. b≥ x/2>0. r = κ
local notation "f" x => betaF G x L
lemma flagE (l:ℝ) (hl:l ≤0) : Rate G L l (fun x:ℝ=> x^l):= by
    let u:ℝ→ℝ:=fun x=> betaF G x L/2
    have hh: Rate G L l (fun x=>u x^l):= by
       refine Rate.compare ((Rate.power (G:=G) (L:=L) (a:=l)).mul_right ((2:ℝ)^l)⁻¹) (?_)
       filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; unfold u; rw [Real.div_rpow (show 0≤betaF G x L from hx.trans_le (le_add_of_nonneg_right (Work.E04.shift_nonneg ..))|>.le) zero_le_two,div_eq_mul_inv]
    refine hh.compare ?_; filter_upwards [eventually_ge_atTop (G.slopeConstant*Real.log (L.val)), eventually_gt_atTop (0:ℝ)] with x h hx; have he:u x ≤ x:= by change (x+_)/2 ≤ x; linarith only [h] -- sign
    have hv: 0< u x:=half_pos (hx.trans_le (le_add_of_nonneg_right (Work.E04.shift_nonneg ..)))
    rw [abs_of_nonneg (Real.rpow_nonneg hx.le _), abs_of_nonneg (Real.rpow_nonneg hv.le _)]; exact Real.rpow_le_rpow_of_nonpos hv he hl
lemma cheapest (r:ℝ): Rate G L r (fun x=> Urns.divisor x):=by
   -- along p log asymptotic vs power betaF negative. use Timing.hard_growth2
   intro z hz; let v:=min 0 z
   filter_upwards [eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually (Timing.hard_growth 2), (eventually_ge_atTop (G.slopeConstant *Real.log L.val)), Real.tendsto_log_atTop.eventually_ge_atTop (2:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (-4*v)] with x hx h hL ht hv
   have he:=zero_lt_one.trans hx; have hB:x ≤ f x:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
   rw [abs_of_pos (Urns.nonzero _)]
   apply le_trans (b:=(f x)^v) _ (Real.rpow_le_rpow_of_exponent_le (hx.le.trans hB) (min_le_right ..)); have hF : (betaF G x L) ≤2*x:=by change x+G.slopeConstant*Real.log _ ≤ 2*x; linarith only [hL]
   apply le_trans (b:=(2*x)^v) _ (Real.rpow_le_rpow_of_nonpos (he.trans_le hB) hF (min_le_left ..))
   unfold Urns.divisor Vac.Numbers.P; rw [Real.sqrt_eq_rpow,← Real.exp_mul,Real.rpow_def_of_pos (mul_pos zero_lt_two he),Real.log_mul (by norm_num) he.ne',← Real.exp_mul, Real.exp_le_exp]; have hp:Real.log 2 ≤ Real.log x:=by linarith only [ht,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
   have hz:=min_le_left 0 z
   rw [show (Real.log (Real.log x))^2*(1/5:ℝ)=(Real.log (Real.log x))^2/(5:ℝ) by ring]
   have hy: v * (Real.log 2+Real.log x) ≥ v *(Real.log x+Real.log x):= mul_le_mul_of_nonpos_left (add_le_add_left hp _) hz -- edit
   nlinarith only [h,hy, mul_le_mul_of_nonneg_right hv (Real.log_nonneg hx.le)]
-- Bill threshold extra choose p M large. κ derivative ≤ cost
lemma estate (S:Stage) (hM: Pastel.chip (M+1)+1< -(↑(p+1):ℝ)/2) : ∀ᶠ x:ℝ in atTop, ∀ β:ℝ,x/2≤β→ β≤2*betaF G x L → let e:=gStep β^((p:ℝ)+1); let t:= betaF G x L; let u:=Pressure.temp x; let v:= t^(chip (M+1)); (x^(chip (M+1))) ≤ e ∧ Urns.divisor x ≤ e ∧ 2*Time.credit G S * v / u^2 ≤ e := by
   let c:= Pastel.chip (M+1); have hh:c <0:=by linarith only [hM,Nat.cast_nonneg (α:=ℝ) (p+1)]
   let V(x:ℝ):=2*Time.credit G S * (betaF G x L)^c/(Pressure.temp x)^2
   have he:Rate G L (c+1) V:= by unfold V; simp_rw [div_eq_mul_inv]; exact (((Rate.power).mul_left _).mul (Price.curveT G L)) -- edit
   filter_upwards [Urns.actualG L (↑(p+1)) _ _ (flagE (G:=G) L c hh.le) (show c< _ by linarith only [hM]), Urns.actualG L _ _ _ (Mallow.cheapest (G:=G) L (c+1)) hM, Urns.actualG L _ _ _ he hM,eventually_gt_atTop (0:ℝ)] with x hx hy hf ht β hβ hB
   intro e t u w; let b:=2*t; have hz:0<t:= ht.trans_le (le_add_of_nonneg_right (Work.E04.shift_nonneg ..))
   have he : t/2 ≤b:=by unfold b; linarith
   have hh: gStep b ^ (↑(p+1):ℝ) ≤e:=by
       unfold e; push_cast; have hp:0<β:= (half_pos ht).trans_le hβ
       exact Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt hB)) (by positivity)
   exact ⟨(hx b he le_rfl|>.trans hh), (hy b he le_rfl|>.trans hh),(hf b he le_rfl|>.trans hh)⟩
variable {s:Sheet G}{D:Rolls s}{P:Protection D}
def Outlook (V:Delays P) : Prop:=∀ j i,StepStages j i→∀ x ≥ V.betaEntry j,∀ β:ℝ,x/2≤β →β≤ 2*betaF G x (D.L j)→let e:=gStep β^((p:ℝ)+1); let u:=Pressure.temp x; x^(chip (M+1)) ≤ e ∧ Urns.divisor x ≤ e ∧ 2*Time.credit G (s.profile i)*(betaF G x (D.L j))^(chip (M+1))/u^2 ≤ e
lemma forecast (h:Pastel.chip (M+1)+1 < -(↑(p+1):ℝ)/2) (V:Delays P) : ∃ W:Delays P, DelayLe V W∧∀ Y : Delays P,DelayLe W Y→ Outlook p M Y:= by
    obtain ⟨x,-,hx,hV⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (fun i _=> estate (D.L j) p M (s.profile i) h)); exact ⟨{V with betaEntry:=x},⟨hx,le_rfl, le_rfl,le_rfl⟩,fun Y h i j hi t ht=> hV i t ((h.beta i).trans ht) j hi⟩
end YM.PhysicalNext.Repeat.Mallow
