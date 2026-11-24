import YM.MS.Rake.CapWin
/-!
# Continuum lengths all and symbol comparison exchange. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
  {S:Scale I}{a b z:I→ℝ}{n:ℤ}{f:E→F}
def PlanetD (G:Gauge) : ℝ→ Edge G:= (spaceD G).meter
abbrev total (S: Scale I)(f:I→ E→F)(k:I→ℝ): Prop:= Line S (fun _=>Set.univ) f k -- use Plasma, Total conflict
abbrev era (a:ℝ)(f:E→F) (k:ℤ)(p:E): F:= a^k • f (a • p) -- ambiguity (real or a^ powering int)
lemma grow_r (hp:ContDiff ℝ ∞ f)(t:ℝ) : ContDiff ℝ ∞ (era t f n):= by unfold era; fun_prop
lemma era_spec {b':ℝ}(h:0<b')(hx:ContDiff ℝ ∞ f) (j:ℕ)(k:E) : ‖iteratedFDeriv ℝ j (era b' f n) k‖ = b'^( ( j:ℤ )+n ) * ‖iteratedFDeriv ℝ j f (b' • k)‖:= by
    let P:ContDiff ℝ ∞ (fun p=> f (b' • p)) := hx.comp (f:=fun p:E=> (b' • p)) ( contDiff_const.smul contDiff_id ); change ‖iteratedFDeriv ℝ j ((b'^n) • fun p:E=> f (b' • p)) k‖ = _; rw [ iteratedFDeriv_const_smul_apply (P.contDiffAt.of_le (by exact_mod_cast le_top)),norm_smul, iteratedFDeriv_comp_const_smul b' (hx.of_le (by exact_mod_cast le_top)), norm_smul,zpow_add₀ h.ne', zpow_natCast,Real.norm_of_nonneg (zpow_nonneg h.le _), norm_of_nonneg (pow_nonneg h.le _) ]; ring
lemma balance (h: Line (Job.single Unit) (fun _=>Set.univ) (fun _ => f) 1)(b j:ℕ): ∃ C:ℝ,0<C∧∀ p, ‖iteratedFDeriv ℝ j f p‖ ≤ C/ (1+‖p‖)^b := by obtain ⟨C,hC,v,hV⟩:= (h b).quoted j; exact ⟨C,hC,fun p=> (by simpa [Scale.strict,Scale.weight, Job.single, div_eq_mul_inv] using hV () p trivial)⟩
lemma fullE (h: total (Job.single Unit) (fun _=> f) 1): total S (fun i=>era (S.length i) f n) (fun i=> S.length i^n):= by
   intro b; refine ⟨fun i=>grow_r (h b|>.smooth ()) _, fun j=>?_⟩; obtain ⟨C,hC,H⟩:= balance h b j; refine ⟨C,hC,0,fun i p hp=>?_⟩; dsimp only; rw [era_spec ( S.pos i ) (h b |>.smooth ()), pow_zero,mul_one];
   obtain hu:= H (S.length i • p); rw [norm_smul_of_nonneg (S.pos i).le] at hu; change _ ≤ C / S.weight i p^b at hu; apply (mul_le_mul_of_nonneg_left hu (zpow_nonneg (S.pos i).le (j+n:ℤ)))|>.trans_eq; rw [zpow_add₀ ( S.pos i|>.ne' ),zpow_natCast]; ring
-- pull from approximate scale.L.S.Globalization. Compact.P.use Alps.limitL rails or direct.
lemma planetEra (i j:BH G)(p:ℝ) : PlanetD G p i j= era (exp p) ( PlanetD G 0 i j ) ((4:ℤ) - wfield i-wfield j):= by
   ext x; obtain h:= congr_arg (fun U:Arts.Rip G=> U 0 i j x) ( Wick.pA G p ); change Alps.amount ( (4:ℂ) - wfield i-wfield j ) p * PlanetD G 0 i j (exp p • x) = _ at h; refine h.symm.trans ?_; unfold era; let K:ℤ:=4-wfield i-wfield j; rw [show ( (4:ℂ) - wfield i-wfield j )=(K:ℝ) from (by push_cast [K]; rfl),Alps.amount_mint, ← Real.rpow_intCast, ← Real.exp_mul p]; rw [mul_comm _ p]; rfl -- exp*z orientation
lemma star_r (i j:BH G): total (Job.single Unit) (fun _=> PlanetD G 0 i j) 1 := by
    obtain he := (line_meter (ι:=Unit) (C:=G.ColorIndex) ( S:=Job.single Unit ) (fun _=>le_rfl) ( a:=phaseDiff (Job.single Unit)) (fun _=>le_rfl) i j).std; refine ?_; unfold total; simp only [ Job.cw,one_zpow ] at he; simp only [ PlanetD,High.spaceD,Landau.zD, exp_zero]; exact he -- π
lemma cost_D (h:∀ i,exp (a i)=S.length i): Sheet S 1 (fun i=> PlanetD G (a i)):= by intro i j; convert fullE (S:=S) (star_r i j) (n:= ( (4:ℤ) - wfield i-wfield j)) using 1; ext; dsimp only; rw [ planetEra i j (a _),h ]; ext; simp
lemma crossD (G: Gauge)(i j:BH G)(p:QP): Continuous fun t:ℝ=> PlanetD G t i j p:= by
   rw [show (fun t=>PlanetD G t i j p)= _ from funext fun t=>congr_fun (planetEra i j t) p]; unfold era; exact Continuous.smul (M:=ℝ) (continuous_exp.zpow₀ _ (fun p=>Or.inl ((exp_pos p).ne'))) ((star_r i j 0 |>.smooth () ).continuous.comp ( continuous_exp.smul continuous_const )) -- Natural ℝ^ℤ
-- close on lattice seam & stage met
variable (h:∀ i,1≤ S.length i)(he:∀ i,exp (a i)=S.length i)
include h he
lemma visited (hp:∀ i, phaseDiff S i ≤ z i)(s t:BH G): Sharp S z (fun _=> firstZone Axis) (fun i=> LowP G (a i) s t) (fun i=> PlanetD G (a i) s t) (fun i=> S.length i ^ ((4:ℤ)-wfield s-wfield t)):= by
   unfold LowP PlanetD High.spaceL High.spaceD zL zD; simp only [ he ]; exact line_meter h hp s t
lemma Mate0 : Sheet S 1 (fun t=>PlanetL G (a t)):= by
   intro u v; simp only [ Pi.one_apply,mul_one]; exact folding ( F:=(fun i=> (LowP G (a i)) u v)) (visited h he (z:=phaseDiff S) (fun i=>le_rfl) u v|>.lattice) (fun i=>cityLine (nearL G (a i)) u v) h
lemma CoupleY : CourseK S 1 (fun t=> LowP G (a t)):= by
   intro u v; simp only [Pi.one_apply,mul_one]; exact (visited h he ( z:= phaseDiff S) (fun i=>le_rfl) u v).both.lat
lemma submarineT (hp:∀ i,phaseDiff S i ≤ z i): CourseK S z (fun t=>LowP G (a t)- PlanetD G (a t)):= fun i j=> ( visited h he hp i j ).both.gain
lemma submarineP (hp:∀ i,phaseDiff S i ≤ z i): Sheet S z (fun t=> PlanetL G (a t)- PlanetD G (a t)):= fun i j=> Hydro ( visited h he hp i j ) (fun i' => cityLine ( nearL G (a i')) i j) h (k:=2) hp
end YM.MS.Rake
