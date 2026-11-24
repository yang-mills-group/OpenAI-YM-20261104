import YM.AllOrder.Response.Stamp
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
open GaussianScore
variable {Y X:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y][BorelSpace Y] (μ:Measure Y)[μ.IsAddHaarMeasure]
    {Γ:Law Y}{E:Book (X×Y)} {V:X×Y→ℝ}{ρ:X→Y}{A H:ℝ×(X×Y)→ℝ}(h:Treaty V ρ A H){r:ℝ}
local notation "F"=> fderiv ℝ ρ 0
local notation "Ω"=> X×Y
set_option quotPrecheck false
local notation "Γ'"=> castle V ρ h.steer
local notation "S"=> Impulse F A H
variable {P:ℝ→X} (hp:ContDiffAt ℝ ω P 0)
local notation "Y₀"=> trust P (fderiv ℝ ρ 0)
local notation "T"=> (H ∘ tone (echo P) Y₀)
local notation "W"=> prepare A (echo P) Y₀ r
local notation "s"=> someJ (Real.exp ∘ (-forecast V P F))
lemma clear (h:E 0=0): EXP E 0=1:= funext fun x=> (show run Real.exp (swap E x) 0=1 from (run_zero ..).trans (by rw [swap, h]; exact Real.exp_zero)) -- edit
lemma toward (h:E 0=0):climate Γ μ E 0=1:=by funext x; unfold climate cloud bound; rw [clear h]; exact average_const ..
lemma climbable (h:∀ i,Plausible (E i))(h0:E 0=0): ∀ i,Plausible (climate Γ μ E i):= fun i=> smooth_bind Γ μ (exp_p h h0 i)
lemma climbers (h:∀ i,Plausible (E i))(h0:E 0=0): ∀ i,Plausible (connected Γ μ E i):= fun i=> log_p (climbable μ (Γ:=Γ) h h0) (toward μ h0) i

variable (he:0<H 0) (hr: 0<Laplace.curvature V (fderiv ℝ (echo P) 0 1) (fderiv ℝ (trust P (fderiv ℝ ρ 0)) 0 1)+r)
include hp he hr
lemma minted : Real.exp r • part μ W T = (H 0 * capital (Γ') μ) • plus s (weigh P (climate (Γ') μ S)):= by
 funext n; let L:=capital (Γ') μ; let p(i:ℕ)(y:Y):= weigh (fun x=>(P x,y)) (EXP S) i; let f y:= plus s (fun i=>p i y) n
 have he' i:= transport (Γ') μ hp (t:=EXP S) (fun i=>exp_p (fun i=> impulse_cost F A H i) (win0 _) i) i
 have hs : f= ∑ i ∈ Finset.antidiagonal n, (s i.1) • p i.2:= by ext1 x; rw [Finset.sum_apply]; exact plus_sum ..
 have hy: (Γ').average μ f= plus s (weigh P (climate (Γ') μ S)) n:= by rw [hs,plus_sum]; rw [average_sum _ _ (fun i _=> (he' i.2).1.scale (s i.1))]; apply Finset.sum_congr rfl; intro i hi; rw [average_scale,show (Γ').average μ (p i.2)=_ from (he' i.2).2]; rfl
 simp only [Pi.smul_apply,smul_eq_mul,part]
 have ht(y:Y): normTerm T W n (onLane y)= (Real.exp (-r)* H 0)* (f*(Γ').kern) y:= by
   calc _ = (Real.exp (-r)*(H 0 * (Γ').kern y))* f y := congr_fun (quoteP h hp he hr y) n
        _ = _:= by rw [Pi.mul_apply]; ring
 simp_rw [ht]; rw [integral_const_mul,←hy,Law.average, capital]; field_simp [Real.exp_neg, (show (∫ y, (Γ').kern y ∂μ) ≠0 from (capital_pos (Γ') μ).ne')]; rw [Real.exp_neg,mul_inv_cancel₀ (Real.exp_pos r).ne',one_mul]
lemma thermal : logS (Real.exp r • part μ W T)= just (Real.log (H 0 * capital (Γ') μ)) - someJ (forecast V P F)+ weigh P (connected (Γ') μ S) := by
   let f := weigh P (climate (Γ') μ S); have hs : 0<s 0:= (by rw [someJ_zero]; exact Real.exp_pos _); have hc: 0<f 0:=by unfold f; rw [weigh_zero,toward μ (E:=S) (win0 _)]; exact zero_lt_one
   have hw:0<H 0 * capital (Γ') μ:= mul_pos he (capital_pos (Γ') μ)
   have hδ:= smooth_top h hp
   rw [minted μ h hp he hr, ←exact_scale,log_mash (show 0< just _ 0 from hw) (show 0<plus s f 0 from (by rw [plus_ge]; exact mul_pos hs hc)),log_mash (a:=s) (b:=f) hs hc] -- abbrev f
   rw [conviction hδ, log_expS,log_const _ hw]
   rw [show logS f=weigh P (connected (Γ') μ S) from funext fun i=> (weigh_log hp (u:=climate (Γ') μ S) (fun i _=> (climbable μ (fun i=> impulse_cost F A H i) (win0 _) i).smooth.contDiffAt) (toward μ (win0 _)) (le_refl i)).symm]; rw [exact_neg («F»:=forecast V P F) ((lift_cost V F).smooth.contDiffAt.comp (f:=P) _ hp)]; abel
end YM.AllOrder.Response
