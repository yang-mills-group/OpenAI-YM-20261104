import YM.OPE.Compatible.Basil.Alert
/-!
# Height requirements: any polynomial on log, also arbitrary polynomial log rarity exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
abbrev echoL (G:Gauge)(L:Side) := Delay.bill G L
abbrev skimX (G:Gauge)(L:Side)(x:ℝ):= betaF G x L ^ (-(1/2:ℝ))
lemma echo_growth (G:Gauge)(L:Side):Tendsto (echoL G L) atTop atTop:=by
   let g(x:ℝ):=Real.log (betaF G x L)
   have he:Tendsto (fun x=>g x*g x) atTop atTop:= (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L))|>.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L))
   apply tendsto_atTop_mono _ he; intro i; change _≤1+_+g i^2;rw [pow_two]; apply le_add_of_nonneg_left; positivity
lemma boom (P:Teller G) (D:Patch) (L:Side)(_hD:D.Branches P.bind G)(K C' d η r U:ℝ) (hd : 0<K)(hC : 0<d) (_hh:Torch η r U) (ha:0≤C') (i j:ℕ) {z:ℝ→ℝ}(he:Rate G L (-1) z):
   ∃ n:ℕ, ∀ᶠ x:ℝ in atTop,
     let B:=echoL G L x; let g:=skimX G L x; let w:=g* B^i; let H := g*B^n
     ∃ k≥0, w ≤ d ∧ (Fintype.card G.ColorIndex:ℝ)*(2* Real.exp (-k+payE η r U (tubularPrice G L)/2)) ≤ Real.exp (-B^j)^2 ∧
       ∀ β:ℝ, betaF G x L / 2 ≤ β→
       let P:= C'*w+z x+ (gStep β) * ((Fintype.card G.ColorIndex:ℝ)*k)
       P≤ d ∧ K*P+K*w ≤ H := by
   let c:= (Fintype.card G.ColorIndex:ℝ); have hc:0≤c:=by unfold c; positivity
   let N:= i+j+2
   refine ⟨N+1,?_⟩
   let A:=echoL G L; let b(x):=A x^N
   have hv:Rate G L 0 b:=by simpa only [zero_mul] using! (Rate.bill.pow N)
   let t(x):=skimX G L x*b x; have ht: Rate G L (-(1/2)) t:=by simpa only [add_zero] using ((Rate.power (a:=-(1/2:ℝ))).mul hv)
   let g(x):=t x*(C'+1+2*c); have hG: Rate G L (-(1/2)) g:= ht.mul_right _; let p:= payE η r U (tubularPrice G L)
   have hU : ∃ f:ℝ, c*2 * Real.exp (p/2)≤Real.exp f:= (Real.tendsto_exp_atTop.eventually_ge_atTop (c*2* Real.exp _)).exists
   obtain ⟨f,hf⟩:=hU
   filter_upwards [he _ (by norm_num:(-1:ℝ)< -(1/2)), echo_growth G L|>.eventually_ge_atTop (|f|+2),
     echo_growth G L|>.eventually_ge_atTop (K*(C'+1+2*c)+K), hG.below (by norm_num) _ hC,ht.below (by norm_num) _ hC,Delay.shift_pos G L] with x hx h h' hy hz hp B g' w H
   have hB:1≤ B:=Delay.bill_ge G L x; have hg:0≤ g' :=Real.rpow_nonneg hp.le _
   have hb :1≤b x:=one_le_pow₀ hB
   have hu : B^j * (|f|+2)≤ b x:= (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ B^j)).trans (by
        change B^j*B ≤ B^N; rw [←pow_succ]; exact pow_le_pow_right₀ hB (by unfold N; omega))
   have hw:w≤t x:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by unfold N; omega)) hg
   refine ⟨b x,zero_le_one.trans hb, hw.trans ((le_abs_self _).trans hz),?_, fun β H' =>?_⟩
   · change c*(2* Real.exp _)≤_
     rw [Real.exp_add,← Real.exp_nat_mul]
     calc
       _ ≤ c*2* Real.exp (p/2)*Real.exp (-(b x)) := le_of_eq (by ring)
       _ ≤ Real.exp f * Real.exp (-b x) := mul_le_mul_of_nonneg_right hf (by positivity)
       _ ≤ _ := by
         rw [← Real.exp_add]; apply Real.exp_monotone; norm_num
         nlinarith only [hu,le_abs_self f,mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=j) hB) (abs_nonneg f)]
   intro P
   let k:=gStep β; have hβ:0<β:=lt_of_lt_of_le (div_pos hp zero_lt_two) H'
   have hv : k≤2*g':=by
      unfold k g' skimX gStep; rw [Real.rpow_neg hp.le,← Real.sqrt_eq_rpow]; have hz:=Real.sqrt_pos.mpr hβ; have hu:=Real.sqrt_pos.mpr hp
      field_simp; nlinarith [Real.sq_sqrt hp.le,Real.sq_sqrt hβ.le]
   have H : P≤g x:=by -- binds H reserved
      apply le_trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hw ha) ((le_abs_self _).trans (hx.trans (le_mul_of_one_le_right hg hb)))) (mul_le_mul_of_nonneg_right hv (mul_nonneg hc (zero_le_one.trans hb))))
      apply le_of_eq; unfold g t; ring
   refine ⟨H.trans ((le_abs_self _).trans hy),?_⟩
   apply le_trans (add_le_add (mul_le_mul_of_nonneg_left H hd.le) (mul_le_mul_of_nonneg_left hw hd.le)); have he' := mul_le_mul_of_nonneg_left h' (show 0 ≤ t x from mul_nonneg hg (zero_le_one.trans hb)); unfold g; change _ ≤ g'*B^(N+1); rw [pow_succ,←mul_assoc g',show g'*B^N=t x from rfl]; linarith
end YM.PhysicalNext.Repeat.Aroma
