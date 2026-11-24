import YM.LocalTaylorR2.Exponent.Gavel

/-!
 # The portfolio fully earns Bank, at any density growth & polynomial rank limits stipulated.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}


lemma Debit (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(o:Target.Order G W)(m j k p:ℕ)(a:ℝ)(Φ:ℝ→ℝ)(hp:Rate G L a Φ): ∃ n X, Rate G L 0 X ∧ (∀ x,0≤X x) ∧ ∀ᶠ x in atTop, ∀ c f (S:StepData c f)(T:Tube G S)(R:Rep G f) μ C (H:Cash W x μ L Q o C T R), Bank H j k n (X x) m p (|Φ x|):=by
 let e z := betaF G z L; let y':= a*m; let Z:= k*j+p*m
 obtain ⟨E,hE,h₁⟩:= alarm_bills P L (-(2*y')-2) (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) (half_pos o.rare)
 have hV := Census.width_rate G L 1 0; simp only [one_mul,add_zero] at hV
 obtain ⟨D,k',hD,h₂⟩:= stockpile G L o (k*j)
 obtain ⟨F,l,hF,h₃⟩:= stockpile G L o (Z*2)
 let f x := 1+|F x|
 let y x:=(e x)^(-y'-1/2)
 have hh {g:ℝ→ℝ}{w:ℝ}(h:Rate G L w g) := h.compare (v:=fun x=>|g x|) (Eventually.of_forall fun x=>(abs_abs _).le)
 let X x:= |D x| + f x
 let n:= k'+l+1
 refine ⟨n,X,(hh hD).add ((Rate.const _).add (hh hF)), fun x=> add_nonneg (abs_nonneg _) (add_nonneg zero_le_one (abs_nonneg _)),?_⟩
 have hf:Rate G L (a*m+(-y'-1/2)) (fun x=> |Φ x|^m * y x) := ((hh hp).pow m).mul Rate.power
 filter_upwards [h₁,Delay.shift_pos G L,hf.below (by unfold y'; linarith) 1 zero_lt_one,(hV.mul hE) ((-y'-1/2)*2) (by linarith)] with x he hy hp hE c f' S T R μ C H
 refine ⟨?_⟩; intro F' Y hv' hK hY U A I A'
 have hB : Y.B=radiusB x:= congr_arg radiusB hv'; have hΦ:Rotator P L o.eta o.gap o.ample o.indexPay Y:= (H.laws.data.localP F' Y hv' hK hY).sails
 let B':=eerie Y (H.unionP U) (o.ξ/2) R.beta; let V:=1+H.shapeW U
 let w (z:Air f' G):= facescale I z; have hZ : Integrable A' Y.dice:= by dsimp only [A',I]; rw [←hB]; exact segregate _ _ _ _ Y (H.unionP U) hΦ
 have ht:0<y x:= Real.rpow_pos_of_pos hy _; have nz:1≤f x:= le_add_of_nonneg_right (abs_nonneg _); have hz:1≤V:= le_add_of_nonneg_right (H.positive_volume _)
 have hh : Y.dice.real B' ≤ (V*y x)^2 := by
    refine le_trans (fracas _ _ _ _ (g:=E x) ?_) ?_
    · intro i; simpa only [card_singleton,pow_one] using (he.2 _ _ S T F' Y hv' H.laws.data.funds.length_eq hΦ R (hv'.symm ▸ H.laws.intake) {i})
    calc
      _ ≤ V * ballCost (radiusB x)*E x:= by refine mul_le_mul_of_nonneg_right ((spaces H U).trans ?_) he.1; gcongr; unfold V; linarith
      _ ≤ V*(y x)^2:= by rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hz); unfold y; rw [← Real.rpow_mul_natCast hy.le]; norm_num; exact (le_abs_self _).trans hE
      _ ≤ _:= by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (le_self_pow₀ hz (by omega)) (sq_nonneg _)
 let U' z:= (w z)^Z
 let n' z:=(w z)^(k*j)
 let u z:= |Φ x|^m* B'.indicator U' z
 have hu':Integrable U' Y.dice:= (globes I hΦ Z).1; have hf : Integrable (B'.indicator U') Y.dice:= hu'.indicator (measurable_eerie ..)
 have hu: Integrable u Y.dice:=hf.const_mul _; have hn:Integrable n' Y.dice:= (globes I hΦ _).1
 have hA : (∫ z,B'.indicator U' z ∂ Y.dice) ≤ f x*V^l* (V*y x):= by
    refine divideC Y.dice U' hu' _ (by positivity) _ (measurable_eerie ..) hh (by positivity) ?_ ?_
    · unfold U'; simp_rw [← pow_mul]; exact (globes I hΦ (Z*2)).1
    unfold U'; simp_rw [← pow_mul]; apply (h₃ _ _ _ S T P Q C μ _ H _ Y hv' hK hY _).trans
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hz) _)).trans
      (le_self_pow₀ (one_le_mul_of_one_le_of_one_le nz (one_le_pow₀ hz)) (by omega))
 constructor; exact hZ
 calc
   _ ≤ ∫ z,(n'+u) z ∂Y.dice:= integral_mono hZ (hn.add hu) (fun z=>by
      unfold A'; have ht₀:=Flux.expenses I z|>.1
      by_cases h : z∈ B'; swap; · rw [Pi.add_apply]; unfold u; rw [Set.indicator_of_notMem h,mul_zero,add_zero,glacial,if_neg h,one_pow,one_mul]
      refine le_trans (b:=u z) ?_ (by rw [Pi.add_apply]; exact le_add_of_nonneg_left (pow_nonneg (zero_le_one.trans ht₀) _))
      apply le_of_eq; rw [glacial,if_pos h,hB,mul_pow]; unfold u; rw [Set.indicator_of_mem h]; unfold U' Z w; rw [pow_add,pow_mul]; dsimp only [I]; ring)
   _ = (∫ z,n' z ∂ Y.dice)+|Φ x|^m*(∫ z,B'.indicator U' z ∂Y.dice) := by rw [integral_add' hn hu]; unfold u; rw [integral_const_mul]
   _ ≤ |D x| *V^n + f x * V^n:=by
        refine add_le_add ((h₂ _ _ _ S T P Q C μ _ H _ Y hv' hK hY _).trans (by change |D x| *V^_ ≤ |D x| * V^_; unfold n; gcongr; omega)) ?_
        apply (mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ |Φ x|^m)).trans
        calc
         _ = (|Φ x|^m*y x)*(f x*V^(l+1)):=by ring
         _ ≤ f x*V^(l+1):= mul_le_of_le_one_left (by positivity) ((le_abs_self _).trans hp)
         _ ≤ f x*V^n:=by unfold n; gcongr; omega
   _ = _ := by unfold X V; ring
lemma storageUp {x':ℝ} (M:StoresR2 H j v d A D k x n χ) (h : n ≤ m)(hp:x ≤ x'):StoresR2 H j v d A D k x' m χ:=by
   refine ⟨M.sure.trans hp,M.fuel,M.flight,fun F X hx hk he ht Y=>?_⟩
   have hA:1≤1+H.shapeW Y:= le_add_of_nonneg_right (H.positive_volume Y); have hF:= M.sure
   apply (M.moment F X hx hk he ht Y).trans; gcongr; linarith
end YM.LocalTaylorR2.Exponent
