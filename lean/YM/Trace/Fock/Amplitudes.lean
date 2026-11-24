import YM.Trace.Fock.Coherent

/-!
Translation diagonalization on each full Fock slot. Coefficients are from an actual
common set of Schwartz amplitude divisions (only vacuum waves are used). With
`FieldsNorm` for their trace, energy balls are bounded by its same positive
scalar measure and give polynomial budgets, before any logarithmic estimate.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace.Shell
open YM Boundary Function MeasureTheory Filter Set Complex
open scoped Topology ENNReal BigOperators InnerProductSpace Pointwise
variable {m n : ℕ}
variable (v : Test4 →L[ℂ] Sum m) (h : FieldImage v)
abbrev vSector (n) : Test4 →L[ℂ] Wave m n := (lp.evalCLM ℂ (Wave m) 2 n).comp v

include h in
private lemma cov (x a p) : ∀ᵐ z ∂νpow p, vSector v p (Probe.ahead a x) z = phase a z • vSector v p x z := h.covariance x a p
private lemma sector_conv (x a) (ha : CC a) (p) : vSector v p (conv a x) = ∫ b:E4, a b • vSector v p (Probe.ahead b x) :=
   wave_integral_test (H:=⟨Wave m p⟩) (vSector v p) a x ha

@[fun_prop] lemma wave_meas (b : Wave m n) : Measurable (⇑b : Cords n→Fiber m n) :=
    StronglyMeasurable.measurable (AEEqFun.stronglyMeasurable _) -- infer explicit
@[fun_prop] lemma phase_diag (z : Test4) : Measurable (fun p : Cords n => plus z (total p)) := by fun_prop
@[fun_prop] lemma phase_cont : Continuous (fun p : E4 × Cords n => phase p.1 p.2) := by unfold phase; fun_prop
def smearCost (z : Test4) : ℝ := Probe.size 0 0 (plus z)
lemma positive_cost (z : Test4) : 0≤smearCost z := by unfold smearCost; exact apply_nonneg ..
lemma phase_limit (z : Test4) (p : Cords n) : ‖plus z (total p)‖ ≤ smearCost z :=
   SchwartzMap.norm_le_seminorm ℂ ..
lemma multiply_mem (b:Wave m n) (z : Test4) : MemLp (fun p : Cords n => (plus z (total p)) • b p) 2 (νpow n) :=
    (Lp.memLp b).of_le_mul (c:=smearCost z) (by fun_prop) (.of_forall fun k => (norm_smul ..).trans_le (mul_le_mul_of_nonneg_right (phase_limit ..) (norm_nonneg ..)))

include h in
private lemma state_conv (x a) (ha : CC a) (p) : vSector v p (conv a x) = (multiply_mem (vSector v p x) a).toLp _ := by
    rw [sector_conv _ _ _ ha]; refine ext_inner_left ℂ fun b=>?_ -- arg count
    let y := vSector v p x
    have he (q r) : inner ℂ (b q) (r • y q)= (r:ℂ) * inner ℂ (b q) (y q) := by rw [inner_smul_right]
    rw [L2.inner_def b (MemLp.toLp ..)];
    have hEq : (↑↑((multiply_mem (vSector v p x) a).toLp _) : Cords p→Fiber m p) =ᵐ[νpow p] (fun k=> (plus a (total k)) • y k) := (multiply_mem ..).coeFn_toLp
    have hx := ((a.continuous.smul ((vSector v p).continuous.comp (Work.C14.ahead_cont x))).integrable_of_hasCompactSupport ha.smul_right (μ:=volume))
    rw [integral_congr_ae (hEq.mono fun q hq=> show _=(plus a (total q)) * inner ℂ (b q) (y q) from congr_arg (inner ℂ (b q)) hq |>.trans (he ..))];
    refine Eq.trans (_root_.integral_inner (𝕜:=ℂ) hx b).symm ?_
    dsimp only [Pi.smul_apply,comp_def]
    have ha' := a.continuous.integrable_of_hasCompactSupport ha (μ:=volume)
    let G (q:E4) (k:Cords p) := (a q * phase q k) * inner ℂ (b k) (y k)
    have hj : Integrable (uncurry G) ((volume:Measure E4).prod (νpow p)) := by
       refine (ha'.norm.mul_prod (μ:=volume) (MeasureTheory.L2.integrable_inner (𝕜:=ℂ) b y).norm).mono' (by unfold G uncurry; fun_prop)
          (.of_forall (fun k=> by change ‖G _ _‖ ≤ _; unfold G; simp_rw [norm_mul]; simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (plane_bound ..) (norm_nonneg _)) (norm_nonneg _)))
    calc _ = ∫ b':E4, ∫ k, G b' k ∂νpow p := ?_
         _ = ∫ k, ∫ b':E4, G b' k ∂(volume:Measure E4)∂νpow p := integral_integral_swap hj
         _ = _ := ?_
    · refine integral_congr_ae (.of_forall fun j => ?_)
      change inner ℂ b (a j • _) = ∫ k, G j k ∂νpow p; rw [inner_smul_right,L2.inner_def, ← MeasureTheory.integral_const_mul]; exact integral_congr_ae ((cov v h x j p).mono fun i hi=> by dsimp only [G]; rw [hi,inner_smul_right,mul_assoc])
    refine integral_congr_ae (.of_forall fun j=> ?_)
    change (∫ a:E4,G a j)=plus a (total j) * _; unfold G; rw [MeasureTheory.integral_mul_const]; congr 1
    rw [plus_eq]; apply integral_congr_ae; filter_upwards with i; unfold phase; rw [mul_comm,Probe.plane_dot (_:E4)] -- lookup

private noncomputable def coverTest : ℕ → Test4 := Classical.choose (plus_fits (V:=E4))
private lemma covers_prop : (∀ i:ℕ, CC (coverTest i)) ∧ ∀ p, ∃ i, plus (coverTest i) p ≠0 := Classical.choose_spec (plus_fits (V:=E4))
open Classical in
noncomputable def coverIndex (p:E4) : ℕ := Nat.find (p:=fun i => plus (coverTest i) p ≠0) (covers_prop.2 p)
open Classical in
lemma available (p) : plus (coverTest (coverIndex p)) p ≠ 0 := Nat.find_spec (covers_prop.2 p)
lemma available_meas : Measurable coverIndex := by
   open Classical in
   apply Measurable.find (f:=fun n (x:E4)=>n) (p:=fun i p=> plus (coverTest i) p ≠0) (by fun_prop) (by
     exact fun n=> ((plus _).continuous.isOpen_support.measurableSet)) (covers_prop.2)
noncomputable def coefficientFunction (n) (p : Cords n) (j : ℕ) : Fiber m n := (plus (coverTest j) (total p))⁻¹ • v (coverTest j) n p
noncomputable def fullWave (n) (p : Cords n) : Fiber m n := coefficientFunction v n p (coverIndex (total p))

include h in
private lemma sector_ident (a : Test4) (ha : CC a) (b : Test4) (hb : CC b) :
     ∀ᵐ k ∂νpow n, (plus a (total k)) • v b n k = (plus b (total k)) • v a n k := by
   have hi := state_conv _ h b a ha n; rw [conv_comm, state_conv _ h a b hb n] at hi
   exact (EventuallyEq.trans ((multiply_mem (vSector v n b) a).coeFn_toLp |>.symm) (by rw [← hi]; exact MemLp.coeFn_toLp ..)) -- fix type
   -- equality of functions eventual
omit h in
private lemma vphase_meas (j : ℕ) : Measurable (fun p=> coefficientFunction v n p j) := by
     unfold coefficientFunction
     exact Measurable.smul ((phase_diag (coverTest _) (n:=n)).inv) (wave_meas _)
omit h in
lemma fullWave_meas (n) : Measurable (fullWave v n) := by
      open Classical in
      have HE := Measurable.find (f:=fun j p=>coefficientFunction v n p j) (p:=fun i p=>plus (coverTest i) (total p) ≠ 0)
             (fun j=> vphase_meas ..) (fun i=> by exact MeasurableSet.compl ((measurableSet_eq_fun (phase_diag ..) measurable_const)))
             (fun p=>covers_prop.2 (total p))
      convert HE using 1; funext x; unfold fullWave coverIndex; congr 1

include h in
lemma fullWave_of_CC (f : Test4) (hf : CC f) (n) : (⇑(v f n) : Cords n→ Fiber m n) =ᵐ[νpow n] fun p=> plus f (total p) • fullWave v n p := by
      refine (ae_all_iff.mpr (fun i : ℕ=> sector_ident v h (n:=n) f hf (coverTest i) (covers_prop.1 i))).mono fun p hp => ?_
      unfold fullWave coefficientFunction; dsimp
      rw [smul_comm _ (plus (coverTest _) (total _))⁻¹,hp, smul_smul, inv_mul_cancel₀ (available _), one_smul]

end YM.Trace.Shell
