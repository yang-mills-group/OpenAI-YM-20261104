import YM.Integration.WilsonPositionDetectorMeshPrice

/-! Polynomial growth of every fixed-order bare position thermometer coefficient on the
independently filed original auxiliary regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionBareDetectorGrowth
open Filter Finset Set Maxwell XSpace XSpace.Cirrus FVA2 FVA2.Register FVA2.Scale MS MS.Land
open PowerSeries
open scoped Topology BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M σ dial)

def priced (a : ℕ → ℂ) : Prop :=
  ∃ p : ℝ[X], ∀ᶠ i : ℕ in atTop, ‖a i‖ ≤ p.eval (i:ℝ)

private theorem bounded {a : ℕ → ℂ} {s : ℂ} (h : Tendsto a atTop (𝓝 s)) : priced a :=
  ⟨Polynomial.C (1+‖s‖),(h.norm.eventually_lt_const (by linarith : ‖s‖<1+‖s‖)).mono
    (fun i hi=>by simpa using hi.le)⟩

private theorem sum {ι : Type} [DecidableEq ι] (u : Finset ι) (a : ι → ℕ → ℂ)
    (h : ∀ j∈u, priced (a j)) : priced (fun i=>∑ j∈u,a j i) := by
  induction u using Finset.induction_on with
  | empty => exact ⟨0,Eventually.of_forall fun i=>by simp⟩
  | @insert j s hj ih =>
    obtain ⟨b,hb⟩ := h j (mem_insert_self ..)
    obtain ⟨c,hc⟩ := ih (fun k hk=>h k (mem_insert_of_mem hk))
    refine ⟨b+c,?_⟩
    filter_upwards [hb,hc] with i hi hj'
    rw [sum_insert hj,Polynomial.eval_add]
    exact (norm_add_le ..).trans (add_le_add hi hj')

private theorem prod {a b : ℕ → ℂ} (ha : priced a) (hb : priced b) : priced (fun i=>a i*b i) := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hb
  refine ⟨p*q,?_⟩
  filter_upwards [hp,hq] with i h k
  rw [norm_mul,Polynomial.eval_mul]
  exact mul_le_mul h k (norm_nonneg _) ((norm_nonneg _).trans h)

private theorem sub {a b : ℕ → ℂ} (ha : priced a) (hb : priced b) : priced (fun i=>a i-b i) := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hb
  refine ⟨p+q,?_⟩
  filter_upwards [hp,hq] with i l r
  rw [Polynomial.eval_add]
  exact (norm_sub_le ..).trans (add_le_add l r)

private theorem angle (i : ℕ) :
    Arrival.Schedule.theta (Z.run.step i) = i * Real.log Z.run.ratio := by
  have r0 : (1:ℝ) ≤ (Z.run.ratio:ℝ) := by exact_mod_cast ((by decide : 1≤3).trans Z.run.large)
  change max (-Real.log (((Z.run.ratio^i:ℕ):ℝ)⁻¹)) 0 = _
  rw [Nat.cast_pow,Real.log_inv,neg_neg,Real.log_pow,max_eq_left]
  positivity

private theorem reset_power (u k : ℕ) :
    priced (fun i=>coeff k (Dframe.reset 0 σ (Z.run.step i)^u)) := by
  obtain ⟨w,hw,he⟩ := (Book.Program.shiftR σ.team).pow u k
  obtain ⟨p,rfl⟩ := hw.scalar
  let b : ℝ[X] := p.comp (-Polynomial.C (Real.log Z.run.ratio)*Polynomial.X)
  refine ⟨1+b^2,Eventually.of_forall fun i=>?_⟩
  change ‖coeff k (Book.Program.shift σ.team (0-Arrival.Schedule.theta (Z.run.step i))^u)‖ ≤ _
  rw [show coeff k (Book.Program.shift σ.team (0-Arrival.Schedule.theta (Z.run.step i))^u) =
      ((p.eval (0-Arrival.Schedule.theta (Z.run.step i)):ℝ):ℂ) from congrFun he _,angle]
  simp only [Complex.norm_real,Real.norm_eq_abs,Polynomial.eval_add,Polynomial.eval_one,
    Polynomial.eval_pow,b,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_C,Polynomial.eval_X,zero_sub]
  rw [show -((i:ℝ)*Real.log Z.run.ratio) = -Real.log Z.run.ratio*(i:ℝ) from by ring]
  nlinarith [sq_nonneg (|p.eval (-Real.log Z.run.ratio*(i:ℝ))|-1/2),
    sq_abs (p.eval (-Real.log Z.run.ratio*(i:ℝ)))]

private theorem top (a : PowerSeries ℂ) (z : constantCoeff a=0) (one : coeff 1 a=1) (k : ℕ) :
    coeff k (a^k) = 1 := by
  obtain ⟨b,hb⟩ := PowerSeries.X_dvd_iff.mpr z
  have b0 : constantCoeff b=1 := by
    simpa [hb,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_eq_constantCoeff_apply] using one
  rw [hb,mul_pow]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply,b0] using PowerSeries.coeff_X_pow_mul (b^k) k 0

include H in
theorem detector (k : ℕ) : priced (fun i=>coeff k (Rose.Detector Z.scheme Z.criterion (Z.run.step i))) := by
  let A (i : ℕ) := Dframe.reset 0 σ (Z.run.step i)
  let D (i : ℕ) := Rose.Detector Z.scheme Z.criterion (Z.run.step i)
  have res (j : ℕ) : priced (fun i=>coeff j (PowerSeries.subst (A i) (D i))) := by
    have h := Reg.Choice.Det 0 Z.scheme Z.criterion σ M g H.details.born.Taylor H.details.born.still H.details.born.base j
    exact bounded (h.comp H.onSchedule)
  change priced (fun i=>coeff k (D i))
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    let h (j i : ℕ) := coeff j (D i)*coeff k (A i^j)
    have previous : priced (fun i=>∑ j∈range k,h j i) := sum _ _ (fun j hj=>
      prod (ih j (mem_range.mp hj)) (reset_power Z j k))
    have equal (i : ℕ) : coeff k (D i) = coeff k (PowerSeries.subst (A i) (D i)) -
        ∑ j∈range k,h j i := by
      have z : constantCoeff (A i)=0 := by
        simpa [Book.Program.Rooted,PowerSeries.coeff_zero_eq_constantCoeff_apply,A,Dframe.reset] using
          Book.Program.share σ.team (0-Arrival.Schedule.theta (Z.run.step i))
      have n : coeff 1 (A i)=1 := Book.Program.ann σ.team _
      rw [FPS.coeff_substituted (D i) z k,Finset.sum_range_succ,smul_eq_mul,top _ z n,mul_one]
      simp only [smul_eq_mul,h]; ring
    simpa only [←funext equal] using sub (res k) previous

include H in
theorem chosen (k : ℕ) : priced (fun i=>coeff k (Rose.chosen Z.scheme Z.criterion (Z.run.step i))) := by
  by_cases e : k=0
  · subst k
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,Rose.zero_choice]
    exact bounded tendsto_const_nhds
  simp_rw [Rose.puts Z.scheme Z.criterion _ k e]
  exact prod (bounded tendsto_const_nhds) (detector Z H k)

include H in
theorem mass (q : ℕ) : ∃ p : ℝ[X], ∀ᶠ i : ℕ in atTop,
    WilsonPositionRawMesh.mass Z (Z.run.step i) q ≤ p.eval (i:ℝ) := by
  choose t ht using fun j : Fin (q+1)=>chosen Z H j
  refine ⟨∑ j,t j,?_⟩
  have good := eventually_all.mpr ht
  filter_upwards [good] with i hi
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_le_sum (fun j _=>(Complex.abs_re_le_norm _).trans (hi j))

end YM.Integration.WilsonPositionBareDetectorGrowth
