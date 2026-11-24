import YM.Integration.OriginalMarkedRowCovariance
import YM.Push.GRID_APPROXIMATION.Hit

/-! Actual signed single-row Gibbs responses, paid at their designated
sites with the original exponential charge for every support reaching
a second prescribed site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedRowPrice
open Filter Function Finset MeasureTheory Lattice RG Wilson
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open OriginalMarkedRunAction OriginalMarkedRunCovariance OriginalMarkedRowCovariance
open Push.GridApprox.Attach
open scoped BigOperators Classical Topology

private theorem exponential_span (a : ℝ) :
    Real.exp a - Real.exp (-a) ≤ 2*a*Real.exp a := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2*a)) (Real.exp_pos a).le
  rw [← Real.exp_add,show a+ -2*a = -a by ring] at h
  linarith

private theorem centered_scalar {z k : ℝ} (hz : 0<z) (hk : 0<k) (A B : ℂ) :
    (z:ℂ)⁻¹*B-(k:ℂ)⁻¹*A = (z:ℂ)⁻¹*(B-((z/k:ℝ):ℂ)*A) := by
  rw [Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hz.ne',Complex.ofReal_ne_zero.mpr hk.ne']

private theorem inverse_price {k z a : ℝ} (low : k*Real.exp (-a)≤z) (hz : 0<z) :
    z⁻¹*k ≤ Real.exp a := by
  rw [← div_eq_inv_mul,div_le_iff₀ hz]
  calc k = (k*Real.exp (-a))*Real.exp a := by rw [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
       _ ≤ z*Real.exp a := mul_le_mul_of_nonneg_right low (Real.exp_pos _).le
       _ = _ := mul_comm ..

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

private theorem integrable_test {k : X→ℝ} (e : Envelope k) (f : X→ℂ) (hf : Measurable f)
    (M : ℝ) (cap : ∀ U, ‖f U‖ ≤ M) : Integrable (fun U => (k U:ℂ)*f U) μ := by
  apply ((e.integrable μ).norm.mul_const M).mono' ((Complex.measurable_ofReal.comp e.meas).mul hf).aestronglyMeasurable
  refine ae_of_all _ fun U => ?_
  change ‖(k U : ℂ) * f U‖ ≤ ‖k U‖ * M
  rw [norm_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (cap U) (norm_nonneg _)

/-- A bounded single positive tilt of any finite positive density, with
the denominator recomputed in the same law. -/
theorem normalized_tilt {k z : X→ℝ} (ek : Envelope k) (hk : ∀ U, 0≤k U)
    (hZ : 0<∫ U,k U ∂μ) (meas : Measurable z) (a : ℝ) (ha : 0≤a)
    (lo : ∀ U, Real.exp (-a) ≤ z U) (hi : ∀ U, z U ≤ Real.exp a)
    (f : X→ℂ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (cap : ∀ U, ‖f U‖ ≤ M) :
    ‖read μ (k*z) f - read μ k f‖ ≤ 2 * Real.exp (2*a) * a * M := by
  let Z := ∫ U,k U ∂μ
  let Z' := ∫ U,k U*z U ∂μ
  let c := Z'/Z
  let span := Real.exp a-Real.exp (-a)
  have ez : Envelope z := ⟨meas,Real.exp a,fun U =>
    (Real.norm_of_nonneg ((Real.exp_pos _).le.trans (lo U))).trans_le (hi U)⟩
  have low : Z*Real.exp (-a) ≤ Z' := by
    dsimp only [Z,Z']
    rw [← integral_mul_const]
    exact integral_mono ((ek.integrable μ).mul_const _) ((ek.mul ez).integrable μ)
      (fun U => mul_le_mul_of_nonneg_left (lo U) (hk U))
  have high : Z' ≤ Z*Real.exp a := by
    dsimp only [Z,Z']
    rw [← integral_mul_const]
    exact integral_mono ((ek.mul ez).integrable μ) ((ek.integrable μ).mul_const _)
      (fun U => mul_le_mul_of_nonneg_left (hi U) (hk U))
  have hp : 0<Z' := (mul_pos hZ (Real.exp_pos _)).trans_le low
  have clo : Real.exp (-a) ≤ c := (le_div_iff₀ hZ).mpr ((mul_comm ..).trans_le low)
  have chi : c ≤ Real.exp a := (div_le_iff₀ hZ).mpr (high.trans_eq (mul_comm ..))
  have margin (U : X) : |z U-c| ≤ span := by
    apply abs_le.mpr
    constructor <;> dsimp [span] <;> linarith [lo U,hi U]
  have span_nonneg : 0 ≤ span := sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_self ha))
  let delta := fun U => (k U:ℂ)*(((z U-c:ℝ):ℂ)*f U)
  have centered : (∫ U,((k*z) U:ℂ)*f U ∂μ) - (c:ℂ)*(∫ U,(k U:ℂ)*f U ∂μ) =
      ∫ U,delta U ∂μ := by
    simp only [Pi.mul_apply]
    rw [← integral_const_mul,← integral_sub (integrable_test μ (ek.mul ez) f hf M cap)
      ((integrable_test μ ek f hf M cap).const_mul (c:ℂ))]
    apply integral_congr_ae
    refine ae_of_all _ fun U => ?_
    simp only [delta,Complex.ofReal_mul,Complex.ofReal_sub]
    ring
  have bound : ‖∫ U,delta U ∂μ‖ ≤ Z*(span*M) := by
    change _ ≤ (∫ U,k U ∂μ)*(span*M)
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le ((ek.integrable μ).mul_const _)
    refine ae_of_all _ fun U => ?_
    simp only [delta,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hk U)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (margin U) (cap U) (norm_nonneg _) span_nonneg) (hk U)
  change ‖(Z':ℂ)⁻¹*(∫ U,((k*z) U:ℂ)*f U ∂μ) - (Z:ℂ)⁻¹*(∫ U,(k U:ℂ)*f U ∂μ)‖ ≤ _
  rw [centered_scalar hp hZ]
  change ‖(Z':ℂ)⁻¹*((∫ U,((k*z) U:ℂ)*f U ∂μ) - (c:ℂ)*(∫ U,(k U:ℂ)*f U ∂μ))‖ ≤ _
  rw [centered,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hp.le]
  calc Z'⁻¹ * ‖∫ U,delta U ∂μ‖ ≤ Z'⁻¹*(Z*(span*M)) := mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr hp.le)
       _ = (Z'⁻¹*Z)*(span*M) := by ring
       _ ≤ Real.exp a*((2*a*Real.exp a)*M) :=
         mul_le_mul (inverse_price low hp)
           (mul_le_mul_of_nonneg_right (exponential_span a) hM) (mul_nonneg span_nonneg hM) (Real.exp_pos _).le
       _ = _ := by rw [show 2*a=a+a by ring,Real.exp_add]; ring

variable {G : Gauge} (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "Ω" => Config G (R.alloy.B.a.S.side m p)
local notation "η" => prior G (R.alloy.B.a.S.side m p)
local notation "I" => remainder R (p:=p) hm d
local notation "B" => R.alloy.B.a.budget m
local notation "ε" => (Real.sqrt 2 * Pert.Asymptotics.regulatorRun R.family N p (m+1))^(d+1)
variable (A : Comparison R (p:=p) hm d)
include A

omit A in
private theorem uniform_row {b : ℕ→ℝ} (cost : ∀ i, (B).supBounds ((I).reg i).site ((I).reg i).support ((I).E i) (b i))
    (i : ℕ) (U : Ω) : |row R (p:=p) hm d i U| ≤ b i := by
  by_cases healthy : Healthy (B).threshold ((I).reg i).support U
  · simp only [OriginalMarkedRowCovariance.row,Activities.regularOccurrence,masked_eq _ _ _ _ healthy]
    exact (Real.norm_eq_abs _).symm.le.trans ((cost i).2 U healthy [] (Nat.zero_le _) (by simp))
  · simpa only [OriginalMarkedRowCovariance.row,Activities.regularOccurrence,masked_ne _ _ _ _ healthy,abs_zero] using (cost i).1

private theorem increment {b : ℕ→ℝ} (cost : ∀ i, (B).supBounds ((I).reg i).site ((I).reg i).support ((I).E i) (b i))
    (i : ℕ) (f : Ω→ℂ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (cap : ∀ U, ‖f U‖≤M) :
    ‖local_ratio R (p:=p) hm d i f‖ ≤ 2*Real.exp (2*b i)*b i*M := by
  let k := density R (p:=p) hm d i
  let z := fun U => Real.exp (-row R (p:=p) hm d i U)
  have append : density R (p:=p) hm d (i+1) = k*z := by
    funext U
    simp only [k,z,Pi.mul_apply,density,«prefix»,Finset.sum_range_succ,neg_add,Real.exp_add,mul_assoc]
  have meas : Measurable z := Real.continuous_exp.measurable.comp
    (masked_measurable _ _ _ (A.posterior.cut.regular.smooth i).borel).neg
  have bound := uniform_row R hm cost i
  rw [← successive R hm A i f,partial_read R hm A (i+1) f,partial_read R hm A i f,append]
  apply normalized_tilt η (density_envelope R hm A i) (fun U => (density_positive R hm A i U).le)
    (normalizer_positive R hm A i) meas (b i) (cost i).1 _ _ f hf M hM cap
  · exact fun U => Real.exp_le_exp.mpr (neg_le_neg ((le_abs_self _).trans (bound U)))
  · exact fun U => Real.exp_le_exp.mpr ((neg_le_abs _).trans (bound U))

def traversal (point : BudgetPoint) {n : Side} (x y : Site n) : ℝ :=
  Real.exp (-point.supportExponent*((separation x y / leg point.B : ℕ):ℝ))

omit A in
private theorem shell_scale (block r t : ℕ) : r*(t/leg ((block+1)*r)) ≤ t/leg block := by
  apply (Nat.le_div_iff_mul_le (leg_pos block)).mpr
  calc r*(t/leg ((block+1)*r))*leg block = (t/leg ((block+1)*r))*(r*leg block) := by ring
       _ ≤ (t/leg ((block+1)*r))*leg ((block+1)*r) := Nat.mul_le_mul_left _ (by unfold leg; nlinarith)
       _ ≤ _ := Nat.div_mul_le_self .. 

omit A in
private theorem shells (point : BudgetPoint) {n : Side} (x : Site n) (r : ℕ) (hr : 1≤point.supportExponent*r) :
    ∑ y : Site n,traversal point y x ≤ hitConstant ((point.B+1)*r) := by
  refine le_trans (Finset.sum_le_sum fun y _ => ?_) (all_marks id Function.injective_id x ((point.B+1)*r))
  unfold traversal
  rw [separation_comm y x]
  apply Real.exp_le_exp.mpr
  let k := separation x y/leg ((point.B+1)*r)
  have paid : (r:ℝ)*(k:ℝ) ≤ ((separation x y/leg point.B:ℕ):ℝ) := by exact_mod_cast shell_scale point.B r (separation x y)
  have h₁ := mul_le_mul_of_nonneg_right hr (show 0≤(k:ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left paid point.exponent_pos.le
  dsimp only [id]
  change -point.supportExponent*((separation x y/leg point.B:ℕ):ℝ) ≤ -(k:ℝ)
  nlinarith only [h₁,h₂]

def shell_width {G : Gauge} (R : Run G) : ℕ := ⌈1/(R.alloy.B.a.budget 0).supportExponent⌉₊

omit A in
private theorem shell_width_pays (m : ℕ) : 1≤(R.alloy.B.a.budget m).supportExponent*shell_width R := by
  let a := (R.alloy.B.a.budget 0).supportExponent
  have ha : 0<a := (R.alloy.B.a.budget 0).exponent_pos
  have init : 1≤a*(shell_width R:ℝ) := by
    simpa only [shell_width,mul_comm] using (div_le_iff₀ ha).mp (Nat.le_ceil (1/a))
  exact init.trans (mul_le_mul_of_nonneg_right (R.alloy.B.a.fits.deepExp (Nat.zero_le m)) (by positivity))

/-- All signed row changes from a prescribed anchor whose support
reaches the chosen marked site. The bound is independent of the ambient
volume. It holds for the actual successive normalized physical laws. -/
theorem touched (x y : Site (R.alloy.B.a.S.side m p)) (f : Ω→ℂ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (cap : ∀ U, ‖f U‖≤M) :
    SumBudget (fun i => if ((I).reg i).site=y ∧ x∈((I).reg i).support then
      ‖local_ratio R (p:=p) hm d i f‖ else 0) (2*Real.exp (2*ε)*M*traversal B y x*ε) := by
  obtain ⟨b,cost,roots⟩ := A.posterior.cut.boundE
  let bill (z : Site (R.alloy.B.a.S.side m p)) i := if ((I).reg i).site=z then (B).mass ((I).reg i).support (b i) else 0
  have small (i : ℕ) : b i ≤ ε := by
    let u := ((I).reg i).site
    have one : bill u i ≤ ∑' j,bill u j := (roots u).2.1.le_tsum i (fun j _ => (roots u).1 j)
    have price : b i ≤ bill u i := by simpa only [u,bill,if_pos rfl] using (B).loMass ((I).reg i).support (b i) (cost i).1
    exact price.trans (one.trans (roots u).2.2)
  let c := 2*Real.exp (2*ε)*M*traversal B y x
  have nonneg : 0≤c := by dsimp [c,traversal]; positivity
  let q (i : ℕ) := if ((I).reg i).site=y ∧ x∈((I).reg i).support then ‖local_ratio R (p:=p) hm d i f‖ else 0
  have q0 (i : ℕ) : 0≤q i := by dsimp [q]; split <;> positivity
  have qle (i : ℕ) : q i ≤ c*bill y i := by
    by_cases hit : ((I).reg i).site=y ∧ x∈((I).reg i).support
    · have anc : y∈((I).reg i).support := hit.1 ▸ ((I).reg i).anchor
      have reach := distance_charge ((I).reg i).support (B).B y x anc hit.2
      have rr : ((separation y x/leg (B).B:ℕ):ℝ) ≤ coverNumber (B).B ((I).reg i).support := by exact_mod_cast reach
      have discount : b i ≤ traversal B y x * (B).mass ((I).reg i).support (b i) := by
        unfold traversal BudgetPoint.mass
        rw [← mul_assoc,← Real.exp_add]
        apply le_mul_of_one_le_left (cost i).1
        apply Real.one_le_exp
        nlinarith only [mul_nonneg (B).exponent_pos.le (sub_nonneg.mpr rr)]
      have exp_le : Real.exp (2*b i) ≤ Real.exp (2*ε) := Real.exp_le_exp.mpr (by linarith [small i])
      simp only [q,bill,if_pos hit,if_pos hit.1,c]
      calc ‖local_ratio R (p:=p) hm d i f‖ ≤ 2*Real.exp (2*b i)*b i*M := increment R hm A cost i f hf M hM cap
           _ ≤ 2*Real.exp (2*ε)*(traversal B y x*(B).mass ((I).reg i).support (b i))*M := by
             gcongr
             exact (cost i).1
           _ = _ := by ring
    · simp only [q,if_neg hit]
      exact mul_nonneg nonneg ((roots y).1 i)
  have summ : Summable (fun i => c*bill y i) := (roots y).2.1.mul_left c
  refine ⟨q0,summ.of_nonneg_of_le q0 qle,?_⟩
  calc ∑' i,q i ≤ ∑' i,c*bill y i := (summ.of_nonneg_of_le q0 qle).tsum_le_tsum qle summ
       _ = c*∑' i,bill y i := tsum_mul_left
       _ ≤ _ := mul_le_mul_of_nonneg_left (roots y).2.2 nonneg

/-- Every actual support meeting the specified site is included. The
shell factor uses only the selected stage and the initial support
exponent of the preselected Run. -/
theorem touching (x : Site (R.alloy.B.a.S.side m p)) (f : Ω→ℂ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (cap : ∀ U, ‖f U‖≤M) :
    SumBudget (fun i => if x∈((I).reg i).support then ‖local_ratio R (p:=p) hm d i f‖ else 0)
      (2*Real.exp (2*ε)*M*ε*hitConstant (((B).B+1)*shell_width R)) := by
  let q (i : ℕ) := if x∈((I).reg i).support then ‖local_ratio R (p:=p) hm d i f‖ else 0
  let qy (y : Site (R.alloy.B.a.S.side m p)) (i : ℕ) := if ((I).reg i).site=y ∧ x∈((I).reg i).support then
    ‖local_ratio R (p:=p) hm d i f‖ else 0
  have q0 (i : ℕ) : 0≤q i := by dsimp [q]; split <;> positivity
  have price (y : Site (R.alloy.B.a.S.side m p)) := touched R hm A x y f hf M hM cap
  have total (i : ℕ) : (∑ y,qy y i) = q i := by
    by_cases hit : x∈((I).reg i).support <;> simp [qy,q,hit]
  obtain ⟨_,_,roots⟩ := A.posterior.cut.boundE
  have hε : 0≤ε := (tsum_nonneg (roots x).1).trans (roots x).2.2
  have hs (s : Finset ℕ) :
      ∑ i∈s,q i ≤ 2*Real.exp (2*ε)*M*ε*hitConstant (((B).B+1)*shell_width R) := by
    calc ∑ i∈s,q i = ∑ y,∑ i∈s,qy y i := by rw [Finset.sum_comm]; simp_rw [total]
         _ ≤ ∑ y,2*Real.exp (2*ε)*M*traversal B y x*ε := Finset.sum_le_sum fun y _ =>
           ((price y).2.1.sum_le_tsum s fun i _ => (price y).1 i).trans (price y).2.2
         _ = (2*Real.exp (2*ε)*M*ε)* ∑ y,traversal B y x := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (shells B x (shell_width R) (shell_width_pays R m)) (by positivity)
  have good := summable_of_sum_le q0 hs
  exact ⟨q0,good,good.tsum_le_of_sum_le hs⟩

/-- The only site count is that of the actual marked carrier. -/
theorem carrier (S : Finset (Site (R.alloy.B.a.S.side m p))) (f : Ω→ℂ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (cap : ∀ U, ‖f U‖≤M) :
    SumBudget (fun i => if ¬Disjoint ((I).reg i).support S then ‖local_ratio R (p:=p) hm d i f‖ else 0)
      (S.card*(2*Real.exp (2*ε)*M*ε*hitConstant (((B).B+1)*shell_width R))) := by
  let q (i : ℕ) := if ¬Disjoint ((I).reg i).support S then ‖local_ratio R (p:=p) hm d i f‖ else 0
  let w (x : Site (R.alloy.B.a.S.side m p)) (i : ℕ) := if x∈((I).reg i).support then ‖local_ratio R (p:=p) hm d i f‖ else 0
  have q0 (i : ℕ) : 0≤q i := by dsimp [q]; split <;> positivity
  have price (x : Site (R.alloy.B.a.S.side m p)) := touching R hm A x f hf M hM cap
  have charge (i : ℕ) : q i ≤ ∑ x∈S,w x i := by
    by_cases h : Disjoint ((I).reg i).support S
    · simp [q,h]; exact Finset.sum_nonneg fun x _ => (price x).1 i
    · obtain ⟨x,hx,hs⟩ := Finset.not_disjoint_iff.mp h
      have z := Finset.single_le_sum (f:=fun x=>w x i) (fun x _ => (price x).1 i) hs
      simpa only [q,w,if_pos h,if_pos hx] using z
  have fees (s : Finset ℕ) :
      (∑ i∈s,q i) ≤ S.card*(2*Real.exp (2*ε)*M*ε*hitConstant (((B).B+1)*shell_width R)) := by
    calc ∑ i∈s,q i ≤ ∑ i∈s,∑ x∈S,w x i := Finset.sum_le_sum fun i _ => charge i
         _ = ∑ x∈S,∑ i∈s,w x i := Finset.sum_comm
         _ ≤ ∑ _x∈S,2*Real.exp (2*ε)*M*ε*hitConstant (((B).B+1)*shell_width R) :=
           Finset.sum_le_sum fun x _ => ((price x).2.1.sum_le_tsum s fun i _ => (price x).1 i).trans (price x).2.2
         _ = _ := by simp
  have good := summable_of_sum_le q0 fees
  exact ⟨q0,good,good.tsum_le_of_sum_le fees⟩

end YM.Integration.OriginalMarkedRowPrice
