import YM.Integration.WilsonUniformUnmarkedHessianRow
import YM.Integration.WilsonPhysicalHistoryAperture

/-! The full reset kinetic moment is zero on each finite torus. At the
common observation radius its exterior has arbitrarily small absolute
mass, and therefore its signed interior has the same price, on every
finer cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedMomentTail
open Filter Real Function Finset PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open RG16 RG16.Literal Pert.Asymptotics WilsonConditionalTaylorBulkHistory
open WilsonUniformUnmarkedHessianRow
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side}

def term (h : Site n → ℝ) (x : Site n) := h x*(Cork.ch 0 (lift x))^2

theorem outside (h : Site n → ℝ) (s b : ℕ) (large : 2 ≤ s) {σ : ℝ} (width : 0 ≤ σ) :
    (∑ x ∈ univ.filter (fun x : Site n=> b ≤ pdist x), |term h x|) ≤
      exp (-σ*(b:ℝ))*(∑ x : Site n, Whisk.liftW σ s (pdist x)*|h x|) := by
  let W (x : Site n):=Whisk.liftW σ s (pdist x)*|h x|
  let A:=univ.filter (fun x : Site n=> b ≤ pdist x)
  have compare (x : Site n) (out : b ≤ pdist x) :
      |term h x| ≤ exp (-σ*(b:ℝ))*W x := by
    let d:ℝ:=pdist x
    have d0 : 0 ≤ d := Nat.cast_nonneg _
    have coordinate : |Cork.ch 0 (lift x)| ≤ d := by
      unfold Cork.ch d
      rw [←Int.cast_abs,←Int.natCast_natAbs]
      exact_mod_cast component_le x (0:Axis)
    have hp : |Cork.ch 0 (lift x)|^2 ≤ (1+d)^s :=
      (pow_le_pow_left₀ (abs_nonneg _) (show |Cork.ch 0 (lift x)|≤1+d by linarith) 2).trans
        (pow_le_pow_right₀ (by linarith : 1≤1+d) large)
    have db : (b:ℝ) ≤ d := by unfold d;exact_mod_cast out
    have ex : 1 ≤ exp (-σ*(b:ℝ))*exp (σ*d) := by
      rw [←Real.exp_add]
      apply Real.one_le_exp
      nlinarith only [mul_nonneg width (sub_nonneg.mpr db)]
    calc
      |term h x| = |h x| * |Cork.ch 0 (lift x)|^2 := by simp [term,abs_mul]
      _ ≤ |h x| *(1+d)^s :=mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ ≤ (|h x| *(1+d)^s)*(exp (-σ*(b:ℝ))*exp (σ*d)) :=
        le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _)) ex
      _ = _ := by unfold W Whisk.liftW;change _ = exp (-σ*(b:ℝ))*((1+d)^s*exp (σ*d)*|h x|);ring
  calc
    _ ≤ ∑ x ∈ A,exp (-σ*(b:ℝ))*W x := Finset.sum_le_sum (fun x hx=>compare x (Finset.mem_filter.mp hx).2)
    _ ≤ ∑ x : Site n,exp (-σ*(b:ℝ))*W x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _=>
        mul_nonneg (exp_pos _).le (mul_nonneg (Whisk.wpos ..).le (abs_nonneg _)))
    _ = _ := (Finset.mul_sum ..).symm

theorem balanced (h : Site n → ℝ) (b : ℕ)
    (zero : (∑ x : Site n, term h x)=0) :
    |∑ x ∈ univ.filter (fun x : Site n=> pdist x < b), term h x| ≤
      ∑ x ∈ univ.filter (fun x : Site n=> b ≤ pdist x), |term h x| := by
  have split:=Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun x : Site n=>pdist x<b)
    (f:=term h)
  simp only [not_lt,zero] at split
  rw [eq_neg_of_add_eq_zero_left split,abs_neg]
  exact Finset.abs_sum_le_sum_abs ..

def aperture (C : Family G) (p j : ℕ) : ℕ :=
  ⌈WilsonPhysicalHistoryAperture.width C j*(WilsonPhysicalHistoryAperture.radius C p j:ℝ) /
    (Alto.candles C.path.levels j)⌉₊

theorem localWidth (C : Family G) (j : ℕ) : 0 < Alto.candles C.path.levels j := by
  have b:=Real.log_pos (C.path.levels.fits.delayed j)
  unfold Alto.candles Alto.cWidth Alto.flurry
  positivity

theorem window (R : Run G) (p N per j : ℕ) (live : j ≤ N) :
    exp (-(Alto.candles R.family.path.levels j)*(aperture R.family p j:ℝ)) ≤
      (regulatorRun R.family N per j)^(p+1) := by
  let C:=R.family
  let w:=WilsonPhysicalHistoryAperture.width C j
  let A:=WilsonPhysicalHistoryAperture.radius C p j
  let σ:=Alto.candles C.path.levels j
  have cost: w*(A:ℝ) ≤ (aperture C p j:ℝ)*σ :=(div_le_iff₀ (localWidth C j)).mp (Nat.le_ceil _)
  apply le_trans _ (WilsonPhysicalHistoryAperture.exponential R p N per j live)
  apply Real.exp_le_exp.mpr
  change -σ*(aperture C p j:ℝ) ≤ -w*(A:ℝ)
  linarith only [cost]

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include bought simple in
theorem signed (E p : ℕ) {ε : ℝ} (small : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N → ∀ e, 0<e → e ≤ E →
      let n:=R.family.side j per
      let t:=term (hessian n u (course R u wood tags N j n) e)
      let b:=aperture R.family (p+1) j
      let g:=regulatorRun R.family N per j
      (∑ x ∈ univ.filter (fun x : Site n=> b ≤ pdist x), |t x|) ≤ ε*g^p ∧
        |∑ x ∈ univ.filter (fun x : Site n=> pdist x < b), t x| ≤ ε*g^p := by
  obtain ⟨K,quiet⟩:=eventually_atTop.mp (IterationFour.Currency.g_small simple R.makes ε small)
  filter_upwards [WilsonUniformUnmarkedHessianRow.earned R simple u V bought wood tags 6 E le_rfl zero_lt_one,
    eventually_ge_atTop K] with k ledger after N per kN j lo hi e positive cap
  intro n t b g
  let A:=course R u wood tags N j n
  let H:=hessian n u A e
  let σ:=Alto.candles R.family.path.levels j
  have clear : (∑ x : Site n,term H x)=0 := by
    have z:=WilsonUniformUnmarkedAffineMoment.rooted R simple u V bought wood tags N per j e hi positive
    change (∑ x : Site n,rancho A e 2 ![(x,coord (1:Axis),u),(0,coord (1:Axis),u)]*
      (Cork.ch 0 (lift x)*Cork.ch 0 (lift x)))=0 at z
    calc
      _ = 2*(∑ x : Site n,rancho A e 2 ![(x,coord (1:Axis),u),(0,coord (1:Axis),u)]*
          (Cork.ch 0 (lift x)*Cork.ch 0 (lift x))) := by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro x _
        unfold term H WilsonUniformUnmarkedHessianRow.hessian;ring
      _ = 0 :=by rw [z,mul_zero]
  have g0 : 0 < g :=RG16.Literal.g_pos R.makes hi
  have bill:=ledger N per kN j lo hi e positive cap
  have bound : (∑ x : Site n,Whisk.liftW σ 6 (pdist x)*|H x|) ≤ g⁻¹ := by
    simpa only [Real.rpow_neg_one] using bill
  have paid : exp (-σ*(b:ℝ))*(∑ x : Site n,Whisk.liftW σ 6 (pdist x)*|H x|) ≤ ε*g^p := by
    calc
      _ ≤ g^((p+1)+1)*g⁻¹ :=
        mul_le_mul (window R (p+1) N per j hi) bound
          (Finset.sum_nonneg (fun x _=>mul_nonneg (Whisk.wpos ..).le (abs_nonneg _))) (pow_nonneg g0.le _)
      _ = g^p*g := by rw [pow_succ g (p+1),mul_assoc,mul_inv_cancel₀ g0.ne',mul_one,pow_succ]
      _ ≤ ε*g^p :=by rw [mul_comm];exact mul_le_mul_of_nonneg_right (quiet j (after.trans lo) N per hi).le (pow_nonneg g0.le _)
  have outer :=(outside H 6 b (by norm_num) (localWidth R.family j).le).trans paid
  exact ⟨outer,(balanced H b clear).trans outer⟩

end YM.Integration.WilsonUniformUnmarkedMomentTail
