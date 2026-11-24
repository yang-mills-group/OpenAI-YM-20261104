import YM.Integration.WilsonReportColumnCut

/-! Finite physical support for every occupied subset of the original signed
Wilson report, with one common true coarse probability law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowRoster
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Cells
open Next.Rank OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol OPE.Strobe.Panoramic Push.GridApprox
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportColumnCut
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} {F:Spec.Final R.family f S}

private theorem product_gap {I : Type*} [DecidableEq I] (q : Finset I) (f g : I → ℂ)
    {e M : ℝ} (he : 0 ≤ e) (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ M)
    (h : ∀ i, ‖f i-g i‖ ≤ e) : ‖(∏ j ∈ q, f j) - (∏ j ∈ q, g j)‖ ≤ q.card*e*M^q.card := by
  induction q using Finset.induction_on with
  | empty => simp
  | @insert i q hi ih =>
    let X := ∏ j ∈ q, f j
    let Y := ∏ j ∈ q, g j
    have hy : ‖Y‖ ≤ M^q.card := by
      dsimp only [Y]
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hg j)).trans_eq (by simp)
    simp only [prod_insert hi,card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    change ‖f i*X-g i*Y‖ ≤ ((q.card:ℝ)+1)*e*(M^q.card*M)
    calc
      _ = ‖f i*(X-Y)+(f i-g i)*Y‖ := congrArg norm (by ring)
      _ ≤ ‖f i‖*‖X-Y‖+‖f i-g i‖*‖Y‖ := by simpa only [norm_mul] using norm_add_le (f i*(X-Y)) ((f i-g i)*Y)
      _ ≤ M*(q.card*e*M^q.card)+e*M^q.card := add_le_add
        (mul_le_mul (hf i) ih (norm_nonneg _) (zero_le_one.trans hM))
        (mul_le_mul (h i) hy (norm_nonneg _) he)
      _ ≤ _ := by nlinarith only [le_mul_of_one_le_right (mul_nonneg he (pow_nonneg (zero_le_one.trans hM) q.card)) hM]

/-- Simultaneous truncation of every reported moment on one genuine regulator;
each complement component retains its original sign, mass and column. -/
theorem retained (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (L : Layout F) (E : OPE.Services R.family f S) (r : ℝ) {n k N p t h : ℕ}
    (d : Fin n→ℕ) (w : (j:Fin n)→R.family.label (d j))
    (grade : ∀ j,R.family.ref (d j) ≤ L.level r) (zero : R.family.ref 0 < k) (deep : L.level r ≤ k)
    (cut : k < N) (zoom : R.family.S.a (L.level r)/R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k^t)
    (price : ∀ j,mass R.family (d j) (L.shift (d j) r (w j)) ≤ R.family.path.levels.clock.hatBeta (L.level r)^h)
    (x : Fin n→Site (R.family.side k p)) :
    let C := R.family; let β := C.path.levels.clock.hatBeta k
    let B := (C.path.levels.budget k).B; let μ := Therm.scene C.path N p k
    let a := 1+t*((∑j,d j)+1)+h
    let M (j : Fin n) := regularRead C (d j) k N p (atRef L (d j) r (N,p) (w j)) (x j)
    let Q (j : Fin n) := localized L r (d j) k N p (w j) (x j)
    (∀ j,Interior (window (x j) (omen C (d j) k B)) (Q j)) ∧
    (∀ j U,‖Q j U‖≤5*β^a) ∧
    ∀ I : Finset (Fin n),Integrable (fun U=>∏ j∈I,Q j U) μ ∧
      ‖(∫ U,∏ j∈I,M j U ∂μ) - ∫ U,∏ j∈I,Q j U ∂μ‖ ≤
        ((2:ℝ)*n*5^n)*(Real.exp (-2*(B:ℝ))*β^(a*(n+1))) := by
  let C := R.family
  let β := C.path.levels.clock.hatBeta k
  let B := (C.path.levels.budget k).B
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability R.makes.wilson cut.le
  let a := 1+t*((∑j,d j)+1)+h
  let M (j : Fin n) := regularRead C (d j) k N p (atRef L (d j) r (N,p) (w j)) (x j)
  let Q (j : Fin n) := localized L r (d j) k N p (w j) (x j)
  let amp := Real.exp (-2*(B:ℝ))
  have b1 : 1≤β := (C.path.levels.fits.delayed k).le
  have b0 := zero_le_one.trans b1
  have α0 : 0≤amp := Real.exp_nonneg _
  have m1 : 1≤5*β^a := by linarith only [one_le_pow₀ (n:=a) b1]
  have row (j : Fin n) := field hG W funding subsidy L E r (w j) (grade j) zero deep cut zoom (x j)
  have mono := WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos hG).le deep
  have size (j : Fin n) : β^(1+t*(d j+1))*mass C (d j) (L.shift (d j) r (w j)) ≤ β^a := by
    have jd := Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (mem_univ j)
    have bigger : 1+t*(d j+1)+h ≤ a := Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right jd _)) _) _
    calc
      _ ≤ β^(1+t*(d j+1))*β^h := mul_le_mul_of_nonneg_left ((price j).trans
        (pow_le_pow_left₀ (zero_le_one.trans (C.path.levels.fits.delayed _).le) mono _)) (pow_nonneg b0 _)
      _ ≤ β^a := (pow_add ..).symm.le.trans (pow_le_pow_right₀ b1 bigger)
  have full (j : Fin n) (U) : ‖M j U‖≤5*β^a := ((row j).2.2.2 U).1.trans
    ((mul_le_mul_of_nonneg_left (size j) (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg b0 _)))
  have finite (j : Fin n) (U) : ‖Q j U‖≤5*β^a :=
    ((row j).2.2.2 U).2.2.trans (mul_le_mul_of_nonneg_left (size j) (by norm_num))
  have paid (j : Fin n) (U) : ‖M j U-Q j U‖ ≤ 2*(amp*β^a) :=
    ((row j).2.2.2 U).2.1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (size j) α0) (by norm_num))
  dsimp only
  refine ⟨fun j=>(row j).1,finite,?_⟩
  intro I
  have suppliedM := (Envelope.prodC I M (fun j _=>(row j).2.1)).integrableC μ
  have suppliedQ := (Envelope.prodC I Q (fun j _=>(row j).2.2.1)).integrableC μ
  refine ⟨suppliedQ,?_⟩
  have hn : I.card ≤ n := (Finset.card_le_univ I).trans_eq (Fintype.card_fin _)
  have cash (U) : ‖(∏ j∈I,M j U)-(∏ j∈I,Q j U)‖ ≤ ((2:ℝ)*n*5^n)*(amp*β^(a*(n+1))) := by
    have sale := product_gap I (fun j=>M j U) (fun j=>Q j U) (by positivity : 0≤2*(amp*β^a))
      m1 (fun j=>full j U) (fun j=>finite j U) (fun j=>paid j U)
    apply sale.trans
    calc
      _ ≤ (n:ℝ)*(2*(amp*β^a))*(5*β^a)^n := mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)) (pow_le_pow_right₀ m1 hn)
        (by positivity) (by positivity)
      _ = _ := by rw [mul_pow,pow_mul,pow_succ]; ring
  have bound := norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall cash)
  rw [probReal_univ,mul_one] at bound
  rw [←integral_sub suppliedM suppliedQ]
  exact bound

end YM.Integration.WilsonReportWindowRoster
end

