import YM.Integration.WilsonHeldRetainedWindows

/-! Arbitrary-order local action truncation in the original one-step Wilson
conditional. The signed price at a held field uses its own first absolute
moment. Integrating the same price uses the incoming upper Wilson scene. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldRetainedActionRate
open Filter MeasureTheory Lattice Wilson RG OPE.Therm
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open WilsonHeldRefillMoment Pert.Asymptotics
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "k" => (j+1)
local notation "fine" => Config G (R.family.side k per)
local notation "coarse" => Config G (R.family.side j per)
local notation "up" => R.family.path.rep N per k
local notation "cond" => actualAverage R.family (N:=N) (p:=per) (m:=j)

private theorem geometry (simple : G.Simple) (interior : k < N) :
    R.family.path.levels.clock.hatBeta k * regulatorRun R.family N per (k+1)^2 ≤ 2 ∧
    regulatorRun R.family N per (k+1) ≤ 2*regulatorRun R.family N per k := by
  let x := R.family.path.levels.clock.hatBeta k
  let b := R.family.path.β N per (k+1)
  let g := regulatorRun R.family N per (k+1)
  have rising : x ≤ R.family.path.levels.clock.hatBeta (k+1) := by
    change _ + G.slopeConstant * R.family.S.scale k ≤ _ + G.slopeConstant * R.family.S.scale (k+1)
    linarith only [mul_le_mul_of_nonneg_left ((OPE.scale_mono R.family.S).monotone (Nat.le_succ k))
      (Gauge.slopeConstant_pos simple).le]
  have band : R.family.path.levels.clock.hatBeta (k+1)/2 ≤ b :=
    (R.makes.wilson.represents N per (k+1) interior).band.1
  have xb : x ≤ 2*b := by linarith only [rising,band]
  have bp : 0 < b := Overlay.beta_positive R.makes.wilson interior
  have cash : g^2*b=1 := by
    change (Real.sqrt b)⁻¹^2*b=1
    rw [inv_pow,Real.sq_sqrt bp.le,inv_mul_cancel₀ bp.ne']
  refine ⟨(mul_le_mul_of_nonneg_right xb (sq_nonneg g)).trans_eq (by linarith only [cash]),?_⟩
  have priorBand : R.family.path.β N per k ≤ 2*x := (R.makes.wilson.represents N per k interior.le).band.2
  have bound : R.family.path.β N per k ≤ 4*b := by linarith only [priorBand,xb]
  have sqrtBound := Real.sqrt_le_sqrt bound
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),show Real.sqrt 4=2 by norm_num] at sqrtBound
  have kp : 0 < Real.sqrt (R.family.path.β N per k) :=
    Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson interior.le)
  change (Real.sqrt b)⁻¹ ≤ 2*(Real.sqrt (R.family.path.β N per k))⁻¹
  rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.mpr bp) kp]
  simpa only [one_mul] using sqrtBound

private theorem support_price (simple : G.Simple) (interior : k < N) (d q grade : ℕ)
    (order : 2*d+q+1 ≤ grade) (S : Support (R.family.side k per))
    (sites : (S.card:ℝ) ≤ R.family.path.levels.clock.hatBeta k^d)
    (small : regulatorRun R.family N per (k+1) ≤ 1) :
    (S.card:ℝ)*regulatorRun R.family N per (k+1)^grade ≤
      ((2:ℝ)^d*2^q)*regulatorRun R.family N per k^q := by
  let x := R.family.path.levels.clock.hatBeta k
  let t := regulatorRun R.family N per (k+1)
  let g := regulatorRun R.family N per k
  have xp : 0 ≤ x := zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have tp : 0 ≤ t := inv_nonneg.mpr (Real.sqrt_nonneg _)
  obtain ⟨two,step⟩ := geometry R simple interior (per:=per)
  have loss : t^grade ≤ t^(2*d+q) := pow_le_pow_of_le_one tp small (by omega)
  calc
    _ ≤ x^d*t^(2*d+q) := mul_le_mul sites loss (pow_nonneg tp _) (pow_nonneg xp _)
    _ = (x*t^2)^d*t^q := by rw [pow_add,pow_mul,mul_pow]; ring
    _ ≤ (2:ℝ)^d*(2*g)^q := mul_le_mul (pow_le_pow_left₀ (mul_nonneg xp (sq_nonneg _)) two d)
      (pow_le_pow_left₀ tp step q) (pow_nonneg tp _) (by positivity)
    _ = _ := by rw [mul_pow,mul_assoc]

private theorem exp_bound {a : ℝ} (nonneg : 0 ≤ a) (tiny : a ≤ 1) : Real.exp a-1 ≤ 2*Real.exp 2*a := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-a)) (Real.exp_pos a).le
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at h
  have e : Real.exp a ≤ 2*Real.exp 2 :=
    (Real.exp_le_exp.mpr (by linarith : a ≤ 2)).trans (by linarith [Real.exp_pos 2])
  exact (show Real.exp a-1 ≤ Real.exp a*a by linarith).trans (mul_le_mul_of_nonneg_right e nonneg)

/-- An arbitrary positive prefactor is bought before the period, cutoff and
window. The remaining power is at the actual upper field level `j+1`. -/
theorem fee (simple : G.Simple) (d q grade : ℕ) (order : 2*d+q+1 ≤ grade) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (N per : ℕ), j+1<N → ∀ S : Support (R.family.side (j+1) per),
      (S.card:ℝ) ≤ R.family.path.levels.clock.hatBeta (j+1)^d →
      let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a (j+1) S
        ((Real.sqrt 2*regulatorRun R.family N per (j+1+1))^(grade+1))
      2*Real.exp 2*a ≤ ε*regulatorRun R.family N per (j+1)^q ∧
      Real.exp a-1 ≤ ε*regulatorRun R.family N per (j+1)^q := by
  let C : ℝ := 2^d*2^q
  let η := min ε 1
  have cp : 0 < C := by dsimp [C]; positivity
  have ep : 0 < η := lt_min he zero_lt_one
  have pay := (tendsto_add_atTop_nat 1).eventually
    (OriginalMarkedGibbsRate.charged R simple (grade-1) (η/C) (div_pos ep cp))
  obtain ⟨lo,hlo⟩ := eventually_atTop.mp (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)
  filter_upwards [pay,eventually_ge_atTop lo] with j bill late N per interior S sites a
  let t := regulatorRun R.family N per (j+1+1)
  let g := regulatorRun R.family N per (j+1)
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have tsmall : t ≤ 1 := (hlo _ (late.trans (by omega)) N per interior).le
  have gsmall : g ≤ 1 := (hlo _ (late.trans (by omega)) N per interior.le).le
  have geo := support_price R simple interior d q grade order S sites tsmall
  have paid : 2*Real.exp 2*a ≤ (η/C)*(S.card:ℝ)*t^grade := by
    simpa only [show grade-1+2=grade+1 by omega,show grade-1+1=grade by omega] using bill N per interior S
  have cash : 2*Real.exp 2*a ≤ η*g^q := calc
    _ ≤ (η/C)*(S.card:ℝ)*t^grade := paid
    _ = (η/C)*((S.card:ℝ)*t^grade) := mul_assoc ..
    _ ≤ (η/C)*(C*g^q) := mul_le_mul_of_nonneg_left geo (div_nonneg ep.le cp.le)
    _ = _ := by rw [←mul_assoc,div_mul_cancel₀ η cp.ne']
  have nonneg : 0 ≤ a := OriginalMarkedLocalPurchase.fee_nonneg _ _ _
    (pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))) _)
  have tiny : a ≤ 1 := calc
    _ ≤ 2*Real.exp 2*a := le_mul_of_one_le_left nonneg (by linarith [Real.add_one_le_exp (2:ℝ)])
    _ ≤ η*g^q := cash
    _ ≤ 1*1 := mul_le_mul (min_le_right ε 1) (pow_le_one₀ gp gsmall) (pow_nonneg gp _) zero_le_one
    _ = 1 := one_mul _
  have actual := cash.trans (mul_le_mul_of_nonneg_right (min_le_left ε 1) (pow_nonneg gp _))
  exact ⟨actual,(exp_bound nonneg tiny).trans actual⟩


/-- The signed comparison of the actual and retained actions is pointwise
in the lower field and keeps exactly the same saved exterior on both sides. -/
theorem held {grade : ℕ} (interior : k < N) (bought : Comparison R (p:=per) interior grade)
    (S : Support (R.family.side k per)) (saved : Set (Edge (Site (R.family.side k per))))
    (fixed : ∀ e : Edge (Site (R.family.side k per)), e.1 ∉ S → e ∈ saved)
    (f : fine → ℂ) (hf : Envelope f) (V : coarse) :
    let P := approximation R (p:=per) interior grade
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a k S
      ((Real.sqrt 2*regulatorRun R.family N per (k+1))^(grade+1))
    ‖cond f V - redraw R N per j saved P f V‖ ≤ (Real.exp a-1)*cond (fun U => ‖f U‖) V := by
  intro P a
  obtain ⟨c,hc,low⟩ := OriginalMarkedGibbsAction.retained_floor R interior bought
  let J (U : fine) := (remainder R (p:=per) interior grade).additive (R.alloy.B.a.budget k) U
  have signed (U : fine) : -Real.log ((up).eval U)+Real.log (P.eval U)=J U := bought.signed U
  have osc (U Y : fine) (same : ∀ e ∈ saved, U e = Y e) : |J U-J Y| ≤ a := by
    have charge := OriginalMarkedLocalPurchase.run R interior bought S U Y (fun e h => same e (fixed e h))
    change |(-Real.log ((up).eval U)+Real.log (P.eval U))-(-Real.log ((up).eval Y)+Real.log (P.eval Y))| ≤ a at charge
    rwa [signed U,signed Y] at charge
  exact held_comparison R interior.le saved P (OriginalMarkedRunCovariance.keep_envelope R interior bought)
    hc low J (OriginalMarkedRunCovariance.factor R interior bought) osc f hf V

private theorem scene_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (live : k ≤ N) {F : fine → E} (hF : Integrable (fun U => (up).eval U • F U) (prior G _)) :
    Integrable (cond F) (scene R.family.path N per j) ∧
    (∫ V, cond F V ∂scene R.family.path N per j) = ∫ U, F U ∂scene R.family.path N per k := by
  have same : actualTransport R.family (N:=N) F (Nat.le_succ j) = cond F := by
    rw [actualTransport_step R.family R.makes live _ (Nat.lt_succ_self j),actualTransport_base R.family R.makes live]
  rw [←same]
  exact ⟨actualScene_integrable_of_weighted R.family R.makes ((Nat.le_succ j).trans live)
    (actualTransport_weighted_integrable_of_integrable R.family R.makes live hF (Nat.le_succ j)),
    actualScene_transport R.family R.makes live hF (Nat.le_succ j)⟩

/-- The grade and accuracy are fixed before the period and the cutoff. Both
the signed discrepancy at every held field and its lower-scene L¹ norm are
paid by the true first absolute moment on the same incoming upper law. -/
theorem purchased (simple : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees : Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d q grade : ℕ) (order : 2*d+q+1 ≤ grade) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (N per : ℕ) (interior : j+1<N)
      (S : Support (R.family.side (j+1) per)) (saved : Set (Edge (Site (R.family.side (j+1) per)))),
      (∀ e : Edge (Site (R.family.side (j+1) per)), e.1 ∉ S → e ∈ saved) →
      (S.card:ℝ) ≤ R.family.path.levels.clock.hatBeta (j+1)^d →
      ∀ (f : Config G (R.family.side (j+1) per) → ℂ), Envelope f →
        let P := approximation R (p:=per) interior grade
        let price := ε*regulatorRun R.family N per (j+1)^q
        let orig := actualAverage R.family (N:=N) (p:=per) (m:=j) f
        let err := fun V => orig V - redraw R N per j saved P f V
        (∀ V, ‖err V‖ ≤ price*actualAverage R.family (N:=N) (p:=per) (m:=j) (fun U => ‖f U‖) V) ∧
        Integrable err (scene R.family.path N per j) ∧
        (∫ V, ‖err V‖ ∂scene R.family.path N per j) ≤ price*∫ U, ‖f U‖ ∂scene R.family.path N per (j+1) := by
  have stock := (tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [stock,fee R simple d q grade order he] with j parts tariff N per interior S saved fixed sites f hf P price orig err
  let E := actualAverage R.family (N:=N) (p:=per) (m:=j) (fun U => ‖f U‖)
  have bought := parts N per interior
  have point (V) : ‖err V‖ ≤ price*E V := by
    have pos : 0 ≤ E V := integral_nonneg fun U =>
      mul_nonneg (actualConditionalDensity_nonneg R.family R.makes interior.le V U) (norm_nonneg _)
    exact (held R interior bought S saved fixed f hf V).trans
      (mul_le_mul_of_nonneg_right (tariff N per interior S sites).2 pos)
  have pe := (R.family.path.rep N per (j+1)).envelope (R.makes.wilson.represents N per (j+1) interior.le).good
  letI : IsFiniteMeasure (prior G (R.family.side (j+1) per)) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Edge (Site (R.family.side (j+1) per)) => G.probHaar))
  have fi : Integrable (fun U => (R.family.path.rep N per (j+1)).eval U • f U) (prior G _) := by
    simpa only [Complex.real_smul] using OriginalMarkedExteriorHaar.weighted_integrable pe hf (prior G _)
  have origI := (scene_step R interior.le fi).1
  have redrawI := (WilsonHeldRetainedWindows.physical R interior bought S saved fixed f hf).1
  have integrable : Integrable err (scene R.family.path N per j) := origI.sub redrawI
  have ef : Envelope (fun U => ‖f U‖) := by
    obtain ⟨c,hc⟩ := hf.cost
    exact ⟨hf.meas.norm,c,fun U => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hc U⟩
  obtain ⟨normI,same⟩ := scene_step R interior.le ((pe.mul ef).integrable (prior G _))
  refine ⟨point,integrable,(integral_mono integrable.norm (normI.const_mul price) point).trans_eq ?_⟩
  rw [integral_const_mul,same]

end YM.Integration.WilsonHeldRetainedActionRate
