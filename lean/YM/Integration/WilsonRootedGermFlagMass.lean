import YM.Integration.WilsonRootedGermFlagTariff

/-! The same phased bare numerator, tested against the full positive old one-hole rent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermFlagMass
open Function Finset Filter MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato
open SectorNext.Vacuum WilsonMatrixOriginalGermForeground WilsonMatrixOriginalGermOccupancy
open WilsonRootedGermFlagTariff
open private weights from YM.Integration.WilsonMatrixOriginalGermOccupancy
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) {i N p : ℕ}

def slice (i p q : ℕ) (D : Config G (R.family.side i p) → ℂ) (U : Config G (R.family.side i p)) : ℂ :=
  if q≤(flags ((R.family.path.levels.budget i).threshold/2) U).card then D U else 0

theorem slice_env (q : ℕ) {D : Config G (R.family.side i p) → ℂ} (hd : Envelope D) :
    Envelope (slice R i p q D) := by
  let t := (R.family.path.levels.budget i).threshold/2
  have mf : Measurable (flags (G:=G) (n:=R.family.side i p) t) := by
    apply measurable_to_countable _
    intro z
    exact flags_measurable_eq ..
  have countable : Measurable (fun z : Support (R.family.side i p)=>z.card) := measurable_of_countable _
  have setm : MeasurableSet {U : Config G (R.family.side i p) | q≤(flags t U).card} :=
    measurableSet_le measurable_const (countable.comp mf)
  obtain ⟨M,cap⟩ := hd.cost
  refine ⟨hd.meas.ite setm measurable_const,M,fun U=>?_⟩
  unfold slice
  split
  · exact cap U
  · rw [norm_zero];exact (norm_nonneg _).trans (cap U)

theorem original (visible : i≤N) (q : ℕ) (o : Site (R.family.side i p))
    (D : Config G (R.family.side i p) → ℂ) (hd : Envelope D) {M : ℝ} (cap : ∀ U, ‖D U‖≤M) :
    (∫ U, rent R i N p o U * ‖slice R i p q D U‖ ∂OPE.Therm.scene R.family.path N p i) ≤
      M*Real.exp ((Fintype.card (Site (R.family.side i p)):ℝ)*siteRate R i N p - (q:ℝ)*heat R i N p) := by
  let L := R.family.path.levels
  let n := R.family.side i p
  let W := R.family.path.rep N p i
  let t := (L.budget i).threshold/2
  let s := L.clock.hatCoupling i
  let μ := prior G n
  let Ξ := partition G (R.family.side N p) (R.family.path.β N p N)
  let f := fun U : Config G n => weight R i N p o U*‖slice R i p q D U‖
  have law := R.makes.wilson.represents N p i visible
  have hs : 0<s := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (L.fits.delayed i)))
  have clock : s≤W.p.threshold := by
    rw [show W.p=L.budget i from law.vac]
    change s ≤ s*L.clock.monitor i
    exact le_mul_of_one_le_right hs.le (Real.one_le_exp (sq_nonneg _))
  have ht : 0<t := div_pos (L.budget i).threshold_pos (by norm_num)
  have half : 2*t≤W.p.threshold := by
    rw [show W.p=L.budget i from law.vac];dsimp only [t];linarith
  have hweight : Envelope (weight R i N p o) := weights R
  have wf : Measurable f := hweight.meas.mul (slice_env R q hd).meas.norm
  have nonnegative (U : Config G n) : 0≤weight R i N p o U := by dsimp only [WilsonMatrixOriginalGermForeground.weight];split <;> positivity
  have little (U : Config G n) : weight R i N p o U≤1 := by
    dsimp only [WilsonMatrixOriginalGermForeground.weight]
    split
    · exact zero_le_one
    · exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (flagRate_pos _).le) (Nat.cast_nonneg _))
  have bill (U : Config G n) : ‖f U‖≤M := by
    change ‖weight R i N p o U*‖slice R i p q D U‖‖≤M
    rw [Real.norm_of_nonneg (mul_nonneg (nonnegative U) (norm_nonneg _))]
    apply (mul_le_of_le_one_left (norm_nonneg _) (little U)).trans
    unfold slice
    split
    · exact cap U
    · rw [norm_zero];exact (norm_nonneg _).trans (cap U)
  have flagsPaid (U : Config G n) (h : f U≠0) : q≤(flags t U).card := by
    by_contra hn
    apply h
    dsimp only [f,slice]
    rw [if_neg hn,norm_zero,mul_zero]
  let WF := ActualRunRequestedNorm.wellFormed R N p i visible W.p rfl rfl le_rfl le_rfl le_rfl
  have price := SelectedCofactorVacuumMass.signed_price WF law.good.paths (Overlay.beta_positive R.makes.wilson visible).le s t hs clock ht half
    (R.family.path.nonnegative R.makes.wilson _ _ _ visible) ((W.envelope law.good).integrable _) f wf M bill q flagsPaid
  have normal : (∫ U, W.eval U ∂μ)=Ξ := R.family.path.partition_eq R.makes.wilson _ _ _ visible
  have bound := price.2
  change ‖(∫ U,W.eval U ∂μ)⁻¹ • (∫ U, Real.exp (W.exponent U) • f U ∂μ)‖≤_ at bound
  rw [normal] at bound
  have edge : Fintype.card (Edge (Site n))=Fintype.card (Site n)*4 := by simp [Edge]
  calc
    _ = WilsonMatrixOriginalGermHeldTest.fare R i N p o (slice R i p q D) :=
      WilsonMatrixOriginalGermHeldTest.factor R visible o _
    _ = Ξ⁻¹ * ∫ U, Real.exp (W.exponent U) • f U ∂μ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with U
      dsimp only [WilsonMatrixOriginalGermHeldTest.fare,f,smul_eq_mul]
      ring
    _ ≤ _ := (le_abs_self _).trans (bound.trans_eq (by
      congr 2
      let A := (L.params i).paths
      let c := 2*W.exCost A (L.clock.loopCap i) (L.clock.allowance i) + W.beta*RG.baseBudget W.clip A s
      change (Fintype.card (Site n):ℝ)*c + (Fintype.card (Edge (Site n)):ℝ)*Module.finrank ℝ G.Mat*Real.log (16/s) - W.beta*(W.clip.linear/5*t^2*q) =
        (Fintype.card (Site n):ℝ)*(c+4*Module.finrank ℝ G.Mat*Real.log (16/s)) - (q:ℝ)*(W.beta*(W.clip.linear/5*t^2))
      rw [edge];push_cast
      ring))

end YM.Integration.WilsonRootedGermFlagMass
