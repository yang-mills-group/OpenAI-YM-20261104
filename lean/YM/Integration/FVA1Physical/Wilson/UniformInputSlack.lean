import YM.Integration.FVA1Physical.Wilson.InputPrefix

/-! In a tower the preceding coarse bank's power reserve must be chosen
before either stage or the lattice is chosen. For a full normalized row the
necessary reserve depends only on the fixed two jet orders and field degree. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open scoped Classical Topology BigOperators
variable {G:Gauge}

def inputSlack (p m h:ℕ) {η:ℝ} (pos:0<η) := (row_exponent m (p+1+p) h pos).choose

theorem inputSlack_pos (p m h:ℕ) {η:ℝ} (pos:0<η) : 0 < inputSlack p m h pos :=
  (row_exponent m (p+1+p) h pos).choose_spec.1

theorem fixed_input_rows (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p m h s:ℕ) (hm:1 ≤ m) {η:ℝ} (hη:0<η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Issue G) (b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ src:PowerSeries (Pot (Joint A.F G)),
        (∀ i ≤ p,Vault (address A.F G) {b} (αm y) s (h+2*Whisk.ribbon m (p+1+p)+1) 0
          (PowerSeries.coeff i src) (y^(inputSlack p m h hη)) ∧ (PowerSeries.coeff i src).totalDegree ≤ m) →
        ∀ i ≤ p,Vault (address A.F G) {b} (αm y) s h 0 (PowerSeries.coeff i (normalizedRows A χ src p)) (y^η) := by
  let d:=p+1+p
  let δ:=inputSlack p m h hη
  have hδ:=inputSlack_pos p m h hη
  obtain ⟨C,law⟩:=full_covariance_rows J clear χ hχ simple H H' P K branch s
  obtain ⟨t,buy⟩:=purchased_chart_chance J clear simple H H' P K branch (D:=0) le_rfl 0
  obtain ⟨_,_,theater⟩:=waiting t H H' J χ hχ clear P 3 0
  let gy:=Work.E09.betaF_growth G P.L
  filter_upwards [law,buy,theater,distributed_action J χ hχ simple H H' P K p s (h+2*Whisk.ribbon m d) hδ,
    gy.eventually ((row_exponent m d h hη).choose_spec.2 C),gy.eventually_gt_atTop 0] with x cover paid hall full reserve positive
  intro A b patch kernel season y kind plane wedge src credit i hi
  obtain ⟨grants,cal,_,_⟩:=paid A patch kernel season 0 b (by simp)
  have suite:=(hall.enter _ _ patch season (boxX y b) (boxY y b) A.F 0 A.v grants
    (by rw [patch]; exact cal.first)).2
  obtain ⟨qkind,act⟩:=full A patch kernel season kind plane wedge
  let Q:=barbed A.F A.v χ A.T
  have a0:0 ≤ αm y := by unfold αm hatW Alto.flurry; positivity
  have hp0:0 ≤ y^δ:=Real.rpow_nonneg positive.le _
  have qcrop:Kind (cropAction p Q):=by
    change PowerSeries.coeff 0 (cropAction p Q)=0
    change PowerSeries.coeff 0 Q=0 at qkind
    simpa only [cropAction,PowerSeries.coeff_mk,zero_le,if_true] using qkind
  have cong:Lap p (normalizedRows A χ src p) (growP (cropAction p Q) (cropAction p src) (fullCov A) (p+1)):=by
    apply grow_prefix (straight A.F G) suite.positivity.inv qkind qcrop _ _
      (Nat.lt_succ_self p) (Nat.lt_succ_self p)
    · intro j hj; simp only [cropAction,PowerSeries.coeff_mk,if_pos hj]; rfl
    · intro j hj; simp only [cropAction,PowerSeries.coeff_mk,if_pos hj]
  have prof:Expanse (cropAction p Q) m d:=by
    constructor
    intro j _
    by_cases h:j ≤ p
    · simp only [cropAction,PowerSeries.coeff_mk,if_pos h]
      exact (act j h).2.trans (Nat.add_le_add_right (le_mul_of_one_le_left (Nat.zero_le _) hm) 2)
    simp [cropAction,h]
  rw [cong i hi]
  have toll:driver m (p+1+p) h C (y^δ+y^δ) ≤ y^η:=reserve
  apply Quote.widen (normalized_jet (v:=y^δ) b p m h s a0 (cover A b patch kernel season)
    (cropAction p Q) (cropAction p src) qcrop prof ?_ ?_ hi) toll le_rfl
  · intro j _
    by_cases h:j ≤ p
    · simp only [cropAction,PowerSeries.coeff_mk,if_pos h]
      exact (act j h).1
    simp only [cropAction,PowerSeries.coeff_mk,if_neg h]
    refine ⟨hp0,fun k=>?_⟩
    rw [map_zero]
    exact Quote.nill hp0
  · intro j _
    by_cases h:j ≤ p
    · simp only [cropAction,PowerSeries.coeff_mk,if_pos h]
      exact credit j h
    simp only [cropAction,PowerSeries.coeff_mk,if_neg h,MvPolynomial.totalDegree_zero,Nat.zero_le,and_true]
    exact Quote.nill hp0

end YM.Integration.FVA1Physical.Wilson
