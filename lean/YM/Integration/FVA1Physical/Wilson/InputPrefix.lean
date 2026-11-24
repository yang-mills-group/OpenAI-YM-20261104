import YM.Integration.FVA1Physical.Wilson.ExactOrder

/-! Apply the rooted Gaussian quotient bound to an arbitrary incoming bank
known through precisely the requested order. Both its higher coefficients and
the higher coefficients of the physical action can be forgotten independently. -/
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

theorem joint_crop_prefix (A:Issue G) (χ:ChartRatio G) (p:ℕ) (src:PowerSeries (Pot (Joint A.F G)))
    (kind:Kind A.T) (pd:(mold A.pre A.F A.v).PosDef) :
    Lap p (normalizedRows A χ src p) (normalizedRows (cropIssue A p) χ (cropAction p src) p) := by
  have srcOnly:Lap p (normalizedRows A χ src p) (normalizedRows A χ (cropAction p src) p) := by
    have ok:=well A.F A.v χ _ kind
    apply grow_prefix (straight A.F G) pd.inv ok ok (fun _ _=>rfl) _ (Nat.lt_succ_self p) (Nat.lt_succ_self p)
    intro i hi
    simp only [cropAction,PowerSeries.coeff_mk,if_pos hi]
  exact fun i hi=>(srcOnly i hi).trans (crop_action_prefix A χ p (cropAction p src) kind pd i hi)

theorem required_input_rows (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p m h s:ℕ) (hm:1 ≤ m) {η:ℝ} (hη:0 < η) :
    ∃ δ:ℝ, 0 < δ ∧ ∀ᶠ x:ℝ in atTop, ∀ (A:Issue G) (b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ src:PowerSeries (Pot (Joint A.F G)),
        (∀ i ≤ p,Vault (address A.F G) {b} (αm y) s (h+2*Whisk.ribbon m (p+1+p)+1) 0
          (PowerSeries.coeff i src) (y^δ) ∧ (PowerSeries.coeff i src).totalDegree ≤ m) →
        ∀ i ≤ p,Vault (address A.F G) {b} (αm y) s h 0 (PowerSeries.coeff i (normalizedRows A χ src p)) (y^η) := by
  obtain ⟨δ,hδ,offer⟩:=purchased_normalized_rows J clear χ hχ simple H H' P K branch p m h s hm hη
  obtain ⟨t,buy⟩:=purchased_chart_chance J clear simple H H' P K branch (D:=0) le_rfl 0
  obtain ⟨_,_,theater⟩:=waiting t H H' J χ hχ clear P 3 0
  refine ⟨δ,hδ,?_⟩
  filter_upwards [offer,buy,theater,(Alto.broad.comp (Work.E09.betaF_growth G P.L)).eventually_gt_atTop 0,
    (Work.E09.betaF_growth G P.L).eventually_gt_atTop 0] with x take paid hall positive pos
  intro A b patch kernel season y kind plane wedge src wage i hi
  obtain ⟨grants,cal,_,_⟩:=paid A patch kernel season 0 b (by simp)
  have suite:=(hall.enter _ _ patch season (boxX y b) (boxY y b) A.F 0 A.v grants
    (by rw [patch]; exact cal.first)).2
  rw [joint_crop_prefix A χ p src kind suite.positivity i hi]
  apply take (cropIssue A p) b patch kernel season
  · change PowerSeries.coeff 0 (cropAction p A.T)=0
    unfold Kind at kind
    simpa only [cropAction,PowerSeries.coeff_mk,zero_le,if_true] using kind
  · constructor
    intro j _
    change (PowerSeries.coeff j (cropAction p A.T)).totalDegree ≤ _
    by_cases h:j≤p
    · simpa only [cropAction,PowerSeries.coeff_mk,if_pos h] using plane.profile j h
    simp [cropAction,h]
  · constructor
    intro j _
    change Tin (Measuring.chart A.f G) (Alto.cWidth y) s (j+1) (hatW y) (PowerSeries.coeff j (cropAction p A.T)) (Alto.purse Alto.Dean (hatW y) j)
    by_cases h:j≤p
    · simpa only [cropAction,PowerSeries.coeff_mk,if_pos h] using wedge.shares j h
    simp only [cropAction,PowerSeries.coeff_mk,if_neg h]
    exact (show MvPolynomial.C (0:ℝ)=0 from map_zero _) ▸
      (Tin.constant positive 0 (show 0≤Alto.purse Alto.Dean (hatW y) j from pow_nonneg positive.le _))
  · intro j _
    change Vault (address A.F G) {b} (αm y) s (h+2*Whisk.ribbon m (p+1+p)+1) 0 (PowerSeries.coeff j (cropAction p src)) (y^δ) ∧ (PowerSeries.coeff j (cropAction p src)).totalDegree ≤ m
    by_cases h:j≤p
    · simpa only [cropAction,PowerSeries.coeff_mk,if_pos h] using wage j h
    simp only [cropAction,PowerSeries.coeff_mk,if_neg h,MvPolynomial.totalDegree_zero,Nat.zero_le,and_true]
    exact Quote.nill (Real.rpow_nonneg pos.le _)
  · exact hi

end YM.Integration.FVA1Physical.Wilson
