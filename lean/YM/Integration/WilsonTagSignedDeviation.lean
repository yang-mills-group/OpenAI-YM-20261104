import YM.Integration.WilsonTagCalendar
import YM.Integration.WilsonTagLocalComparison

/-! Integrated signed errors for the actual jointly sampled eligibility densities, with
each physical site or bond charged once, including when a marked probe revisits it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTagSignedDeviation
open Filter Set MeasureTheory Lattice Wilson RG OPE.Therm
open WilsonPhysicalTagCumulants WilsonTagThermalWindow
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

def product (X : Finset (Site c)) (A : Finset (Edge (Site c))) (W : Config G f) (t : S.Choices) : ℝ :=
  (∏ x∈X, frameDensity S W x (t.1 x)) * ∏ e∈A, connectorDensity S W t.1 e (t.2 e)

def alphabet (X : Finset (Site c)) (A : Finset (Edge (Site c))) : ℝ :=
  (Fintype.card S.patch.FrameTag : ℝ)^X.card * (Fintype.card S.patch.Points : ℝ)^A.card

def anchors (X : Finset (Site c)) (A : Finset (Edge (Site c))) :=
  A ∪ X.image fun x => (x,(0:Axis))

def exceptional (X : Finset (Site c)) (A : Finset (Edge (Site c))) : Set (Config G f) :=
  ⋃ e∈anchors X A, activated S e

theorem product_range (h : S.patch.Branches S.kernel G) (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (W : Config G f) (t : S.Choices) : 0 ≤ product S X A W t ∧ product S X A W t ≤ alphabet S X A := by
  have ha := Finset.prod_le_prod (s:=X) (fun x _ => (frame_range S h W x (t.1 x)).1)
    (fun x _ => (frame_range S h W x (t.1 x)).2)
  have hb := Finset.prod_le_prod (s:=A) (fun e _ => (connector_range S W t.1 e (t.2 e)).1)
    (fun e _ => (connector_range S W t.1 e (t.2 e)).2)
  have h₁ := Finset.prod_nonneg (s:=X) (fun x _ => (frame_range S h W x (t.1 x)).1)
  have h₂ := Finset.prod_nonneg (s:=A) (fun e _ => (connector_range S W t.1 e (t.2 e)).1)
  refine ⟨mul_nonneg h₁ h₂,?_⟩
  simpa only [alphabet,product,Finset.prod_const] using mul_le_mul ha hb h₂ (by positivity)

theorem quiet_factors (X : Finset (Site c)) (A : Finset (Edge (Site c))) (W : Config G f)
    (h : W ∉ exceptional S X A) (t : S.Choices) :
    (∀x∈X,frameDensity S W x (t.1 x)=1) ∧ (∀e∈A,connectorDensity S W t.1 e (t.2 e)=1) := by
  have good (e) (he : e ∈ anchors X A) : W ∉ changed S t e := fun bad =>
    h (Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,⟨t,bad⟩⟩⟩)
  have hs (x) (hx : x∈X) : frameDensity S W x (t.1 x)=1 := by
    by_contra hn
    exact good (x,0) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)) (Or.inl hn)
  have hb (e) (he : e∈A) : connectorDensity S W t.1 e (t.2 e)=1 := by
    by_contra hn
    exact good e (Finset.mem_union_left _ he) (Or.inr hn)
  exact ⟨hs,hb⟩

theorem quiet (X : Finset (Site c)) (A : Finset (Edge (Site c))) (W : Config G f)
    (h : W ∉ exceptional S X A) (t : S.Choices) : product S X A W t = 1 := by
  obtain ⟨hs,hb⟩ := quiet_factors S X A W h t
  exact (congrArg₂ (·*·) (Finset.prod_eq_one hs) (Finset.prod_eq_one hb)).trans (one_mul _)

private theorem expand_cont (x : Site f) : Continuous fun U : Config G f => expandAt x U := by
  unfold expandAt
  fun_prop

private theorem frame_meas (x : Site c) (k : S.patch.FrameTag) :
    Measurable fun W : Config G f => frameDensity S W x k :=
  measurable_const.mul ((S.patch.frameMass_meas _).comp (expand_cont _).measurable)

private theorem bond_meas (h : S.patch.Branches S.kernel G) (t : S.Choices) (e : Edge (Site c)) :
    Measurable fun W : Config G f => connectorDensity S W t.1 e (t.2 e) :=
  measurable_const.mul ((S.patch.predictorMass_meas _).comp (S.connector_meas h t.1 e))

theorem exceptional_meas (h : S.patch.Branches S.kernel G)
    (X : Finset (Site c)) (A : Finset (Edge (Site c))) : MeasurableSet (exceptional (G:=G) S X A) := by
  refine MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun _ => ?_
  unfold activated
  rw [Set.setOf_exists]
  refine MeasurableSet.iUnion fun t => ?_
  exact (measurableSet_eq_fun (frame_meas (G:=G) S e.1 (t.1 e.1)) measurable_const).compl.union
    (measurableSet_eq_fun (bond_meas S h t e) measurable_const).compl

section LocalUniform

private def siteWeight (X : Finset (Site c)) (W : Config G f) (x : Site c) (t : S.patch.FrameTag) : ℝ :=
  if x∈X then (Fintype.card S.patch.FrameTag : ℝ)⁻¹ else S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) W) t

private def bondWeight (A : Finset (Edge (Site c))) (W : Config G f) (a : S.SitesChoice)
    (e : Edge (Site c)) (t : S.patch.Points) : ℝ :=
  if e∈A then (Fintype.card S.patch.Points : ℝ)⁻¹ else S.patch.predictorMass S.kernel (S.connector W a e) t

/-- Replace only the indicated frame and conditional connector laws. All exterior
choices keep their original stochastic dependence on the actual frame vector. -/
def localLaw (X : Finset (Site c)) (A : Finset (Edge (Site c))) (W : Config G f) (t : S.Choices) : ℝ :=
  (∏ x,siteWeight S X W x (t.1 x)) * ∏ e,bondWeight S A W t.1 e (t.2 e)

private theorem uniform_mass (K : Type*) [Fintype K] [Nonempty K] :
    (∑ _ : K,(Fintype.card K:ℝ)⁻¹)=1 := by
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

theorem local_mass (h : S.patch.Branches S.kernel G) (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (W : Config G f) : ∑ t,localLaw S X A W t=1 := by
  have hs (x) : ∑ t, siteWeight S X W x t=1 := by
    by_cases hx : x∈X
    · simpa only [siteWeight,if_pos hx] using uniform_mass S.patch.FrameTag
    · simpa only [siteWeight,if_neg hx] using S.patch.frameMass_sum h (expandAt (S.ratio.embed x) W)
  have hb (a : S.SitesChoice) (e) : ∑ t, bondWeight S A W a e t=1 := by
    by_cases he : e∈A
    · simpa only [bondWeight,if_pos he] using uniform_mass S.patch.Points
    · simpa only [bondWeight,if_neg he] using S.patch.predictorMass_sum (C:=S.kernel) (S.connector W a e)
  have hsites : ∑ a : S.SitesChoice, (∏ x,siteWeight S X W x (a x))=1 := by
    rw [← Fintype.prod_sum]; simp only [hs,Finset.prod_const_one]
  have hbonds (a : S.SitesChoice) : ∑ t : S.BondChoice, (∏ e,bondWeight S A W a e (t e))=1 := by
    rw [← Fintype.prod_sum]; simp only [hb,Finset.prod_const_one]
  rw [Fintype.sum_prod_type]
  unfold localLaw
  simp_rw [← Finset.mul_sum,hbonds,mul_one]
  exact hsites

theorem local_nonneg (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (W : Config G f) (t : S.Choices) : 0≤localLaw S X A W t := by
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro x _
    unfold siteWeight
    split
    · positivity
    unfold Patch.frameMass
    split
    · positivity
    split <;> positivity
  · apply Finset.prod_nonneg
    intro e _
    unfold bondWeight
    split
    · positivity
    unfold Patch.predictorMass
    split
    · positivity
    exact S.patch.weight_nonneg _

theorem local_measurable (h : S.patch.Branches S.kernel G) (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (t : S.Choices) : Measurable fun W : Config G f => localLaw S X A W t := by
  apply Measurable.mul
  · apply Finset.measurable_fun_prod
    intro x _
    by_cases hx : x∈X
    · simpa only [siteWeight,if_pos hx] using (measurable_const : Measurable (fun _ : Config G f => (Fintype.card S.patch.FrameTag:ℝ)⁻¹))
    · simpa only [siteWeight,if_neg hx,Function.comp_def] using (S.patch.frameMass_meas (t.1 x)).comp (expand_cont _).measurable
  · apply Finset.measurable_fun_prod
    intro e _
    by_cases he : e∈A
    · simpa only [bondWeight,if_pos he] using (measurable_const : Measurable (fun _ : Config G f => (Fintype.card S.patch.Points:ℝ)⁻¹))
    · simpa only [bondWeight,if_neg he,Function.comp_def] using (S.patch.predictorMass_meas (t.2 e)).comp (S.connector_meas h t.1 e)

private theorem uniform_of_density {n x : ℝ} (hn : n≠0) (hx : n*x=1) : n⁻¹=x := by
  calc
    n⁻¹ = n⁻¹*(n*x) := by rw [hx,mul_one]
    _ = x := by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem local_equal (X : Finset (Site c)) (A : Finset (Edge (Site c))) (W : Config G f)
    (he : W∉exceptional S X A) (t : S.Choices) : localLaw S X A W t=S.likelihood W t := by
  obtain ⟨hs,hb⟩ := quiet_factors S X A W he t
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro x _
    unfold siteWeight
    split
    · exact uniform_of_density (by positivity) (hs x ‹x∈X›)
    · rfl
  · apply Finset.prod_congr rfl
    intro e _
    unfold bondWeight
    split
    · exact uniform_of_density (by positivity) (hb e ‹e∈A›)
    · rfl
end LocalUniform

def observed (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (F : Config G f → S.Choices → ℂ) (W : Config G f) : ℂ :=
  ∑ t, (reference S t : ℂ) * ((product S X A W t - 1 : ℝ) : ℂ) * F W t

theorem observed_measurable (h : S.patch.Branches S.kernel G)
    (X : Finset (Site c)) (A : Finset (Edge (Site c))) (F : Config G f → S.Choices → ℂ)
    (hf : ∀ t, Measurable fun W => F W t) : Measurable (observed S X A F) := by
  apply Finset.measurable_fun_sum
  intro t _
  have hm : Measurable fun W : Config G f => product S X A W t :=
    (Finset.measurable_fun_prod X (fun x _ => frame_meas S x (t.1 x))).mul
      (Finset.measurable_fun_prod A (fun e _ => bond_meas S h t e))
  exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
    (hm.sub measurable_const))).mul (hf t)

theorem original (h : S.patch.Branches S.kernel G) (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (F : Config G f → S.Choices → ℂ) (closed : WilsonTagMarginals.Ends X A)
    (hf : ∀ W, WilsonTagMarginals.Reads S (F W) X A) (W : Config G f) :
    WilsonTagMarginals.actual S W (F W) -
      Comparison.RG02.Cumulants.tagAverage (fun t => (reference S t : ℂ)) (F W) = observed S X A F W := by
  rw [WilsonTagLocalComparison.physical S W h (F W) X A closed (hf W)]
  change (∑ t:S.Choices, _) - (∑ t:S.Choices, (reference S t:ℂ)*F W t) = ∑ t:S.Choices, _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  push_cast
  unfold product
  push_cast
  ring

theorem agree (h : S.patch.Branches S.kernel G) (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (closed : WilsonTagMarginals.Ends X A) (W : Config G f) (he : W ∉ exceptional S X A)
    (H : S.Choices → ℂ) (hr : WilsonTagMarginals.Reads S H X A) :
    WilsonTagMarginals.actual S W H = Comparison.RG02.Cumulants.tagAverage (fun t => (reference S t : ℂ)) H := by
  apply sub_eq_zero.mp
  rw [original S h X A (fun _ => H) closed (fun _ => hr) W]
  simp [observed,quiet S X A W he]

private theorem uniform (h : S.patch.Branches S.kernel G) (X : Finset (Site c)) (A : Finset (Edge (Site c)))
    (F : Config G f → S.Choices → ℂ) (b : ℝ) (_hb : 0 ≤ b) (bounded : ∀ W t, ‖F W t‖ ≤ b)
    (W : Config G f) : ‖observed S X A F W‖ ≤ (alphabet S X A+1)*b := by
  have r (t : S.Choices) : 0 ≤ reference S t := by unfold reference; positivity
  calc
    _ ≤ ∑ t, ‖(reference S t : ℂ) * ((product S X A W t - 1 : ℝ):ℂ) * F W t‖ := norm_sum_le _ _
    _ ≤ ∑ t, reference S t * ((alphabet S X A+1)*b) := by
      apply Finset.sum_le_sum
      intro t _
      have hp := product_range S h X A W t
      have hc : |product S X A W t - 1| ≤ alphabet S X A+1 := abs_le.mpr ⟨by linarith,by linarith⟩
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (r t)]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hc (bounded W t) (norm_nonneg _) (by linarith)) (r t)
    _ = _ := by rw [← Finset.sum_mul,reference_total,one_mul]


theorem supported {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Set Ω) (hd : MeasurableSet D) (H : Ω → E) (hm : AEStronglyMeasurable H μ)
    (p : ℝ) (bound : ∀ W, ‖H W‖ ≤ p) (off : ∀ W ∉ D, H W = 0) :
    Integrable H μ ∧ (∫ W, ‖H W‖ ∂μ) ≤ μ.real D*p := by
  have hi := Integrable.of_bound hm p (Filter.Eventually.of_forall bound)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ W, D.indicator (fun _ : Ω => p) W ∂μ := by
      apply integral_mono hi.norm ((integrable_const p).indicator hd)
      intro W
      by_cases he : W∈D
      · simpa only [Set.indicator_of_mem he] using bound W
      · change ‖H W‖ ≤ D.indicator (fun _ : Ω => p) W
        rw [Set.indicator_of_notMem he,off W he,norm_zero]
    _ = _ := by rw [integral_indicator hd,setIntegral_const,smul_eq_mul]

theorem mean_bound {T : Type*} [Fintype T] (w : T → ℝ) (hn : ∀t, 0 ≤ w t)
    (hw : ∑ t, w t=1) (F : T→ℂ) (b : ℝ) (hb : ∀ t, ‖F t‖≤b) :
    ‖Comparison.RG02.Cumulants.tagAverage (fun t => (w t : ℂ)) F‖ ≤ b := by
  change ‖∑ t, (w t : ℂ)*F t‖ ≤ b
  calc
    _ ≤ ∑ t, ‖(w t : ℂ)*F t‖ := norm_sum_le _ _
    _ ≤ ∑ t, w t*b := Finset.sum_le_sum fun t _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hn t)]
      exact mul_le_mul_of_nonneg_left (hb t) (hn t)
    _ = _ := by rw [← Finset.sum_mul,hw,one_mul]

theorem measured (h : S.patch.Branches S.kernel G) (μ : Measure (Config G f)) [IsProbabilityMeasure μ]
    (X : Finset (Site c)) (A : Finset (Edge (Site c))) (F : Config G f → S.Choices → ℂ)
    (hm : AEStronglyMeasurable (observed S X A F) μ) (b : ℝ) (hb : 0 ≤ b)
    (bounded : ∀ W t, ‖F W t‖ ≤ b) :
    Integrable (observed S X A F) μ ∧
    (∫ W, ‖observed S X A F W‖ ∂μ) ≤ μ.real (exceptional S X A)*((alphabet S X A+1)*b) := by
  apply supported μ _ (exceptional_meas S h X A) _ hm _ (uniform S h X A F b hb bounded)
  intro W he
  simp [observed,quiet S X A W he]

/-- Every independent bounded signed probe shares the same physical labels and field. -/
theorem selected (R : Run G) (hG : G.Simple) (P : Poetry R.family.path.levels)
    (paid : QLocalPhysicalPatchGate.Paid (WilsonTagCalendar.condition (G:=G)) R.kit) (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m<N → ∀ p, let a := R.family.path.levels
      let S := a.clock.op m p
      ∀ (X : Finset (Site (a.S.side m p))) (A : Finset (Edge (Site (a.S.side m p))))
        (F : Config G (a.S.side (m+1) p) → S.Choices → ℂ) (b : ℝ), 0 ≤ b →
        (∀ W t, ‖F W t‖ ≤ b) → (∀ t, Measurable fun W => F W t) →
        Integrable (observed S X A F) (scene R.family.path N p (m+1)) ∧
        (∫ W, ‖observed S X A F W‖ ∂scene R.family.path N p (m+1)) ≤
          (anchors X A).card*(a.clock.hatBeta (m+1)^q)⁻¹*((alphabet S X A+1)*b) := by
  filter_upwards [WilsonTagCalendar.selected R hG P paid q] with m ready N hm p
  dsimp only
  intro X A F b hb bounded hF
  let a := R.family.path.levels
  let S := a.clock.op m p
  let μ := scene R.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=p) R.makes.wilson hm
  have hh := measured S (a.blocks m p).branches μ X A F
    (observed_measurable S (a.blocks m p).branches X A F hF).aestronglyMeasurable b hb bounded
  have ha : 0 ≤ alphabet S X A := by unfold alphabet; positivity
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right (ready N hm p (anchors X A))
    (mul_nonneg (add_nonneg ha zero_le_one) hb))⟩

/-- True Wilson tag expectation minus the independent reference expectation, evaluated
under the original fine measure. The test may depend arbitrarily on that fine field. -/
theorem physical (R : Run G) (hG : G.Simple) (P : Poetry R.family.path.levels)
    (paid : QLocalPhysicalPatchGate.Paid (WilsonTagCalendar.condition (G:=G)) R.kit) (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m<N → ∀ p, let a := R.family.path.levels
      let S := a.clock.op m p
      ∀ (X : Finset (Site (a.S.side m p))) (A : Finset (Edge (Site (a.S.side m p)))),
        WilsonTagMarginals.Ends X A →
        ∀ (F : Config G (a.S.side (m+1) p) → S.Choices → ℂ) (b : ℝ), 0 ≤ b →
        (∀ W t, ‖F W t‖ ≤ b) → (∀ t, Measurable fun W => F W t) →
        (∀ W, WilsonTagMarginals.Reads S (F W) X A) →
        (∫ W, ‖WilsonTagMarginals.actual S W (F W) -
          Comparison.RG02.Cumulants.tagAverage (fun t => (reference S t : ℂ)) (F W)‖
          ∂scene R.family.path N p (m+1)) ≤
          (anchors X A).card*(a.clock.hatBeta (m+1)^q)⁻¹*(2*b) := by
  filter_upwards [WilsonTagCalendar.selected R hG P paid q] with m ready N hm p
  dsimp only
  intro X A closed F b hb bounded hF reads
  let a := R.family.path.levels
  let S := a.clock.op m p
  let μ := scene R.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=p) R.makes.wilson hm
  let h := (a.blocks m p).branches
  have ht (W : Config G (a.S.side (m+1) p)) : ‖observed S X A F W‖ ≤ 2*b := by
    rw [← original S h X A F closed reads]
    have h₁ := mean_bound (S.likelihood W) (S.likelihood_pos W) (S.chosen h W) (F W) b (bounded W)
    have h₂ := mean_bound (reference S) (fun t => by unfold reference; positivity)
      (reference_total S) (F W) b (bounded W)
    exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (two_mul b).symm)
  have hi := supported μ _ (exceptional_meas S h X A) _ (observed_measurable S h X A F hF).aestronglyMeasurable
    (2*b) ht (fun W he => by simp [observed,quiet S X A W he])
  calc
    _ = ∫ W, ‖observed S X A F W‖ ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall fun W => congrArg norm (original S h X A F closed reads W))
    _ ≤ _ := hi.2.trans (mul_le_mul_of_nonneg_right (ready N hm p (anchors X A)) (mul_nonneg (by norm_num) hb))

end YM.Integration.WilsonTagSignedDeviation
