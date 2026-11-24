import YM.Integration.WilsonTagSignedDeviation

/-! Signed connected coefficients of the actual stochastic choice in a local Wilson step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTagCumulantRate
open Filter Set MeasureTheory Lattice Wilson RG Marker OPE.Therm
open YM.Multi YM.Primitives.GCC.Anchor YM.Comparison.RG02.Cumulants
open WilsonTagMarginals WilsonPhysicalTagCumulants
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}

def bill (s : R.Mode) (b : V → ℝ) : ℝ :=
  ∑ t ∈ shards R s, ‖mobiusTop t.val.card‖ * ∏ i ∈ t.val, ∏ j ∈ i.sites, b j

omit [Fintype V] in
theorem bill_nonneg (s : R.Mode) (b : V → ℝ) (hb : ∀ i, 0 ≤ b i) : 0 ≤ bill s b :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun j _ => hb j)

def coefficient {A : Type*} [CommMonoid A] (s : R.Mode) (E : A → ℂ) (F : V → A) : ℂ :=
  (_root_.YM.Extra.Trajectories.connected (moments R E F)).part s

theorem bound {A : Type*} [CommMonoid A] (s : R.Mode) (E : A → ℂ) (hE : E 1=1)
    (F : V → A) (b : V → ℝ)
    (hf : ∀ T : Finset V, ‖E (∏ j ∈ T, F j)‖ ≤ ∏ j ∈ T, b j) :
    ‖coefficient s E F‖ ≤ bill s b := by
  rw [coefficient,cumulant_formula _ _ _ hE]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [norm_mul,norm_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf i.sites))
    (norm_nonneg _)

/-- The absolute partition bill for replacing one normalized subset moment in each product. -/
def slope (s : R.Mode) (b : V → ℝ) : ℝ :=
  ∑ t ∈ shards R s, ‖mobiusTop t.val.card‖ * (t.val.card:ℝ) * ∏ i ∈ t.val, ∏ j ∈ i.sites, b j

omit [Fintype V] in
theorem slope_nonneg (s : R.Mode) (b : V → ℝ) (hb : ∀ i, 0≤b i) : 0 ≤ slope s b :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun j _ => hb j)

private theorem product_difference {I : Type*} [DecidableEq I] (T : Finset I)
    (r d : ℝ) (hr : 0≤r) (f g : I → ℂ) (b : I → ℝ) (hb : ∀ i, 0≤b i)
    (hf : ∀i, ‖f i‖≤b i) (hg : ∀i, ‖g i‖≤b i) (hd : ∀i, r*‖f i-g i‖≤d*b i) :
    r*‖(∏ i ∈ T, f i)-(∏ i ∈ T, g i)‖ ≤ (T.card:ℝ)*d*(∏ i ∈ T, b i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    let x := ∏ j ∈ T,f j
    let y := ∏ j ∈ T,g j
    let B := ∏ j ∈ T,b j
    have hy : ‖y‖≤B := by
      dsimp only [y,B]; rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hg j)
    simp only [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    change r*‖f i*x-g i*y‖≤((T.card:ℝ)+1)*d*(b i*B)
    have hxy : f i*x-g i*y=f i*(x-y)+(f i-g i)*y := by ring
    rw [hxy]
    calc
      _ ≤ r*(‖f i‖*‖x-y‖+‖f i-g i‖*‖y‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le (f i*(x-y)) ((f i-g i)*y)) hr
      _ = ‖f i‖*(r*‖x-y‖)+(r*‖f i-g i‖)*‖y‖ := by ring
      _ ≤ b i*((T.card:ℝ)*d*B)+(d*b i)*B :=
        add_le_add (mul_le_mul (hf i) ih (mul_nonneg hr (norm_nonneg _)) (hb i))
          (mul_le_mul_of_nonneg_right (hd i) (norm_nonneg y) |>.trans
            (mul_le_mul_of_nonneg_left hy ((mul_nonneg hr (norm_nonneg _)).trans (hd i))))
      _ = _ := by ring

theorem transfer {A : Type*} [CommMonoid A] (s : R.Mode) (E L : A → ℂ) (hE : E 1=1) (hL : L 1=1)
    (F : V → A) (b : V → ℝ) (hb : ∀i,0≤b i) (r d : ℝ) (hr : 0≤r)
    (h₁ : ∀ T : Finset V, ‖E (∏ j ∈ T,F j)‖ ≤ ∏ j ∈ T,b j)
    (h₂ : ∀ T : Finset V, ‖L (∏ j ∈ T,F j)‖ ≤ ∏ j ∈ T,b j)
    (hΔ : ∀ T : Finset V, r*‖E (∏ j ∈ T,F j)-L (∏ j ∈ T,F j)‖ ≤ d*(∏ j ∈ T,b j)) :
    r*‖coefficient s E F-coefficient s L F‖ ≤ d*slope s b := by
  let a (i : Hot R) := E (∏ j ∈ i.sites,F j)
  let l (i : Hot R) := L (∏ j ∈ i.sites,F j)
  let B (i : Hot R) := ∏ j ∈ i.sites,b j
  have eq : coefficient s E F-coefficient s L F =
      ∑ t ∈ shards R s, mobiusTop t.val.card*((∏ i ∈ t.val,a i)-(∏ i ∈ t.val,l i)) := by
    rw [coefficient,coefficient,cumulant_formula _ _ _ hE,cumulant_formula _ _ _ hL,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => (mul_sub _ _ _).symm
  rw [eq]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr).trans
  rw [slope,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have step := product_difference t.val r d hr a l B (fun i => Finset.prod_nonneg (fun j _ => hb j))
    (fun i => h₁ i.sites) (fun i => h₂ i.sites) (fun i => hΔ i.sites)
  rw [norm_mul]
  calc
    _ = ‖mobiusTop t.val.card‖*(r*‖(∏ i ∈ t.val,a i)-(∏ i ∈ t.val,l i)‖) := by ring
    _ ≤ ‖mobiusTop t.val.card‖*((t.val.card:ℝ)*d*∏ i ∈ t.val,B i) := mul_le_mul_of_nonneg_left step (norm_nonneg _)
    _ = _ := by dsimp [B]; ring

theorem measurable_table {Ω A : Type*} [MeasurableSpace Ω] [CommMonoid A] (s : R.Mode)
    (E : Ω → A → ℂ) (hE : ∀ W, E W 1=1) (F : Ω → V → A)
    (hj : ∀ T : Finset V, Measurable fun W => E W (∏ j ∈ T, F W j)) :
    Measurable fun W => coefficient s (E W) (F W) := by
  have form W : coefficient s (E W) (F W) = ∑ t ∈ shards R s,
      mobiusTop t.val.card * ∏ i ∈ t.val, E W (∏ j ∈ i.sites, F W j) :=
    cumulant_formula _ _ _ (hE W)
  simp_rw [form]
  apply Finset.measurable_fun_sum
  intro t _
  exact measurable_const.mul (Finset.measurable_fun_prod _ (fun i _ => hj i.sites))

private theorem mass {T : Type*} [Fintype T] (w : T → ℝ) (hw : ∑ t,w t=1) :
    tagAverage (fun t => (w t : ℂ)) 1=1 := by
  apply averaged
  simpa only [← Complex.ofReal_sum,Complex.ofReal_one] using congrArg Complex.ofReal hw

omit [Fintype V] [DecidableEq V] in
private theorem mark_bound {T : Type*} [Fintype T] (w : T → ℝ) (hw : ∑ t,w t=1)
    (hn : ∀t, 0≤w t) (F : V → T → ℂ) (b : V → ℝ) (hb : ∀ i t, ‖F i t‖≤b i)
    (p : Finset V) : ‖tagAverage (fun t => (w t : ℂ)) (∏ j ∈ p, F j)‖ ≤ ∏ j ∈ p, b j := by
  apply WilsonTagSignedDeviation.mean_bound w hn hw
  intro t
  simp only [Finset.prod_apply,norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hb j t)

omit [Fintype V] [DecidableEq V] in
private theorem mark_meas {Ω T : Type*} [MeasurableSpace Ω] [Fintype T] (w : Ω → T → ℝ)
    (hw : ∀ t, Measurable fun W => w W t) (F : V → Ω → T → ℂ)
    (hf : ∀ i t, Measurable fun W => F i W t) (p : Finset V) :
    Measurable fun W => tagAverage (fun t => (w W t : ℂ)) (∏ j ∈ p, F j W) := by
  change Measurable fun W => ∑ t, (w W t : ℂ) * (∏ j ∈ p, F j W) t
  simp only [Finset.prod_apply]
  exact Finset.measurable_fun_sum _ fun t _ =>
    (Complex.continuous_ofReal.measurable.comp (hw t)).mul (Finset.measurable_fun_prod _ fun j _ => hf j t)

variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem clean (h : S.patch.Branches S.kernel G) (s : R.Mode) (X : Finset (Site c))
    (A : Finset (Edge (Site c))) (hx : Ends X A) (W : Config G f)
    (he : W ∉ WilsonTagSignedDeviation.exceptional S X A) (F : V → S.Choices → ℂ)
    (hr : ∀ i, Reads S (F i) X A) :
    coefficient s (tagAverage (fun t => (S.likelihood W t : ℂ))) F =
      coefficient s (tagAverage (fun t => (reference S t : ℂ))) F := by
  apply congrArg (fun u : Poly R => (_root_.YM.Extra.Trajectories.connected u).part s)
  ext y
  simp only [moments_part]
  exact WilsonTagSignedDeviation.agree S h X A hx W he _ (reads_prod S _ F (fun i _ => hr i))

theorem paid (h : S.patch.Branches S.kernel G) (μ : Measure (Config G f)) [IsProbabilityMeasure μ]
    (s : R.Mode) (X : Finset (Site c)) (A : Finset (Edge (Site c))) (hx : Ends X A)
    (F : V → Config G f → S.Choices → ℂ) (b : V → ℝ)
    (bounds : ∀ i W t, ‖F i W t‖ ≤ b i) (hj : ∀ i t, Measurable fun W => F i W t)
    (hr : ∀ i W, Reads S (F i W) X A) :
    let source W := coefficient s (tagAverage fun t => (S.likelihood W t : ℂ)) (fun i => F i W)
    let referenceChart W := coefficient s (tagAverage fun t => (reference S t : ℂ)) (fun i => F i W)
    (∫ W, ‖source W - referenceChart W‖ ∂μ) ≤ μ.real (WilsonTagSignedDeviation.exceptional S X A) * (2*bill s b) := by
  let src (W : Config G f) := tagAverage fun t => (S.likelihood W t : ℂ)
  let ref := tagAverage fun t => (reference S t : ℂ)
  have hs W : src W 1=1 := mass _ (S.chosen h W)
  have ht : ref 1=1 := mass _ (reference_total S)
  have hns W : ‖coefficient s (src W) (fun i => F i W)‖ ≤ bill s b :=
    bound s _ (hs W) _ b (mark_bound _ (S.chosen h W) (S.likelihood_pos W) _ b (fun i t => bounds i W t))
  have hnt W : ‖coefficient s ref (fun i => F i W)‖ ≤ bill s b :=
    bound s _ ht _ b (mark_bound _ (reference_total S) (fun t => by unfold reference; positivity) _ b
      (fun i t => bounds i W t))
  have ms := measurable_table s (fun W => (src W : (S.Choices → ℂ) → ℂ)) hs (fun W i => F i W)
    (mark_meas (fun (W : Config G f) t => S.likelihood W t) (S.likelihood_meas h) F hj)
  have mt := measurable_table s (fun _ : Config G f => (ref : (S.Choices → ℂ) → ℂ)) (fun _ => ht)
    (fun W i => F i W) (mark_meas (fun (_ : Config G f) t => reference S t) (fun _ => measurable_const) F hj)
  exact (WilsonTagSignedDeviation.supported μ _ (WilsonTagSignedDeviation.exceptional_meas S h X A) _
    (ms.sub mt).aestronglyMeasurable (2*bill s b)
    (fun W => (norm_sub_le _ _).trans ((add_le_add (hns W) (hnt W)).trans_eq (two_mul _).symm))
    (fun W he => sub_eq_zero.mpr (clean S h s X A hx W he _ (fun i => hr i W)))).2

/-- Independent mixed sectors at each fixed finite order use the same Wilson labels.
The true regulator estimate counts the union of all eligible local anchor positions. -/
theorem selected (H : Run G) (hG : G.Simple) (P : Poetry H.family.path.levels)
    (prepaid : QLocalPhysicalPatchGate.Paid (WilsonTagCalendar.condition (G:=G)) H.kit) (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m<N → ∀ p, let a := H.family.path.levels
      let S := a.clock.op m p
      ∀ (s : R.Mode) (X : Finset (Site (a.S.side m p))) (A : Finset (Edge (Site (a.S.side m p)))),
        Ends X A → ∀ (F : V → Config G (a.S.side (m+1) p) → S.Choices → ℂ) (b : V → ℝ),
        (∀ i, 0≤b i) → (∀ i W t, ‖F i W t‖ ≤ b i) →
        (∀ i t, Measurable fun W => F i W t) → (∀ i W, Reads S (F i W) X A) →
        (∫ W, ‖coefficient s (tagAverage fun t => (S.likelihood W t : ℂ)) (fun i => F i W) -
          coefficient s (tagAverage fun t => (reference S t : ℂ)) (fun i => F i W)‖ ∂scene H.family.path N p (m+1)) ≤
          (WilsonTagSignedDeviation.anchors X A).card*(a.clock.hatBeta (m+1)^q)⁻¹*(2*bill s b) := by
  filter_upwards [WilsonTagCalendar.selected H hG P prepaid q] with m ready N hm p
  dsimp only
  intro s X A hx F b hb hf hj hr
  let a := H.family.path.levels
  let μ := scene H.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := probability (H:=H.family.path) (p:=p) H.makes.wilson hm
  exact (paid (a.clock.op m p) (a.blocks m p).branches μ s X A hx F b hf hj hr).trans
    (mul_le_mul_of_nonneg_right (ready N hm p (WilsonTagSignedDeviation.anchors X A))
      (mul_nonneg (by norm_num) (bill_nonneg s b hb)))

end YM.Integration.WilsonTagCumulantRate
