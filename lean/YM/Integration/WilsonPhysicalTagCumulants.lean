import YM.Integration.WilsonTagMarginals
import YM.Integration.WilsonLocalKernelPairing

/-! Disconnected contributions to the physical blocking-tag cumulant vanish before integration over the fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalTagCumulants
open YM RG Lattice Wilson MeasureTheory Marker Comparison.RG02.Cumulants Finset
open YM.Multi YM.Primitives.GCC.Anchor
open WilsonTagMarginals
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (U : Config G f)

def vertices (A : Finset (Edge (Site c))) : Finset (Site c) :=
  A.biUnion fun e => {e.1, e.1+Lattice.step e.2}

theorem endpoints (A : Finset (Edge (Site c))) : Ends (vertices A) A := by
  intro e he
  constructor
  · exact Finset.mem_biUnion.mpr ⟨e,he,by simp⟩
  · exact Finset.mem_biUnion.mpr ⟨e,he,by simp⟩

/-- This includes every original forward and reverse marked word on the indicated support. -/
theorem predicted {A : Finset (Edge (Site c))} {F : Config G c → ℂ}
    (hF : ∀ V W : Config G c, (∀ e ∈ A, V e = W e) → F V = F W) :
    Reads S (fun t => F (S.prediction U t)) (vertices A) A := by
  constructor
  · intro b a a' ha
    apply hF
    intro e he
    have h := endpoints A e he
    have hc : S.connector U a e = S.connector U a' e := by
      funext z
      simp only [StepData.connector,StepData.frames,ha _ h.1,ha _ h.2]
    exact congrArg (fun X => S.patch.predict S.kernel X (b e)) hc
  · intro a b b' hb
    apply hF
    intro e he
    simp only [StepData.prediction,hb _ he]

theorem reads_prod {I : Type*} (p : Finset I) (F : I → S.Choices → ℂ)
    {X : Finset (Site c)} {A : Finset (Edge (Site c))}
    (h : ∀ i∈p, Reads S (F i) X A) : Reads S (∏ i∈p,F i) X A := by
  constructor
  · intro b a a' hh
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => (h i hi).sites b a a' hh
  · intro a b b' hh
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun i hi => (h i hi).bonds a b b' hh

theorem disconnected {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}
    (h : S.patch.Branches S.kernel G) (m : R.Mode) (W : V → S.Choices → ℂ)
    (P : Finset V) (hi : (m.val ∩ P).Nonempty) (ho : (m.val \ P).Nonempty)
    {X Y : Finset (Site c)} {A B : Finset (Edge (Site c))}
    (hs : Disjoint X Y) (hb : Disjoint A B) (hx : Ends X A) (hy : Ends Y B)
    (hI : ∀ i∈m.val∩P, Reads S (W i) X A) (hO : ∀ i∈m.val\P, Reads S (W i) Y B) :
    (_root_.YM.Extra.Trajectories.connected (moments R (actual S U) W)).part m = 0 := by
  have hm : ∑ a : S.Choices, (S.likelihood U a : ℂ) = 1 := by
    simpa only [← Complex.ofReal_sum,Complex.ofReal_one] using congrArg Complex.ofReal (S.chosen h U)
  refine cumulant_split _ _ m (averaged _ hm) hi ho (fun s hsub => ?_)
  have hw : (∏ i∈s.val,W i) = (∏ i∈s.val∩P,W i) * (∏ i∈s.val\P,W i) :=
    Eq.trans (by rw [← (merges_side s P).2] :
      (∏ i∈s.val,W i) = ∏ i∈(inside s P).val ∪ (diff s P).val,W i)
      (Finset.prod_union (merges_side s P).1)
  rw [hw]
  exact factor S U h _ _ hs hb hx hy
    (reads_prod S _ W fun i hi => hI i (Finset.inter_subset_inter_right hsub hi))
    (reads_prod S _ W fun i ho => hO i ((Finset.sdiff_subset_sdiff hsub (Subset.refl P)) ho))

private def kernelRows (A : Finset (Edge (Site c))) (b : ℝ) (V Q : Config G c) : ℂ :=
  ∏ e∈A, (WilsonKernelCoupling.link S b (Q e) (V e) : ℂ)

private theorem rowRead (A : Finset (Edge (Site c))) (b : ℝ) (V : Config G c) :
    Reads S (fun t => kernelRows S A b V (S.prediction U t)) (vertices A) A := by
  apply predicted
  intro Q Q' he
  exact Finset.prod_congr rfl fun e h => by rw [he e h]

private theorem observed (A : Finset (Edge (Site c))) (b : ℝ) (V : Config G c) :
    (WilsonKernelCoupling.marginal S A b U (WilsonKernelCoupling.readLinks A V) : ℂ) =
      actual S U (fun t => kernelRows S A b V (S.prediction U t)) := by
  unfold WilsonKernelCoupling.marginal
  rw [Complex.ofReal_sum]
  change _ = ∑ t : S.Choices, (S.likelihood U t : ℂ) * _
  apply Finset.sum_congr rfl
  intro t _
  rw [Complex.ofReal_mul,Complex.ofReal_prod]
  congr 1
  change (∏ i∈A.attach, (WilsonKernelCoupling.link S b (S.prediction U t i.val) (V i.val) : ℂ)) = _
  exact Finset.prod_attach A (fun e => (WilsonKernelCoupling.link S b (S.prediction U t e) (V e) : ℂ))

/-- The full normalized Wilson kernel has a product marginal on sets of links
with disjoint endpoint footprints. Other links have already been integrated out. -/
theorem kernel (h : S.patch.Branches S.kernel G) (A B : Finset (Edge (Site c)))
    (he : Disjoint A B) (hs : Disjoint (vertices A) (vertices B)) (b : ℝ) (V : Config G c) :
    WilsonKernelCoupling.marginal S (A∪B) b U (WilsonKernelCoupling.readLinks (A∪B) V) =
      WilsonKernelCoupling.marginal S A b U (WilsonKernelCoupling.readLinks A V) *
        WilsonKernelCoupling.marginal S B b U (WilsonKernelCoupling.readLinks B V) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,observed S U (A∪B),observed S U A,observed S U B]
  have hp : (fun t => kernelRows S (A∪B) b V (S.prediction U t)) =
      (fun t => kernelRows S A b V (S.prediction U t)) *
      (fun t => kernelRows S B b V (S.prediction U t)) := by
    funext t
    exact Finset.prod_union he
  rw [hp]
  exact WilsonTagMarginals.factor S U h _ _ hs he (endpoints A) (endpoints B)
    (rowRead S U A b V) (rowRead S U B b V)

/-- Uniform pre-eligibility law on every original site and bond label. -/
def reference (_t : S.Choices) : ℝ :=
  (∏ _x : Site c, (Fintype.card S.patch.FrameTag : ℝ)⁻¹) *
    ∏ _e : Edge (Site c), (Fintype.card S.patch.Points : ℝ)⁻¹

def frameDensity (W : Config G f) (x : Site c) (a : S.patch.FrameTag) : ℝ :=
  (Fintype.card S.patch.FrameTag : ℝ) *
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) W) a

def connectorDensity (W : Config G f) (a : S.SitesChoice) (e : Edge (Site c))
    (b : S.patch.Points) : ℝ :=
  (Fintype.card S.patch.Points : ℝ) * S.patch.predictorMass S.kernel (S.connector W a e) b

def density (W : Config G f) (t : S.Choices) : ℝ :=
  (∏ x, frameDensity S W x (t.1 x)) * ∏ e, connectorDensity S W t.1 e (t.2 e)

private theorem restoreProduct {I : Type*} [Fintype I] (n : ℝ) (hn : n ≠ 0) (m : I → ℝ) :
    (∏ _i : I, n⁻¹) * (∏ i : I, n * m i) = ∏ i : I, m i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem reference_total : ∑ t : S.Choices, reference S t = 1 := by
  have h : (Fintype.card S.patch.FrameTag : ℝ) ≠ 0 := by positivity
  have h' : (Fintype.card S.patch.Points : ℝ) ≠ 0 := by positivity
  have card : (Fintype.card S.Choices : ℝ) =
      (Fintype.card S.patch.FrameTag : ℝ) ^ Fintype.card (Site c) *
      (Fintype.card S.patch.Points : ℝ) ^ Fintype.card (Edge (Site c)) := by
    simp [StepData.Choices,StepData.SitesChoice,StepData.BondChoice]
  simp only [reference,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card,Finset.prod_const,inv_pow]
  rw [mul_mul_mul_comm,mul_inv_cancel₀ (pow_ne_zero _ h),mul_inv_cancel₀ (pow_ne_zero _ h'),one_mul]

theorem restore (W : Config G f) (t : S.Choices) :
    reference S t * density S W t = S.likelihood W t := by
  unfold reference density frameDensity connectorDensity StepData.likelihood
  rw [mul_mul_mul_comm,restoreProduct _ (by positivity),restoreProduct _ (by positivity)]

theorem frame_germ (W : Config G f) (x : Site c) (a : S.patch.FrameTag)
    (h : S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) W)) :
    frameDensity S W x a = 1 := by
  have hc : (Fintype.card S.patch.FrameTag : ℝ) ≠ 0 := by positivity
  simp only [frameDensity,Patch.frameMass,if_pos h,mul_inv_cancel₀ hc]

theorem connector_germ (W : Config G f) (a : S.SitesChoice) (e : Edge (Site c))
    (b : S.patch.Points) (h : S.patch.usesBest S.kernel (S.connector W a e)) :
    connectorDensity S W a e b = 1 := by
  have hc : (Fintype.card S.patch.Points : ℝ) ≠ 0 := by positivity
  simp only [connectorDensity,Patch.predictorMass,if_pos h,mul_inv_cancel₀ hc]

/-- Reference labels remain outside the integral even when the sector chart,
Gaussian law, fine field, and signed observable all depend on those labels.
The original eligibility densities stay inside the common integral. -/
theorem sector {Z : S.Choices → Type*} [∀ t, MeasurableSpace (Z t)]
    (μ : ∀ t, MeasureTheory.Measure (Z t)) (W : ∀ t, Z t → Config G f)
    (F : ∀ t, Z t → ℂ) :
    (∑ t, ∫ z, (S.likelihood (W t z) t : ℂ) * F t z ∂μ t) =
      tagAverage (fun t => (reference S t : ℂ))
        (fun t => ∫ z, (density S (W t z) t : ℂ) * F t z ∂μ t) := by
  change (∑ t : S.Choices, _) = ∑ t : S.Choices, (reference S t : ℂ) * _
  apply Finset.sum_congr rfl
  intro t _
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change (S.likelihood (W t z) t : ℂ) * F t z = (reference S t : ℂ) * ((density S (W t z) t : ℂ) * F t z)
    rw [← mul_assoc,← Complex.ofReal_mul,restore]

def fallbackSites (W : Config G f) : Finset (Site c) :=
  Finset.univ.filter fun x => ¬S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) W)

def fallbackBonds (W : Config G f) (a : S.SitesChoice) : Finset (Edge (Site c)) :=
  Finset.univ.filter fun e => ¬S.patch.usesBest S.kernel (S.connector W a e)

/-- On an arbitrary physical field only actual fallback sites and bonds remain
in the density relative to the common reference tag law. -/
theorem restricted (W : Config G f) (t : S.Choices) :
    density S W t = (∏ x∈fallbackSites S W, frameDensity S W x (t.1 x)) *
      ∏ e∈fallbackBonds S W t.1, connectorDensity S W t.1 e (t.2 e) := by
  unfold density
  congr 1
  · symm
    apply Finset.prod_subset (Finset.filter_subset ..)
    intro x _ hx
    exact frame_germ S W x _ (by simpa [fallbackSites] using hx)
  · symm
    apply Finset.prod_subset (Finset.filter_subset ..)
    intro e _ he
    exact connector_germ S W _ e _ (by simpa [fallbackBonds] using he)

theorem frame_range (h : S.patch.Branches S.kernel G) (W : Config G f)
    (x : Site c) (a : S.patch.FrameTag) :
    0 ≤ frameDensity S W x a ∧ frameDensity S W x a ≤ Fintype.card S.patch.FrameTag := by
  let X := expandAt (S.ratio.embed x) W
  have nonneg (k : S.patch.FrameTag) : 0 ≤ S.patch.frameMass S.kernel X k := by
    unfold Patch.frameMass
    split
    · positivity
    split <;> positivity
  have ha : S.patch.frameMass S.kernel X a ≤ 1 := calc
    _ ≤ ∑ k, S.patch.frameMass S.kernel X k :=
      Finset.single_le_sum (fun k _ => nonneg k) (Finset.mem_univ a)
    _ = 1 := S.patch.frameMass_sum h X
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (nonneg a),
    (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)).trans_eq (mul_one _)⟩

theorem connector_range (W : Config G f) (a : S.SitesChoice) (e : Edge (Site c))
    (b : S.patch.Points) :
    0 ≤ connectorDensity S W a e b ∧ connectorDensity S W a e b ≤ Fintype.card S.patch.Points := by
  let X := S.connector W a e
  have nonneg (k : S.patch.Points) : 0 ≤ S.patch.predictorMass S.kernel X k := by
    unfold Patch.predictorMass
    split
    · positivity
    exact S.patch.weight_nonneg _
  have hb : S.patch.predictorMass S.kernel X b ≤ 1 := calc
    _ ≤ ∑ k, S.patch.predictorMass S.kernel X k :=
      Finset.single_le_sum (fun k _ => nonneg k) (Finset.mem_univ b)
    _ = 1 := S.patch.predictorMass_sum (C := S.kernel) X
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (nonneg b),
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans_eq (mul_one _)⟩

/-- Every remaining site or bond costs only its own finite label alphabet. -/
theorem bounded (h : S.patch.Branches S.kernel G) (W : Config G f) (t : S.Choices) :
    density S W t ≤ (Fintype.card S.patch.FrameTag : ℝ) ^ (fallbackSites S W).card *
      (Fintype.card S.patch.Points : ℝ) ^ (fallbackBonds S W t.1).card := by
  rw [restricted]
  calc
    _ ≤ (∏ _x∈fallbackSites S W, (Fintype.card S.patch.FrameTag : ℝ)) *
        ∏ _e∈fallbackBonds S W t.1, (Fintype.card S.patch.Points : ℝ) := by
      apply mul_le_mul
      · exact Finset.prod_le_prod (fun x _ => (frame_range S h W x _).1)
          (fun x _ => (frame_range S h W x _).2)
      · exact Finset.prod_le_prod (fun e _ => (connector_range S W _ e _).1)
          (fun e _ => (connector_range S W _ e _).2)
      · exact Finset.prod_nonneg fun e _ => (connector_range S W _ e _).1
      · positivity
    _ = _ := by simp

end YM.Integration.WilsonPhysicalTagCumulants
