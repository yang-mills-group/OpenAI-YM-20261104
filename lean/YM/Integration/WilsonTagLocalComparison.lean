import YM.Integration.WilsonPhysicalTagCumulants

/-! Restriction of a normalized finite product likelihood to the data read by a probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonProductTagRestriction
open YM.Comparison.RG02.Cumulants Finset
open scoped BigOperators Classical
variable {I : Type*} [Fintype I] [DecidableEq I] {K : I → Type*} [∀ i, Fintype (K i)]

def block (A : Finset I) (d : (i:I) → K i → ℂ) (t : (i:I) → K i) : ℂ := ∏ i∈A, d i (t i)

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (K i)] in
private theorem reads (A : Finset I) (d : (i:I) → K i → ℂ) :
    TagCut.Reads (block A d) A := by
  intro x y h
  exact Finset.prod_congr rfl fun i hi => by rw [h i hi]

private theorem unit (A : Finset I) (b d : (i:I) → K i → ℂ)
    (hb : ∀ i, ∑ t, b i t = 1) (hd : ∀ i, ∑ t, b i t*d i t = 1) :
    tagAverage (TagCut.productLaw b) (block A d) = 1 := by
  let c (i : I) (t : K i) := b i t*(if i∈A then d i t else 1)
  have hc (i : I) : ∑ t, c i t=1 := by
    by_cases h : i∈A
    · simpa only [c,if_pos h] using hd i
    · simpa only [c,if_neg h,mul_one] using hb i
  have hp (t : (i:I) → K i) : TagCut.productLaw c t =
      TagCut.productLaw b t * block A d t := by
    unfold TagCut.productLaw c block
    rw [Finset.prod_mul_distrib,← Finset.prod_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  change (∑ t, TagCut.productLaw b t * block A d t) = 1
  simp_rw [← hp]
  exact TagCut.normalized c hc

/-- Every unused label is integrated against its own complete normalized law. -/
theorem restrict (b d : (i:I) → K i → ℂ) (hb : ∀ i, ∑ t, b i t=1)
    (hd : ∀ i, ∑ t, b i t*d i t=1) (A : Finset I) (F : ((i:I) → K i) → ℂ)
    (hF : TagCut.Reads F A) :
    tagAverage (TagCut.productLaw (fun i t => b i t*d i t)) F =
      tagAverage (TagCut.productLaw b) (block A d * F) := by
  have localReads : TagCut.Reads (block A d * F) A := by
    intro x y h
    exact congrArg₂ (·*·) (reads A d x y h) (hF x y h)
  calc
    _ = tagAverage (TagCut.productLaw b) ((block A d * F) * block Aᶜ d) := by
      change (∑ t, _ * F t) = ∑ t, _ * _
      apply Finset.sum_congr rfl
      intro t _
      simp only [TagCut.productLaw,Finset.prod_mul_distrib,Pi.mul_apply,block]
      rw [← Finset.prod_mul_prod_compl A (fun i => d i (t i))]
      ring
    _ = _ := by
      rw [TagCut.factorization b (TagCut.normalized b hb) _ _ disjoint_compl_right localReads (reads Aᶜ d),
        unit Aᶜ b d hb hd,mul_one]

end YM.Integration.WilsonProductTagRestriction

namespace YM.Integration.WilsonTagLocalComparison
open RG Wilson Lattice Comparison.RG02.Cumulants
open WilsonTagMarginals WilsonPhysicalTagCumulants WilsonProductTagRestriction
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (U : Config G f)

private def base {I : Type*} (K : Type*) [Fintype K] (_ : I) (_ : K) : ℂ := (Fintype.card K : ℂ)⁻¹

private theorem base_one {I : Type*} (K : Type*) [Fintype K] [Nonempty K] (i : I) :
    ∑ a : K, base K i a = 1 := by
  have h : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [base,nsmul_eq_mul,h]

private theorem frame (x : Site c) (a : S.patch.FrameTag) :
    base S.patch.FrameTag x a * (frameDensity S U x a : ℂ) = site S U x a := by
  have h : (Fintype.card S.patch.FrameTag : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [base,frameDensity,site,Complex.ofReal_mul,Complex.ofReal_natCast,← mul_assoc,inv_mul_cancel₀ h,one_mul]

private theorem bondDensity (a : S.SitesChoice) (e : Edge (Site c)) (b : S.patch.Points) :
    base S.patch.Points e b * (connectorDensity S U a e b : ℂ) = bond S U a e b := by
  have h : (Fintype.card S.patch.Points : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [base,connectorDensity,bond,Complex.ofReal_mul,Complex.ofReal_natCast,← mul_assoc,inv_mul_cancel₀ h,one_mul]

private theorem reference_eq (a : S.SitesChoice) (b : S.BondChoice) :
    (reference S (a,b) : ℂ) =
      TagCut.productLaw (base S.patch.FrameTag) a * TagCut.productLaw (base S.patch.Points) b := by
  simp [reference,TagCut.productLaw,base]

theorem physical (h : S.patch.Branches S.kernel G) (F : S.Choices → ℂ)
    (X : Finset (Site c)) (A : Finset (Edge (Site c))) (closed : Ends X A) (hf : Reads S F X A) :
    actual S U F = ∑ t, (reference S t : ℂ) *
      (((∏ x∈X, frameDensity S U x (t.1 x)) *
        ∏ e∈A, connectorDensity S U t.1 e (t.2 e) : ℝ) : ℂ) * F t := by
  let sf := fun x a => (frameDensity S U x a : ℂ)
  let bb := fun a e b => (connectorDensity S U a e b : ℂ)
  have hs (i : Site c) : ∑ k, base S.patch.FrameTag i k * sf i k = 1 := by
    simp only [sf,frame,site,← Complex.ofReal_sum,S.patch.frameMass_sum h,Complex.ofReal_one]
  have hb (a : S.SitesChoice) (e : Edge (Site c)) :
      ∑ k, base S.patch.Points e k * bb a e k = 1 := by
    simp only [bb,bondDensity,bond,← Complex.ofReal_sum,S.patch.predictorMass_sum,Complex.ofReal_one]
  have sites := WilsonProductTagRestriction.restrict (base S.patch.FrameTag) sf
    (base_one S.patch.FrameTag) hs X (inner S U F) (siteReads S U F hf closed)
  have bonds (a : S.SitesChoice) := WilsonProductTagRestriction.restrict (base S.patch.Points) (bb a)
    (base_one S.patch.Points) (hb a) A (fun b => F (a,b)) (hf.bonds a)
  dsimp only [sf] at sites
  simp_rw [frame] at sites
  have inner_eq (a : S.SitesChoice) : inner S U F a =
      tagAverage (TagCut.productLaw (base S.patch.Points)) (block A (bb a) * (fun b => F (a,b))) := by
    have ha := bonds a
    dsimp only [bb] at ha
    simp_rw [bondDensity] at ha
    exact ha
  rw [split S U F,sites,Fintype.sum_prod_type]
  change (∑ a:S.SitesChoice, TagCut.productLaw (base S.patch.FrameTag) a *
    (block X sf a * inner S U F a)) = _
  apply Finset.sum_congr rfl
  intro a _
  rw [inner_eq]
  change TagCut.productLaw (base S.patch.FrameTag) a *
    (block X sf a * (∑ b:S.BondChoice,TagCut.productLaw (base S.patch.Points) b *
      (block A (bb a) b * F (a,b)))) = _
  rw [← mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [reference_eq,Complex.ofReal_mul,Complex.ofReal_prod,block,sf,bb]
  ring

end YM.Integration.WilsonTagLocalComparison
