import YM.Comparison.RG02.Cumulants.TagCut
import YM.RG.Block

/-! Marginals of the actual two-stage blocking-tag law on a frozen fine configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTagMarginals
open YM RG Lattice Wilson Marker Comparison.RG02.Cumulants Finset
open scoped BigOperators Classical

private theorem replace {J : Type*} [Fintype J] [DecidableEq J] {W : J → Type*}
    [∀ j,Fintype (W j)] (u v : ∀ j,W j → ℂ) (hu : ∑ a, TagCut.productLaw u a = 1)
    (hv : ∑ a, TagCut.productLaw v a = 1) (A : Finset J)
    (same : ∀ j∈A, u j = v j) {f : (∀ j,W j) → ℂ} (hf : TagCut.Reads f A) :
    tagAverage (TagCut.productLaw u) f = tagAverage (TagCut.productLaw v) f := by
  let X := ∀ j,W j
  let E := TagCut.swap (W:=W) Aᶜ
  let F (z : X × X) := TagCut.productLaw u z.1 * TagCut.productLaw v z.2 * f z.1
  have inv (z : X × X) : TagCut.productLaw u (E z).1 * TagCut.productLaw v (E z).2 =
      TagCut.productLaw u z.1 * TagCut.productLaw v z.2 := by
    unfold TagCut.productLaw
    simp_rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    change u j (TagCut.hybrid Aᶜ z.1 z.2 j) * v j (TagCut.hybrid Aᶜ z.2 z.1 j) = _
    by_cases hj : j ∈ A
    · simp [TagCut.hybrid,hj,same j hj,mul_comm]
    · simp [TagCut.hybrid,hj]
  have he (z : X × X) : F (E z) =
      TagCut.productLaw u z.1 * (TagCut.productLaw v z.2 * f z.2) := by
    have h : f (TagCut.hybrid Aᶜ z.1 z.2) = f z.2 :=
      hf _ _ fun j hj => by simp [TagCut.hybrid,hj]
    unfold F
    rw [inv]
    change _ * f (TagCut.hybrid Aᶜ z.1 z.2) = _
    rw [h,mul_assoc]
  have hs (a : X) : ∑ b : X, F (a,b) = TagCut.productLaw u a * f a := by
    calc
      _ = ∑ b : X, TagCut.productLaw v b * (TagCut.productLaw u a * f a) :=
        Finset.sum_congr rfl fun b _ => by unfold F; ring
      _ = _ := by rw [← Finset.sum_mul,hv,one_mul]
  calc
    _ = ∑ z : X × X, F z := by rw [Fintype.sum_prod_type]; simp_rw [hs]; rfl
    _ = _ := by
      rw [← Equiv.sum_comp E F]
      simp_rw [he]
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,hu,one_mul]
      rfl

variable {G : Gauge} {c f : Side} (S : StepData c f) (U : Config G f)
def site (i : Site c) (a : S.patch.FrameTag) : ℂ :=
  S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) a
def bond (a : S.SitesChoice) (e : Edge (Site c)) (b : S.patch.Points) : ℂ :=
  S.patch.predictorMass S.kernel (S.connector U a e) b
def inner (F : S.Choices → ℂ) (a : S.SitesChoice) : ℂ :=
  tagAverage (TagCut.productLaw (bond S U a)) (fun b => F (a,b))
def actual (F : S.Choices → ℂ) : ℂ :=
  tagAverage (fun t => (S.likelihood U t : ℂ)) F

theorem site_one (h : S.patch.Branches S.kernel G) :
    ∑ a, TagCut.productLaw (site S U) a = 1 := by
  apply TagCut.normalized
  intro i
  simpa only [site,← Complex.ofReal_sum,Complex.ofReal_one] using
    congrArg Complex.ofReal (S.patch.frameMass_sum h (expandAt (S.ratio.embed i) U))

theorem bond_one (a : S.SitesChoice) : ∑ b, TagCut.productLaw (bond S U a) b = 1 := by
  apply TagCut.normalized
  intro e
  simpa only [bond,← Complex.ofReal_sum,Complex.ofReal_one] using
    congrArg Complex.ofReal (S.patch.predictorMass_sum (C := S.kernel) (S.connector U a e))

theorem split (F : S.Choices → ℂ) :
    actual S U F = tagAverage (TagCut.productLaw (site S U)) (inner S U F) := by
  change (∑ t : S.Choices, (S.likelihood U t : ℂ)*F t) = _
  rw [Fintype.sum_prod_type]
  change _ = ∑ a : S.SitesChoice, TagCut.productLaw (site S U) a *
    ∑ b : S.BondChoice, TagCut.productLaw (bond S U a) b * F (a,b)
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [StepData.likelihood,Complex.ofReal_mul,Complex.ofReal_prod,TagCut.productLaw,
    site,bond,mul_assoc]

/-- A retained bond carries the two site tags used by its physical connector. -/
def Ends (X : Finset (Site c)) (A : Finset (Edge (Site c))) : Prop :=
  ∀ e∈A, e.1∈X ∧ e.1+Lattice.step e.2∈X

structure Reads (F : S.Choices → ℂ) (X : Finset (Site c)) (A : Finset (Edge (Site c))) : Prop where
  sites (b : S.BondChoice) : TagCut.Reads (fun a => F (a,b)) X
  bonds (a : S.SitesChoice) : TagCut.Reads (fun b => F (a,b)) A

theorem siteReads (F : S.Choices → ℂ) {X : Finset (Site c)} {A : Finset (Edge (Site c))}
    (hF : Reads S F X A) (hw : Ends X A) : TagCut.Reads (inner S U F) X := by
  intro a a' ha
  have hm (e) (he : e∈A) : bond S U a e = bond S U a' e := by
    have hc : S.connector U a e = S.connector U a' e := by
      funext z
      simp only [StepData.connector,StepData.frames,ha _ (hw e he).1,ha _ (hw e he).2]
    unfold bond
    rw [hc]
  have hfun : (fun b => F (a,b)) = (fun b => F (a',b)) :=
    funext fun b => hF.sites b a a' ha
  unfold inner
  rw [replace (bond S U a) (bond S U a') (bond_one ..) (bond_one ..) A hm (hF.bonds a),hfun]

theorem factor (h : S.patch.Branches S.kernel G) (F H : S.Choices → ℂ)
    {X Y : Finset (Site c)} {A B : Finset (Edge (Site c))} (hs : Disjoint X Y)
    (hb : Disjoint A B) (hx : Ends X A) (hy : Ends Y B)
    (hF : Reads S F X A) (hH : Reads S H Y B) :
    actual S U (F*H) = actual S U F * actual S U H := by
  have hh : inner S U (F*H) = inner S U F * inner S U H := by
    funext a
    exact TagCut.factorization (bond S U a) (bond_one ..) _ _ hb (hF.bonds a) (hH.bonds a)
  rw [split S U (F*H),hh,split S U F,split S U H]
  exact TagCut.factorization (site S U) (site_one S U h) _ _ hs
    (siteReads S U F hF hx) (siteReads S U H hH hy)

end YM.Integration.WilsonTagMarginals
