import YM.Integration.WilsonPhysicalHistoryRetainedSpringJet
import YM.Integration.WilsonPhysicalHistoryRetainedSpringValence
import YM.Integration.FundedPeriodAction

/-! The actual local Wilson action polynomial and its prescribed periodized sum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Finset Lattice RG Wilson Precision Exterior Work.F03 Bid
open WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}

private theorem atomReal (a : Atom G k) (x : Site n) (z : Dir G n) (q : ℕ) (t : ℝ) :
    polynomial a x (collect G z) q t =
      ((∑ r ∈ range (q+1), t^r * CubicMatch.term r
        (fun u : ℝ => a.unmasked (represent (u • z)) x)) : ℝ) := by
  have chart (u : ℝ) : field (collect G z) u = represent (u • z) := by
    funext e
    rw [represent_link]
    rfl
  have smooth : ContDiffAt ℝ ω (fun u : ℝ => a.unmasked (represent (u • z)) x) 0 := by
    change ContDiffAt ℝ ω (fun u : ℝ => ∑ b, a.coeff b * ∏ e,
      (a.leg e).atSite (represent (u • z)) x (b e)) 0
    apply ContDiffAt.sum
    intro b _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro e _
    exact (ContinuousLinearMap.contDiff (PiLp.proj (𝕜:=ℝ) 2 (fun _=>ℝ) (b e))).contDiffAt.comp _
      (CubicMatch.slot_smooth (U:=fun u : ℝ=>represent (u • z)) (CubicMatch.test_ray z) (a.leg e) x)
  rw [atom_ray_polynomial, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  have cast : CubicMatch.term r (fun u : ℝ => (a.unmasked (represent (u • z)) x : ℂ)) =
      ((CubicMatch.term r (fun u : ℝ => a.unmasked (represent (u • z)) x) : ℝ) : ℂ) :=
    CubicMatch.term_linear (k:=r) Complex.ofRealCLM (smooth.of_le le_top)
  simp only [chart, cast, Complex.real_smul, Complex.ofReal_mul]

theorem site_jet (A : ℕ→Atom G k) {σ D : ℝ} (pos : 0<σ)
    (paid : SumBudget (fun i => (A i).budget σ) D) (x : Site n) (z : Dir G n) (q : ℕ) (t : ℝ) :
    siteTaylor A x z q t =
      ((∑ r ∈ range (q+1), t^r * CubicMatch.term r
        (fun u : ℝ => sitePacket A x (represent (u • z)))) : ℝ) := by
  let coeff (s : Signed) (r i : ℕ) :=
    CubicMatch.term r (fun u : ℝ => (A i).unmasked (represent (u • pulled z s)) x)
  have cash (s : Signed) (r : ℕ) : Summable (coeff s r) :=
    (CubicMatch.atom_story (j:=r) pos paid x (CubicMatch.test_ray (pulled z s))).summable
  have tag (s : Signed) :
      (∑' i, polynomial (A i) x (collect G (pulled z s)) q t) =
        ((∑ r ∈ range (q+1), t^r * ∑' i, coeff s r i) : ℝ) := by
    calc
      _ = ∑' i, ((∑ r ∈ range (q+1), t^r * coeff s r i : ℝ) : ℂ) :=
        tsum_congr fun i => atomReal (A i) x (pulled z s) q t
      _ = _ := by
        rw [← Complex.ofReal_tsum]
        congr 1
        rw [Summable.tsum_finsetSum (fun r _ => (cash s r).mul_left (t^r))]
        simp only [tsum_mul_left]
  have localCoeff (r : ℕ) : CubicMatch.term r (fun u : ℝ => sitePacket A x (represent (u • z))) =
      (Fintype.card Signed : ℝ)⁻¹ * ∑ s, ∑' i, coeff s r i :=
    site_coefficient A pos paid x z r
  rw [siteTaylor]
  simp_rw [tag, localCoeff]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.mul_sum]
  ring


private theorem storedSmooth (A : ℕ→Atom G k) {σ D : ℝ} (pos : 0<σ)
    (paid : SumBudget (fun i => (A i).budget σ) D) (x : Site n) (z : Dir G n) :
    ContDiffAt ℝ ω (fun u : ℝ => sitePacket A x (represent (u • z))) 0 := by
  let f (s : Signed) (t : ℝ) := ∑' i, (A i).unmasked (represent (t • pulled z s)) x
  have smooth (s : Signed) : ContDiffAt ℝ ω (f s) 0 :=
    CubicMatch.atom_sum_smooth pos paid x (CubicMatch.test_ray (pulled z s))
  have written : (fun t : ℝ => sitePacket A x (represent (t • z))) =
      fun t => ((Fintype.card Signed:ℝ)⁻¹) • ∑ s, f s t := by
    funext t
    simp only [sitePacket, Patch.average, f, Work.F03.represent_pulled, smul_eq_mul]
  rw [written]
  exact (ContDiffAt.sum (fun s _ => smooth s)).const_smul _

open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FreeResolvent PowerSeries

/-- At fixed period the signed sum of the real rooted derivatives is exactly
the coefficient published for this prism by the finite reclosure. -/
theorem filed_vertex (a : PrismA G) {σ D : ℝ} (hs : 0<σ) (paid : Commission a.cells σ D a.grade)
    (z : Dir G n) (r : ℕ) :
    MvPolynomial.eval ((cloth G n) z)
        (coeff (a.grade-a.rise+r) (X^2 * flash (Mosaic.surf a n))) =
      ∑ x : Site n, CubicMatch.term r (fun t : ℝ => sitePacket a.cells x (represent (t • z))) := by
  have chart (t : ℝ) : mantle (t • (cloth G n) z) = represent (t • z) := by
    simp only [mantle, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have reported := FundedPeriodAction.radial_packet n hs a paid ((cloth G n) z) (a.grade-a.rise+r)
  calc
    _ = CubicMatch.term r (fun t : ℝ => FundedPeriodAction.action n a (represent (t • z))) := by
      simpa only [chart, Nat.le_add_right, if_true, Nat.add_sub_cancel_left, CubicMatch.term, smul_eq_mul] using reported
    _ = _ := by
      simp_rw [FundedPeriodAction.action, packet_sites]
      exact CubicMatch.term_sum (fun x _ => (storedSmooth a.cells hs paid.toll x z).of_le le_top)

/-- The finite spatial sum restores the precise previously filed polynomial,
including every angular coefficient through q on its own torus. -/
theorem filed_site_sum (a : PrismA G) {σ D : ℝ} (hs : 0<σ) (paid : Commission a.cells σ D a.grade)
    (z : Dir G n) (q : ℕ) (g : ℝ) :
    (∑ x : Site n, siteTaylor a.cells x z q g) =
      ∑ r ∈ range (q+1), (g:ℂ)^r *
        (MvPolynomial.eval ((cloth G n) z) (coeff (a.grade-a.rise+r) (X^2 * flash (Mosaic.surf a n))) : ℝ) := by
  simp_rw [site_jet a.cells hs paid.toll, filed_vertex a hs paid]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]

/-- Restore all placements before hearing a finite word under the common original
conditional. Its individual input coefficients are the prescribed finite packets. -/
theorem filed_words {I : Type*} [Fintype I] [DecidableEq I] (Z : SeriesA G)
    {σ D : ℝ} (hs : 0<σ) (draw : Draw Z σ D) (a : I → PrismA G) (member : ∀ i, a i ∈ Z)
    (z : Dir G n) (q : I → ℕ) (g p : ℝ) :
    let w := fun i => (Comparison.RG02.Integral.temperature g * p * (g/Real.sqrt p)^((a i).grade-(a i).rise) : ℝ)
    (∑ x : I → Site n, ∏ i, (w i : ℂ) * siteTaylor (a i).cells (x i) z (q i) g) =
      ∏ i, (w i : ℂ) * ∑ r ∈ range (q i + 1), (g:ℂ)^r *
        (MvPolynomial.eval ((cloth G n) z)
          (coeff ((a i).grade-(a i).rise+r) (X^2 * flash (Mosaic.surf (a i) n))) : ℝ) := by
  intro w
  rw [← Fintype.prod_sum (fun i x => (w i : ℂ) * siteTaylor (a i).cells x z (q i) g)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.mul_sum, filed_site_sum (a i) hs (draw.2 (a i) (member i))]

end YM.Integration.OriginalMarkedRunAction

