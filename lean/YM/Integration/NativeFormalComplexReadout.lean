import YM.Integration.NativeFormalReadoutAgreement

/-! The complex distribution is determined coefficient by coefficient by
the two real readings of a test and of its multiplication by i. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalComplexReadout

open Lattice Labels Extraction PhysicalNext.Repeat.Legato MeasureTheory
open MS MS.Local.Physical MS.Menus MS.Land
open FVA2 FVA2.ColorCode FVAAlt2.Home
open NativeFormalSharedCoupling

variable {G : Gauge} {d n : ℕ}

def scale {I : Type*} (c : ℂ) (p : Datum I) : Datum I :=
  ⟨⟨p.1.n, c • p.1.test⟩, p.2⟩

/-- The continuum invoice uses the native complex-linear test convention. -/
theorem invoice (V : Warehouse G) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (d k : ℕ) (o : Test n) (c : ℂ) (v : Fin n → Pert.Position.E V.F d) :
    Spring.ms V M μ d k n (c • o) v = c * Spring.ms V M μ d k n o v := by
  rw [Spring.invoice, Spring.invoice]
  change (∫ x, (c * o x) * Fountain.phys V M μ k x d v) =
    c * ∫ x, o x * Fountain.phys V M μ k x d v
  simp_rw [mul_assoc]
  exact integral_const_mul c _

private theorem recover (z : ℂ) : z = ⟨z.re, -(Complex.I * z).re⟩ := by
  apply Complex.ext
  · rfl
  · change z.im = -(Complex.I * z).re
    simp

/-- The original two real MS currency readings recover the full complex
smeared point distribution in every named physical field. -/
theorem current (R : Run G) (hG : G.Simple) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (p : Datum (Glyph (wings G) d)) (k : ℕ) :
    (Pic.marked (warehouse R) M μ).lives d k p.1.n p.1.test (sameAxis (warehouse R).F d ∘ p.2) =
      ⟨PowerSeries.coeff k (Report.currentM μ M p),
        -PowerSeries.coeff k (Report.currentM μ M (scale Complex.I p))⟩ := by
  rw [Pic.payMark, NativeFormalReadoutAgreement.current R hG M μ p k,
    NativeFormalReadoutAgreement.current R hG M μ (scale Complex.I p) k]
  change _ = Complex.mk _ (-(Spring.ms (warehouse R) M μ d k p.1.n (Complex.I • p.1.test)
    (sameAxis (warehouse R).F d ∘ p.2)).re)
  rw [invoice]
  exact recover _

/-- The RG10 detector likewise recovers the full complex native continuum
panel at every order, with the identical test and physical field tuple. -/
theorem panel (R : Run G) (hG : G.Simple) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (d : ℕ) (p : Datum (FormalOPE.RG10.Position.Deck (warehouse R).F d)) (k : ℕ) :
    (Pic.marked (warehouse R) M μ).lives d k p.1.n p.1.test
        (FormalOPE.RG10.Position.deck (warehouse R).F d ∘ p.2) =
      ⟨PowerSeries.coeff k (Report.science μ M (warehouse R).F d p),
        -PowerSeries.coeff k (Report.science μ M (warehouse R).F d (scale Complex.I p))⟩ := by
  rw [Pic.payMark, NativeFormalReadoutAgreement.science R hG M μ d p k,
    NativeFormalReadoutAgreement.science R hG M μ d (scale Complex.I p) k]
  change _ = Complex.mk _ (-(Spring.ms (warehouse R) M μ d k p.1.n (Complex.I • p.1.test)
    (FormalOPE.RG10.Position.deck (warehouse R).F d ∘ p.2)).re)
  rw [invoice]
  exact recover _

/-- All independent complex fields can be reconstructed from the original named
MS currency readings, using the actual physical basis at the Run. -/
theorem fields (R : Run G) (hG : G.Simple) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (d k : ℕ) (p : PertExtension.Physical.Profile)
    (v : Fin p.n → Pert.Position.E (warehouse R).F d) :
    (Pic.marked (warehouse R) M μ).lives d k p.n p.test v =
      ∑ w : Fin p.n → Glyph (wings G) d,
        Complex.mk (PowerSeries.coeff k (Report.currentM μ M ⟨p, w⟩))
          (-PowerSeries.coeff k (Report.currentM μ M (scale Complex.I ⟨p, w⟩))) *
        ∏ i, (sameAxis (warehouse R).F d).repr (v i) (w i) := by
  classical
  let L := (Pic.marked (warehouse R) M μ).lives d k p.n p.test
  let b := sameAxis (warehouse R).F d
  calc
    _ = L (fun i => ∑ j, b.repr (v i) j • b j) :=
      congrArg L (funext fun i => (b.sum_repr (v i)).symm)
    _ = ∑ w : Fin p.n → Glyph (wings G) d, L (b ∘ w) * ∏ i, b.repr (v i) (w i) := by
      rw [MultilinearMap.map_sum]
      exact Finset.sum_congr rfl fun _ _ => (MultilinearMap.map_smul_univ ..).trans (mul_comm ..)
    _ = _ := Finset.sum_congr rfl fun w _ =>
      congrArg (fun z => z * ∏ i, b.repr (v i) (w i))
        (current R hG M μ (⟨p, w⟩ : Datum (Glyph (wings G) d)) k)

end YM.Integration.NativeFormalComplexReadout
end
