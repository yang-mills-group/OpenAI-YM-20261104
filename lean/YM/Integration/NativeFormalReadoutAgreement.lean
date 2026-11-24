import YM.Integration.NativeFormalSharedCoupling
import YM.FVAAlt2.First.Check

/-! Point and smeared MS coefficients of the moving report agree with the
FVA2 physical field, using the original labels and the full complex test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalReadoutAgreement

open Lattice Labels Extraction PhysicalNext.Repeat.Legato MeasureTheory
open MS MS.Local.Physical MS.Menus MS.Land
open FVA2 FVA2.ColorCode
open FVAAlt2 FVAAlt2.Home FVAAlt2.Home.Profiles
open NativeFormalSharedCoupling

variable {G : Gauge} {d n : ℕ}

/-- Both suppliers evaluate the same continued MS distribution in the
physical basis, at every coefficient and every tuple of points. -/
theorem point (V : Warehouse G) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (w : Fin n → Glyph (wings G) d) (k : ℕ) (x : Points n) :
    area M (Lobby.owner ∘ w) μ k x =
      Fountain.phys V M μ k x d (sameAxis V.F d ∘ w) := by
  rw [Fountain.onLit]
  rfl

theorem marked (V : Warehouse G) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (w : Fin n → Glyph (wings G) d) (k : ℕ) (x : Points n) (hx : x ∈ conf n) :
    area M (Lobby.owner ∘ w) μ k x =
      (Pic.marked V M μ).out d ⟨x, hx⟩ k (sameAxis V.F d ∘ w) :=
  point V M μ w k x

/-- The moving real readout is the real part of the actual FVA2 smearing
for the complete complex profile supplied by the caller. -/
theorem current (R : Run G) (hG : G.Simple) {B : Booked (wings G)} (M : MS_Data G B)
    (μ : ℝ) (p : Datum (Glyph (wings G) d)) (k : ℕ) :
    PowerSeries.coeff k (Report.currentM μ M p) =
      (Spring.ms (warehouse R) M μ d k p.1.n p.1.test (sameAxis (warehouse R).F d ∘ p.2)).re := by
  change PowerSeries.coeff k (forecast M (Lobby.owner ∘ p.2) μ (Subspace.pcanon p.1.test)) = _
  rw [Subspace.forecastR (q := 3) μ R.alloy.B.ratio M (Lobby.owner ∘ p.2) hG (by decide)
    p.1.test (RegulatorIR.FVAAlt2.Lodge.basisR R) k, Spring.invoice]
  apply congrArg Complex.re
  apply integral_congr_ae
  filter_upwards with x
  rw [point (warehouse R) M μ p.2 k x]

/-- The numerical entries of the RG10 field transformation are precisely
the coordinates in the FVA2 named basis. -/
theorem entry (F : Frames G) (x : FormalOPE.RG10.Position.Deck F d)
    (j : Glyph (wings G) d) :
    (dout F (wings G) d x j : ℂ) =
      (sameAxis F d).coord j (FormalOPE.RG10.Position.deck F d x) :=
  dout_at F (wings G) j x

/-- Expand a physical multilinear form in the RG10 field coordinates. -/
theorem expansion (F : Frames G)
    (f : MultilinearMap ℂ (fun _ : Fin n => Pert.Position.E F d) ℂ)
    (x : Fin n → FormalOPE.RG10.Position.Deck F d) :
    f (FormalOPE.RG10.Position.deck F d ∘ x) =
      ∑ w : Fin n → Glyph (wings G) d, f (sameAxis F d ∘ w) * ∏ j, Ωb F (wings G) (x j) (w j) := by
  classical
  calc
    _ = f (fun i => ∑ j, Ωb F (wings G) (x i) j • sameAxis F d j) :=
      congrArg f (funext fun i => (tally_b F (wings G) (x i)).symm)
    _ = _ := by
      rw [MultilinearMap.map_sum]
      exact Finset.sum_congr rfl fun _ _ => (MultilinearMap.map_smul_univ ..).trans (mul_comm ..)

/-- Every coefficient of the moving RG10 report equals the physical
FVA2 coefficient smeared against the same complex test and RG10 fields. -/
theorem science (R : Run G) (hG : G.Simple) {B : Booked (wings G)}
    (M : MS_Data G B) (μ : ℝ) (d : ℕ)
    (p : Datum (FormalOPE.RG10.Position.Deck (warehouse R).F d)) (k : ℕ) :
    PowerSeries.coeff k (Report.science μ M (warehouse R).F d p) =
    (Spring.ms (warehouse R) M μ d k p.1.n p.1.test
      (FormalOPE.RG10.Position.deck (warehouse R).F d ∘ p.2)).re := by
  let V := warehouse R
  rw [expansion V.F (Spring.ms V M μ d k p.1.n p.1.test) p.2, Complex.re_sum]
  unfold Report.science mix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Matrix.map_apply, ← map_prod, PowerSeries.coeff_mul_C]
  rw [current R hG M μ ⟨p.1, w⟩ k]
  have hc : ∏ j, Ωb V.F (wings G) (p.2 j) (w j) =
      (↑(∏ j, dout V.F (wings G) d (p.2 j) (w j)) : ℂ) := by
    push_cast
    simp_rw [dout_at]
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]
  rfl


/-- The FVA2 panel used by the physical transfer has these same RG10
coefficient readings in the original renormalized basis. -/
theorem panel (R : Run G) (hG : G.Simple) {B : Booked (wings G)}
    (M : MS_Data G B) (μ : ℝ) (d : ℕ)
    (p : Datum (FormalOPE.RG10.Position.Deck (warehouse R).F d)) (k : ℕ) :
    PowerSeries.coeff k (Report.science μ M (warehouse R).F d p) =
      ((Pic.marked (warehouse R) M μ).lives d k p.1.n p.1.test
        (FormalOPE.RG10.Position.deck (warehouse R).F d ∘ p.2)).re := by
  rw [Pic.payMark]
  exact science R hG M μ d p k

end YM.Integration.NativeFormalReadoutAgreement
end
