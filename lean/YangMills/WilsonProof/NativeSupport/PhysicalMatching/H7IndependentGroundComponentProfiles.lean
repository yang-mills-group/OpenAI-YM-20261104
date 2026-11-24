import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellProfiles
import YangMills.WilsonProof.NativeSupport.MaxwellKinematics.MaxwellPupilKinematics

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7IndependentGroundComponentProfiles
open YM YM.Maxwell YM.Maxwell.Free
open YangMills (GaugeGroup maxwellReference)
open YM.XSpace.Normalize (Index left right)
open H7IndependentFiledMaxwellProfiles
open scoped BigOperators

/-- The first incoming diagonal panel and the original occupied plane. -/
def panelRead (g : GaugeGroup) (x : Points 2) (k l : Axis) : ℂ :=
  ∑ i : Axis, (maxwellReference g).moment x
    ![phi (G := g.core) 0 0 i i, phi (G := g.core) k k l l]

/-- The six original unordered squares in the trace column. -/
def traceRead (g : GaugeGroup) (x : Points 2) (k l : Axis) : ℂ :=
  ∑ b : Index, (maxwellReference g).moment x
    ![phi (G := g.core) (left b) (left b) (right b) (right b),
      phi (G := g.core) k k l l]

private theorem finiteRead {ι : Type*} [Fintype ι] (g : GaugeGroup)
    (x : Points 2) (hx : x 0 ≠ x 1) (a b : ι → Axis) (k l : Axis) :
    (∑ i : ι, (maxwellReference g).moment x
      ![phi (G := g.core) (a i) (a i) (b i) (b i), phi (G := g.core) k k l l]) =
    ((price g.core / (‖x 0 - x 1‖ ^ 2) ^ 4 *
      ∑ i : ι, (minor (x 0 - x 1) (a i) (b i) k l)^2 : ℝ) : ℂ) := by
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [squareCorrelation g x hx]
  simp only [kernelEntry, price, div_eq_mul_inv, inv_pow]
  push_cast
  ring

theorem panelE23 (g : GaugeGroup) (x : Points 2) (hx : x 0 ≠ x 1) :
    panelRead g x 2 3 =
      ((4 * price g.core * ((x 0 - x 1) 0)^2 * transverse (x 0 - x 1) /
        (‖x 0 - x 1‖^2)^6 : ℝ) : ℂ) := by
  rw [panelRead, finiteRead g x hx (fun _ : Axis => 0) (fun i : Axis => i) 2 3,
    componentE23 _ (sub_ne_zero.mpr hx)]
  congr 1
  have hr : ‖x 0 - x 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  field_simp [hr] <;> ring

theorem panelE01 (g : GaugeGroup) (x : Points 2) (hx : x 0 ≠ x 1) :
    panelRead g x 0 1 =
      ((price g.core / (‖x 0 - x 1‖^2)^4 -
        4 * price g.core * ((x 0 - x 1) 0)^2 * transverse (x 0 - x 1) /
          (‖x 0 - x 1‖^2)^6 : ℝ) : ℂ) := by
  rw [panelRead, finiteRead g x hx (fun _ : Axis => 0) (fun i : Axis => i) 0 1,
    componentE01 _ (sub_ne_zero.mpr hx)]
  congr 1
  have hr : ‖x 0 - x 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  field_simp [hr] <;> ring

theorem sixMinors (u : E4) (hu : u ≠ 0) (k l : Axis) (hkl : k ≠ l) :
    (∑ b : Index, (minor u (left b) (right b) k l)^2) = 1 := by
  let ρ := ‖u‖^2
  let c (a : Axis) := H7IndependentMaxwellPupilKinematics.reflection (fun i => u i) ρ a
  have hr : ρ ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hu)
  have hn : (∑ i : Axis, (u i)^2) = ρ := by
    dsimp only [ρ]
    rw [normFour, Fin.sum_univ_four]
  have refl (a b : Axis) : reflected u a b = c b a := by
    dsimp [reflected, c, ρ, H7IndependentMaxwellPupilKinematics.reflection]
    by_cases hab : a = b
    · subst b
      simp [basis_eq, div_eq_mul_inv]
    · simp [basis_eq, hab, Ne.symm hab, div_eq_mul_inv]
  have det (a b : Axis) : minor u a b k l =
      H7IndependentMaxwellPupilKinematics.determinant (c k) (c l) a b := by
    simp only [minor, refl, H7IndependentMaxwellPupilKinematics.determinant]
    ring
  have six (f : Axis → Axis → ℝ) : (∑ b : Index, f (left b) (right b)) =
      f 0 1 + (f 0 2 + (f 0 3 + (f 1 2 + (f 1 3 + f 2 3)))) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    rfl
  calc
    _ = H7IndependentMaxwellPupilKinematics.sixPlanes (c k) (c l) := by
      rw [six (fun a b => (minor u a b k l)^2)]
      simp only [det, H7IndependentMaxwellPupilKinematics.sixPlanes]
    _ = 1 := H7IndependentMaxwellPupilKinematics.fullTrace _ ρ hr hn k l hkl

theorem tracePlane (g : GaugeGroup) (x : Points 2) (hx : x 0 ≠ x 1)
    (k l : Axis) (hkl : k ≠ l) :
    traceRead g x k l = ((price g.core / (‖x 0-x 1‖^2)^4 : ℝ) : ℂ) := by
  rw [traceRead, finiteRead g x hx left right k l, sixMinors _ (sub_ne_zero.mpr hx) k l hkl,
    mul_one]

theorem twoConservationProfiles (g : GaugeGroup) (x : Points 2) (hx : x 0 ≠ x 1) :
    panelRead g x 2 3 + panelRead g x 0 1 = traceRead g x 2 3 ∧
      traceRead g x 0 1 = traceRead g x 2 3 := by
  rw [panelE23 g x hx, panelE01 g x hx, tracePlane g x hx 2 3 (by decide),
    tracePlane g x hx 0 1 (by decide)]
  constructor
  · push_cast
    ring
  · rfl
end PhysicalMatching.H7IndependentGroundComponentProfiles

