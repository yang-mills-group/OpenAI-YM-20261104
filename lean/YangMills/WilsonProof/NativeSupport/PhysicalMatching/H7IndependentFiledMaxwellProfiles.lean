import YangMills.WilsonProof.NativeSupport.MaxwellKinematics.MaxwellPupilKinematics
import YM.Integration.WilsonGraphUnorderedMaxwellTrace
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings
import YM.Push.STRESS_FLUX.Pairing
import YM.Maxwell.Curls
import YM.Maxwell.PotentialKernel
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace PhysicalMatching.H7IndependentFiledMaxwellProfiles
open YM YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick YM.StressFlux YM.Analysis
open YangMills PhysicalMatching.H7StandaloneAppointedPublicWardRows
open scoped BigOperators Classical

def reflected (x : E4) (a k : YM.Axis) : ℝ :=
  basis a k - 2*x a*x k*(‖x‖^2)⁻¹
def minor (x : E4) (a b k l : YM.Axis) : ℝ :=
  reflected x a k*reflected x b l - reflected x a l*reflected x b k
def kernelEntry (x : E4) (a b k l : YM.Axis) : ℝ :=
  4*normal*((‖x‖^2)⁻¹)^2*minor x a b k l

theorem curvatureEntry {x : E4} (hx : x ≠ 0) (a b k l : YM.Axis) :
    bareCurl a b k l x = kernelEntry x a b k l := by
  have select (i j : YM.Axis) (y : ℝ) :
      (if i=j then y else 0) = basis j i * y := by
    by_cases h : i=j
    · subst i; simp
    · simp [h,Ne.symm h]
  simp only [bareCurl, Pi.sub_apply, Bare.opp_grad hx, second_Green hx,select,
    kernelEntry,minor,reflected]
  ring

theorem publicPhi (G : Gauge) (a b i l : YM.Axis) :
    phi (G:=G) a b i l = reduceEq (pair G a i b l).val := by
  rw [reduce_pair]
  unfold phi
  apply Finset.sum_congr rfl
  intro c hc
  rw [product_eq]
  rfl

theorem publicPhiVacuum (g : YangMills.GaugeGroup) (x : YM.Points 1)
    (a b i l : YM.Axis) :
    (maxwellReference g).moment x (fun _ => phi (G:=g.core) a b i l) = 0 := by
  change moment g.core x (fun _ => phi (G:=g.core) a b i l) = 0
  rw [← onePoint_at,publicPhi]
  exact vacuum_pair _ _ _ _ x

theorem publicPhiPair (g : YangMills.GaugeGroup) (x : YM.Points 2) (hx : x 0 ≠ x 1)
    (a b i l p q r s : YM.Axis) :
    (maxwellReference g).moment x ![phi (G:=g.core) a b i l, phi (G:=g.core) p q r s] =
      (g.core.lieDim : ℂ) *
        ((kernelEntry (x 0-x 1) a i p r*kernelEntry (x 0-x 1) b l q s +
          kernelEntry (x 0-x 1) a i q s*kernelEntry (x 0-x 1) b l p r : ℝ) : ℂ) := by
  change moment g.core x ![_,_] = _
  rw [publicPhi,publicPhi,← head_at,chains_read g.core hx]
  simp only [chains, curvatureEntry (sub_ne_zero.mpr hx)]

theorem squareCorrelation (g : YangMills.GaugeGroup) (x : YM.Points 2) (hx : x 0 ≠ x 1)
    (a b k l : YM.Axis) :
    (maxwellReference g).moment x ![phi (G:=g.core) a a b b,phi (G:=g.core) k k l l] =
      (2 : ℂ) * g.core.lieDim * (kernelEntry (x 0-x 1) a b k l : ℂ)^2 := by
  rw [publicPhiPair g x hx]
  push_cast
  ring


def transverse (u : E4) : ℝ := (u 2)^2 + (u 3)^2

theorem normFour (u : E4) : ‖u‖^2 = (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2 := by
  simpa [Fin.sum_univ_four, add_assoc, Real.norm_eq_abs, sq_abs] using
    (EuclideanSpace.real_norm_sq_eq u)

theorem e23Kernel (u : E4) (h : u ≠ 0) :
    kernelEntry u 2 3 2 3 = 4 * normal * (‖u‖^2 - 2 * transverse u) / (‖u‖^2)^3 := by
  have hr : ‖u‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  have d01 : (0 : YM.Axis) ≠ 1 := by decide
  have d02 : (0 : YM.Axis) ≠ 2 := by decide
  have d03 : (0 : YM.Axis) ≠ 3 := by decide
  have d10 : (1 : YM.Axis) ≠ 0 := by decide
  have d12 : (1 : YM.Axis) ≠ 2 := by decide
  have d13 : (1 : YM.Axis) ≠ 3 := by decide
  have d20 : (2 : YM.Axis) ≠ 0 := by decide
  have d21 : (2 : YM.Axis) ≠ 1 := by decide
  have d23 : (2 : YM.Axis) ≠ 3 := by decide
  have d30 : (3 : YM.Axis) ≠ 0 := by decide
  have d31 : (3 : YM.Axis) ≠ 1 := by decide
  have d32 : (3 : YM.Axis) ≠ 2 := by decide
  norm_num [kernelEntry, minor, reflected, basis_eq, transverse, d01, d02, d03, d10, d12, d13, d20, d21, d23, d30, d31, d32] <;> field_simp [hr] <;> ring

theorem componentE23 (u : E4) (h : u ≠ 0) :
    (∑ i : YM.Axis, (minor u 0 i 2 3)^2) =
      4 * (u 0)^2 * transverse u / (‖u‖^2)^2 := by
  have hr : ‖u‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  have d01 : (0 : YM.Axis) ≠ 1 := by decide
  have d02 : (0 : YM.Axis) ≠ 2 := by decide
  have d03 : (0 : YM.Axis) ≠ 3 := by decide
  have d10 : (1 : YM.Axis) ≠ 0 := by decide
  have d12 : (1 : YM.Axis) ≠ 2 := by decide
  have d13 : (1 : YM.Axis) ≠ 3 := by decide
  have d20 : (2 : YM.Axis) ≠ 0 := by decide
  have d21 : (2 : YM.Axis) ≠ 1 := by decide
  have d23 : (2 : YM.Axis) ≠ 3 := by decide
  have d30 : (3 : YM.Axis) ≠ 0 := by decide
  have d31 : (3 : YM.Axis) ≠ 1 := by decide
  have d32 : (3 : YM.Axis) ≠ 2 := by decide
  norm_num [Fin.sum_univ_four, minor, reflected, basis_eq, transverse, d01, d02, d03, d10, d12, d13, d20, d21, d23, d30, d31, d32] <;>
    field_simp [hr] <;> first | ring | (rw [normFour]; ring)

theorem componentE01 (u : E4) (h : u ≠ 0) :
    (∑ i : YM.Axis, (minor u 0 i 0 1)^2) =
      1 - 4 * (u 0)^2 * transverse u / (‖u‖^2)^2 := by
  have hr : ‖u‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  have d01 : (0 : YM.Axis) ≠ 1 := by decide
  have d02 : (0 : YM.Axis) ≠ 2 := by decide
  have d03 : (0 : YM.Axis) ≠ 3 := by decide
  have d10 : (1 : YM.Axis) ≠ 0 := by decide
  have d12 : (1 : YM.Axis) ≠ 2 := by decide
  have d13 : (1 : YM.Axis) ≠ 3 := by decide
  have d20 : (2 : YM.Axis) ≠ 0 := by decide
  have d21 : (2 : YM.Axis) ≠ 1 := by decide
  have d23 : (2 : YM.Axis) ≠ 3 := by decide
  have d30 : (3 : YM.Axis) ≠ 0 := by decide
  have d31 : (3 : YM.Axis) ≠ 1 := by decide
  have d32 : (3 : YM.Axis) ≠ 2 := by decide
  have hs : (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2 ≠ 0 := by
    rw [← normFour u]
    exact hr
  simp only [Fin.sum_univ_four, minor, reflected, basis_eq, transverse, normFour u]
  norm_num [d01, d02, d03, d10, d12, d13, d20, d21, d23, d30, d31, d32] <;>
    field_simp [hs] <;> ring

def price (G : Gauge) : ℝ := 32 * G.lieDim * normal^2

theorem filedE23Pair (g : YangMills.GaugeGroup) (hg : g.core.Simple)
    (x : YM.Points 2) (hx : x 0 ≠ x 1) :
    (maxwellReference g).moment x
      ![(H7StandaloneFourSmearedWardReadings.probes hg 0).val,
        (H7StandaloneFourSmearedWardReadings.probes hg 0).val] =
    ((price g.core * (‖x 0 - x 1‖^2 - 2 * transverse (x 0 - x 1))^2 /
      (‖x 0-x 1‖^2)^6 : ℝ) : ℂ) := by
  have label : phi (G := g.core) 2 2 3 3 =
      (H7StandaloneFourSmearedWardReadings.probes hg 0).val :=
    YM.UVNext.FreeStress.PublicPanels.planeLabel (G := g.core) 5
  rw [← label, squareCorrelation g x hx, e23Kernel _ (sub_ne_zero.mpr hx)]
  unfold price
  push_cast
  ring

def rhoLine (rho u s : ℝ) : ℝ := rho + 2*u*s + s^2

theorem translatedE23Derivative (K rho u T : ℝ) (hr : rho ≠ 0) :
    HasDerivAt (fun s : ℝ => K * (rhoLine rho u s - 2*T)^2 / (rhoLine rho u s)^6)
      (-8*K*u*(rho-2*T)*(rho-3*T)/rho^7) 0 := by
  exact H7IndependentMaxwellPupilKinematics.e23Derivative K rho u T hr

end PhysicalMatching.H7IndependentFiledMaxwellProfiles
end
