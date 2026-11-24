import YM.Integration.WilsonPhysicalMarkedDefectRowCoefficients
import YM.Comparison.Density.Render.Valence
import YM.Comparison.Density.Transport.Taylor

/-! The original coupling and the unscaled link angles are joint variables.
Clearing a physical source's pole preserves each earned Laurent position and
its complete transport paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedWordJointFare
open Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn
open AnalyticBridge.SectorAffine.Offset Comparison.Density
open scoped ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (T : Row P Γ G X)

abbrev Chart (G : Gauge) (n : Side) := ℝ × Directions G n

def power (c : ℕ) := T.lamp.e + c - T.lamp.r

def grain (c : ℕ) (z : Chart G n) : ℝ :=
  z.1 ^ power T c * T.atom.unmasked (increment 1 z.2) T.center

def fare (c j : ℕ) : ℝ :=
  Render.couple j * (Render.couple j) ^ power T c * Render.fareAt T.atom j

theorem tested (c j : ℕ) (z : Chart G n) (hz : ‖z‖ ≤ 1) :
    Through j (grain T c) z (fare T c j) := by
  let fst := ContinuousLinearMap.fst ℝ ℝ (Directions G n)
  let snd := ContinuousLinearMap.snd ℝ ℝ (Directions G n)
  have hf : ‖fst‖ ≤ 1 := fst.opNorm_le_bound zero_le_one fun a => by simpa [fst] using norm_fst_le a
  have hs : ‖snd‖ ≤ 1 := snd.opNorm_le_bound zero_le_one fun a => by simpa [snd] using norm_snd_le a
  have coord : Through j (fun y : Chart G n => y.1) z 1 :=
    Through.control (Push.Uniform.allows_linear (L := fst) hf ((norm_fst_le z).trans hz))
  have monomial := Render.band (x := z) (s := Finset.range (power T c))
    (f := fun _ (y : Chart G n) => y.1) (fun _ _ => coord)
  have hpow : Through j (fun y : Chart G n => y.1 ^ power T c) z
      ((Render.couple j) ^ power T c) := by simpa using monomial
  have hat := Transport.through_pull snd hs (Render.reserved T.atom T.center
    (k := j) ((norm_snd_le z).trans hz))
  exact Render.seam z hpow hat

theorem deployed (c : ℕ) (hc : T.lamp.r ≤ T.lamp.e+c) {g : ℝ} (hg : 0 < g)
    (A : Directions G n) (x : X) :
    T.paint x * (grain T c (g,A) : ℂ) =
      (g:ℂ)^c * T.nominal g x (increment 1 A) := by
  have hp : g ^ power T c = g^c * g^T.lamp.lag := by
    rw [← zpow_natCast g (power T c), ← zpow_natCast g c, ← zpow_add₀ hg.ne']
    congr 1
    unfold power QuadraticLocal.Sunrise.Loan.lag
    omega
  simp only [grain, hp, Row.nominal, Row.grain, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

end YM.Integration.WilsonEmittedWordJointFare
