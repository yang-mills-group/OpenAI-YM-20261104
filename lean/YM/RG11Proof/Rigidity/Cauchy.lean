import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import YM.Extra.FREE_DETECTOR_ALGEBRA.Laplace
import YM.Next.MAXWELL.Pole

/-!
# Harmonic collision microscope

Used to infer *full analytic bilocals*, not just some lower Taylor tests, from
absence of one angular singularity. Converse doesn't require uniqueness for
an overdetermined Maxwell system. We use harmonicity alone, which is crucial:
a general analytic term might be swallowed by the regular OPE remainder.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Tensor Analysis Extra.FD SphereTest Filter Set Function
open scoped BigOperators Topology ContDiff
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Harmonicity of centered homogeneous Taylor coefficients. -/
lemma taylor_lap {u : E4 → F} (hq : ContDiffAt ℝ ∞ u 0)
    (h : lap u =ᶠ[𝓝 0] 0) (k : ℕ) : lap (diagonal (coeff u k 0)) = 0 := by
  match k with
  | 0 =>
    let L := coeff u 0 0
    have he : diagonal L = fun _ => L (fun _ => 0) := funext fun x => congr_arg L (Subsingleton.elim ..)
    exact he ▸ SphereTest.lap_zero _
  | 1 =>
    have hl (a : Axis) (z : E4) := Tensor.slot_lower (j:=0) (hq.of_le (WithTop.coe_le_coe.mpr le_top)) (basis a) z
    have hP (a : Axis) : grad a (diagonal (coeff u 1 0)) = fun _ => coeff (grad a u) 0 0 (fun _ => 0) := by
      funext z
      change D _ _ _ = _; rw [hl a z]; unfold Tensor.diagonal; change coeff (grad a u) _ _ _ = _; exact congr_arg _ (Subsingleton.elim ..)
    funext z; simp only [lap,hP]; simp [grad,D]
  | k+2 =>
    funext z; unfold lap
    have ht (i : ℕ) : ContDiffAt ℝ i u 0 := hq.of_le (WithTop.coe_le_coe.mpr le_top)
    have hh (i : ℕ) (a : Axis) : ContDiffAt ℝ i (grad a u) 0 :=
      (grad_smooth_at hq a).of_le (WithTop.coe_le_coe.mpr le_top)
    simp_rw [show ∀ a : Axis, grad a (diagonal (coeff u (k+2) 0))=diagonal (coeff (grad a u) (k+1) 0) from fun a=>
      funext (Tensor.slot_lower (ht (k+2)) (basis a)), show ∀ a : Axis, grad a (Tensor.diagonal (coeff (grad a u) (k+1) 0)) z=Tensor.diagonal (coeff (grad a (grad a u)) k 0) z from fun a=> Tensor.slot_lower (hh (k+1) a) (basis a) z,Tensor.diagonal]
    rw [← sum_apply, ← coeff_sum]
    · rw [GermCoeff k (show (∑ a : Axis, grad a (grad a u)) =ᶠ[𝓝 0] (fun _ => 0) from h.mono fun i hi => by
        rw [Finset.sum_apply]; exact hi), coeff_zero]; rfl
    intro i _; exact (grad_smooth_at (grad_smooth_at hq i) i).of_le (WithTop.coe_le_coe.mpr le_top)

-- No nontrivial harmonic homogeneous polynomial is divisible by the radial
-- square. Keep the extra mass `c` on the quotient to close strong induction.
private lemma killsMultiple (n : ℕ) (f : E4 → F) (hn : Pure n f) (c : ℝ) (hc : 0 < c)
    (he : c • f + qRad • lap f = 0) : f = 0 := by
  induction n using Nat.strong_induction_on generalizing f c with
  | h n ih =>
    suffices hf : lap f = 0 by
      rw [hf,smul_zero,add_zero] at he
      exact (smul_eq_zero.mp he).resolve_left hc.ne'
    match n with
    | 0 => rw [hn.zeroth, SphereTest.lap_zero]; rfl
    | 1 =>
      funext x; unfold lap
      have hp (a) := (hn.derive a).zeroth
      apply Finset.sum_eq_zero; intro i _; nth_rw 1 [hp i]; simp [grad,D]
    | n+2 =>
      have hl := hn.laplace
      apply ih n (by omega) (lap f) hl (c+4*(2+(n:ℝ))) (by positivity)
      have hr := congr_arg lap he
      have hq : ContDiff ℝ ∞ (qRad • lap f) := pure_square.smooth.smul hl.smooth
      rw [lap_add' (hn.vScale c).smooth hq,lap_scale' hn.smooth,lap_raise hl,
        show lap (0 : E4→F) = 0 from SphereTest.lap_zero _] at hr
      simpa [add_smul,add_assoc] using hr

lemma harmonic_multiple (n : ℕ) (f : E4 → F) (hn : Pure n f)
    (he : lap (qRad • f)=0) : f=0 :=
  killsMultiple n f hn (4*(2+(n:ℝ))) (by positivity) ((lap_raise hn).symm.trans he)

end YM.RG11.Rigidity
