import YM.Integration.WilsonOriginalForestSplit
import YM.Integration.WilsonOriginalChargedRawWick

/-! An unmarked field-independent change of drivers factors on the complete original Gaussian table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalScalarGaussianFold
open Function Finset Marker Multi Comparison.RG02 Comparison.RG02.Cumulants
open Primitives.GCC.Anchor Next.Rank Next.SectorChange.Gaussian
open Extra.Trajectories (pass_add)
open scoped BigOperators Classical

variable {I V:Type}[Fintype V][DecidableEq V]{R:Census V}

private theorem as_polynomials (actual alternate:Hot R→Normal.poly I)(c:Poly R)
    (same:∀ z, (lit R (fun h => Cloud.paint z (actual h))).pass =
      c*(lit R (fun h => Cloud.paint z (alternate h))).pass)(s:R.Mode) :
    Cloud.integrand actual s = ∑ a, ∑ b,
      if Poly.merges a b s then (c.part a) • (Cloud.integrand alternate b) else 0 :=by
  apply Valence.Enlist.paint_inj
  intro z
  have eq:=congrArg (fun p:Poly R => p.part s) (same z)
  rw [Poly.part_mul] at eq
  simp_rw [←Cloud.before_log] at eq
  simpa only [map_sum, map_smul, apply_ite (Cloud.paint z), map_zero, smul_eq_mul] using eq

theorem factored (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(m:I→ℂ)
    (actual alternate:Hot R→Normal.poly I)(v:Poly R)(zero:v.part R.quiet=0)
    (same:∀ h, actual h = alternate h + MvPolynomial.C (v.part h.val)) :
    Cloud.prescription Q hQ m actual = v.pass * Cloud.prescription Q hQ m alternate :=by
  have phase (z:I→ℝ) :
      lit R (fun h=>Cloud.paint z (actual h)) =
      v + lit R (fun h=>Cloud.paint z (alternate h)) :=by
    ext s
    rw [Poly.part_plus]
    by_cases hs:s.val.Nonempty
    · rw [part_lit _ ⟨s,hs⟩,part_lit _ ⟨s,hs⟩,same,map_add]
      simp [Cloud.paint,add_comm]
    · have hout:s=R.quiet:=of_not_not (mt (hot_iff_ne s).2 hs)
      rw [hout,zero,part_lit_quiet,part_lit_quiet,zero_add]
  have shared (z:I→ℝ) := (congrArg Poly.pass (phase z)).trans (pass_add zero (part_lit_quiet _))
  ext s
  rw [Poly.part_mul]
  change Cloud.wick Q hQ m (Cloud.integrand actual s)= _
  rw [as_polynomials actual alternate v.pass shared s]
  simp only [map_sum, map_smul, apply_ite (Cloud.wick Q hQ m), map_zero, smul_eq_mul]
  rfl

open Comparison.RG02.Order
variable {J:Census V}{r:ℕ}

theorem normalized (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(m:I→ℂ)
    (actual alternate:Hot (Board J r)→Normal.poly I)(v:Grade J r)
    (zero:v.part (Board J r).quiet=0)(vacant:bottom J r v=v)
    (same:∀ h, actual h = alternate h + MvPolynomial.C (v.part h.val)) :
    ratio (Cloud.prescription Q hQ m actual) = ratio (Cloud.prescription Q hQ m alternate) :=by
  have one (a:Hot (Board J r)→Normal.poly I):UnitLeading (Cloud.prescription Q hQ m a):=by
    rw [UnitLeading,Cloud.prescribed,driven_quiet]
    exact Cloud.wick_one ..
  have pure:bottom J r v.pass=v.pass:=by
    simp only [Poly.pass,map_sum,map_smul,map_pow,vacant]
  apply Eq.symm
  apply ratio_unique (one actual)
  rw [factored Q hQ m actual alternate v zero same]
  unfold denominator
  rw [map_mul,pure,mul_assoc]
  exact congrArg (v.pass * ·) (recovers (one alternate))

end YM.Integration.WilsonOriginalScalarGaussianFold
