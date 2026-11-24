import YM.Integration.WilsonNeutralTwoPrintPathStart
import YM.Integration.WilsonNeutralTwoPrintPathQuoted

/-! Sum the true marked angular winding over the retained ordered coordinates.
One of the occupied points anchors the diameter on its actual finite torus. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathRankFare
open Function Finset Lattice Laurent Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open scoped BigOperators Classical
variable {V α I:Type}[NormedAddCommGroup V][Fintype α]{n:Side}{r:ℕ}
  {J:Finset I}{y:I → Cover}{σ A:ℝ}

private theorem spent {p:I→Site n}{f:Ten V (Site n × α) r}(pin:J.Nonempty)
    (hs:0<σ)(funded:Wig (tor n) p σ A J f):
    ∑z,‖f z‖≤A*tiePay α r σ:=by
  obtain ⟨u,hu⟩:=pin
  cases r with
  | zero=>
    rw [Fintype.sum_unique,tiePay,pow_zero,mul_one]
    apply (funded.2 _).trans
    apply mul_le_of_le_one_right funded.1
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
  | succ r=>
    have hk:0<r+1:=Nat.succ_pos _
    calc
      _ ≤ ∑z:Fin (r+1)→Site n × α,A*sail (σ/(r+1:ℕ)) (tor n) (p u) z := by
        apply sum_le_sum
        intro z _
        apply (funded.2 z).trans
        apply mul_le_mul_of_nonneg_left _ funded.1
        have spread (l:Fin (r+1)):(tor n).gap (p u) (z l).1 ≤ Syn (tor n) p J z:=
          leg_le (tor n) (foyer p J z) (.inl ⟨u,hu⟩) (.inr l)
        have cut:=sail_cut (Nat.zero_le (Syn (tor n) p J z)) (le_refl (0:ℝ)) hs hk (p u) z spread
        simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using cut
      _ ≤ A*tiePay α (r+1) σ:=by
        rw [←mul_sum]
        exact mul_le_mul_of_nonneg_left (train_native (α:=α) (div_pos hs (show 0<((r+1:ℕ):ℝ) by positivity)) (p u) (r+1)) funded.1

def tariff (α:Type)[Fintype α](r:ℕ)(s a:ℝ):ℝ:=
  ((priceM α r s+tiePay α r (s/4)+1)*a+a)*tiePay α r (s/32/2)

variable [CompleteSpace V]
theorem original {P:Ten V (Site n × α) r}{F:Ten V (Cloth α) r}
    (pin:J.Nonempty)(room:4*crestCard y J<n.val)(hs:0<σ)(paid:MarkU y J P F σ A):
    ∑z,‖P z-plume F n z‖≤tariff α r σ A*catchW (σ/512) n:=by
  have port:=markOrbit paid pin room hs
  dsimp only at port
  have sum:=spent pin (show 0<σ/32/2 by positivity) port
  simp only [Pi.sub_apply] at sum
  simp_rw [norm_sub_rev (P _) (plume F n _)]
  apply sum.trans_eq
  unfold tariff
  rw [show σ/32/16=σ/512 by ring]
  ring

theorem compared {P Q:Ten V (Site n × α) r}{F:Ten V (Cloth α) r}{τ B:ℝ}
    (pin:J.Nonempty)(room:4*crestCard y J<n.val)(hs:0<σ)(ht:0<τ)
    (first:MarkU y J P F σ A)(second:MarkU y J Q F τ B):
    ∑z,‖P z-Q z‖≤tariff α r σ A*catchW (σ/512) n+tariff α r τ B*catchW (τ/512) n:=by
  calc
    _ ≤ ∑z,(‖P z-plume F n z‖+‖Q z-plume F n z‖):=by
      apply sum_le_sum
      intro z _
      simpa only [←dist_eq_norm,dist_comm (Q z)] using dist_triangle (P z) (plume F n z) (Q z)
    _ ≤ _:=by
      rw [sum_add_distrib]
      exact add_le_add (original pin room hs first) (original pin room ht second)

end YM.Integration.WilsonNeutralTwoPrintPathRankFare
end
