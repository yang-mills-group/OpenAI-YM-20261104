import YM.Integration.WilsonConditionalTaylorWheelCommonInput
import YM.Integration.WilsonConditionalTaylorBulkLimit

/-! The complete finite ordered angular coefficient uses the same
normalization in the upper position-space and original finite Wick banks. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelTensors
open Function PowerSeries MvPolynomial FormalBulk08 FormalBulk08.Orb FormalBulk08.Lava FormalBulk08.Lotus
open WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {U:Type} [Fintype U]

theorem painted (r:ℕ) (T:Ten ℝ U r): Blue.paint r T=Lava.facade r T:=by
  change (∑ i:Fin r→U,T i • ∏ j,MvPolynomial.X (i j))=_
  simp only [Lava.facade_eq,Lava.cards,MvPolynomial.smul_eq_C_mul]

theorem rank (P:Gen ℝ U) (finite:FiniteGen P) (pure:Pure P) (r:ℕ):
    Lava.marble r (totalR P)=P r:=by
  apply Lava.facade_unique (Lava.marble_agate _ _) (fun x s=>pure r s x)
  rw [Lava.marble_grade]
  let n:=max finite.choose (r+1)
  have hn:still P n:=fun k hk=>finite.choose_spec k ((Nat.le_max_left ..).trans hk)
  rw [visible hn,map_sum]
  have select (k:ℕ):MvPolynomial.homogeneousComponent r (paint k (P k))=
      if k=r then Lava.facade k (P k) else 0:=by
    rw [painted,MvPolynomial.homogeneousComponent_of_mem (Lava.facade_grade ..)]
    by_cases h:k=r
    · subst k;simp
    · simp [h,Ne.symm h]
  simp only [select]
  have hr:r<n:=lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right ..)
  simp [Finset.mem_range.mpr hr]

theorem actual (P:Pal ℝ U) (k:ℕ) (degree:shellK k P) (pure:∀e,Pure (P e)) (e r:ℕ):
    FormalBulk08.Shore.rancho (flash P) e r=P e r:=by
  rw [Shore.rancho,flash,coeff_mk]
  exact rank (P e) (finite_shell degree e) (pure e) r

end YM.Integration.WilsonConditionalTaylorWheelTensors
end

