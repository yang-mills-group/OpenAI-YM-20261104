import YM.Integration.WilsonConditionalTaylorFieldBalance
import YM.Integration.WilsonConditionalTaylorBulkShape

/-! Positive field orders propagate under the measured kinetic reset, even
when the earlier unmarked vacuum differs by its own entropy constant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorFieldReset
open PowerSeries FormalBulk08 Orb Series Reef Shore Lava Wine
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Wave
open WilsonConditionalTaylorFieldBalance WilsonConditionalTaylorResetCoordinates
open WilsonConditionalTaylorBulkShape
open scoped Classical BigOperators
variable {I : Type} [Fintype I] {m:ℕ}

omit [Fintype I] in
theorem positive (U : Pap I) {e : ℕ} (pos : 0<e) : coeff e (splitV U)=coeff e U:=by
  rw [splitV,map_sub,coeff_C,if_neg pos.ne',sub_zero]

theorem transport {I J : Type} [Fintype I] [Fintype J] {U : Pap I} (shape : Ranks U) (s : I→J) :
    Ranks (WilsonMovingPolynomialPull.place s U):=by
  intro e r pos occupied
  apply shape e r pos
  intro zero
  have old := (marble_eq_zero_iff r _).mp zero
  apply occupied
  rw [rancho,marble_eq_zero_iff,WilsonMovingPolynomialPull.place,coeff_map]
  change MvPolynomial.homogeneousComponent r (MvPolynomial.rename s (coeff e U))=0
  rw [←MvPolynomial.rename_homogeneousComponent,old,map_zero]

theorem step (b A B : PowerSeries ℝ) (T Z : Pap I) (Q : MvPolynomial I ℝ)
    (one : Kind T) (post : Kind (Wave.bley b T Q)) (head : coeff 0 Z= -Q)
    (quad : Q.IsHomogeneous 2) (shape : Ranks Z) (prior : Fields m T (splitV Z))
    (hA : Through m b⁻¹ A) (hB : Through m b B) :
    Fields m (Wave.bley b T Q) (splitV (canter A B I Z)):=by
  intro e he r hr
  by_cases nil : e=0
  · subst e;rw [post,splitK]
  have current : 0<e:=by omega
  have bridge {i d : ℕ} (ih : i ≤ m) (dh : 0<d) : MvPolynomial.homogeneousComponent d (coeff i (T-C Q))=
      MvPolynomial.homogeneousComponent d (coeff i Z):=by
    by_cases zero : i=0
    · subst i;rw [map_sub,one,coeff_zero_C,zero_sub,head]
    · have h:=prior i ih d dh
      rw [positive Z (by omega)] at h
      rw [map_sub,coeff_C,if_neg zero,sub_zero,h]
  have cap (i : ℕ) (hi : i ≤ e) (large : i + 2 < r) : rancho T i r=0:=by
    apply (marble_eq_zero_iff r _).mpr
    by_cases zero : i=0
    · subst i;rw [one,map_zero]
    · rw [prior i (by omega) r hr,positive Z (by omega)]
      apply (marble_eq_zero_iff r _).mp
      by_contra occupied
      have bound:=shape i r (by omega) occupied
      omega
  have restored := WilsonConditionalTaylorReclockRows.restored b T Q quad current r cap
  have yielded : MvPolynomial.homogeneousComponent r (coeff e (Wave.bley b T Q))=
      MvPolynomial.homogeneousComponent r (coeff e (canter b⁻¹ b I (T-C Q))) :=
    (marble_grade r _).symm.trans ((congrArg (facade r) restored).trans (marble_grade r _))
  rw [yielded,positive _ current,homogeneous,homogeneous]
  apply Finset.sum_congr rfl
  intro i old
  have inside : i ≤ e:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using old
  have clock := ((hA.pow i).mul (hB.pow r)) (e-i) (by omega)
  simp only [Wine.bill,clock,bridge (inside.trans he) hr]

end YM.Integration.WilsonConditionalTaylorFieldReset

