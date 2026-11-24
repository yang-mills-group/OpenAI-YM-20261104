import YM.Integration.WilsonNeutralFinitePanel
import YM.Integration.WilsonNeutralWeightedDates

/-! Compare ordered fourth-horizon transfers on the original numerical
thermometer fields. The local signed matrix and the independent coarseProduct
condition number enter as distinct invoices on the same quotient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralColumnComparison
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics Source PhysicalNext.Repeat.Legato
open WilsonNeutralGradeFourTransport WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "X" => R.family.label 4 ⧸ scalars R
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "g" => regulatorRun R.family

private instance : IsClosed ((scalars R : Submodule ℂ (R.family.label 4)) : Set (R.family.label 4)) :=
  (scalars R).closed_of_finiteDimensional

def coarseProduct (filed : ℕ → X ≃ₗ[ℂ] X) (m : ℕ) : ℕ → X ≃ₗ[ℂ] X
  | 0 => LinearEquiv.refl ℂ X
  | n+1 => (filed (m+n)).trans (coarseProduct filed m n)

def op (T : X ≃ₗ[ℂ] X) : X →L[ℂ] X := T.toLinearMap.toContinuousLinearMap

private theorem finite_change {E : Type*} [NormedAddCommGroup E] (f : ℕ → E) (a : ℕ → ℝ)
    (len : ℕ) (live : ∀ i, 0≤a i) (budget : ∑ i ∈ range len,a i ≤ 1/2)
    (steps : ∀ l, l<len → ‖f (l+1)-f l‖ ≤ a l*‖f l‖) :
    ‖f len-f 0‖ ≤ 2*‖f 0‖*(∑ i ∈ range len,a i) := by
  have induction_bound (k : ℕ) (hk : k≤len) : ‖f k-f 0‖ ≤ 2*‖f 0‖*(∑ i ∈ range k,a i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have kl : k<len := by omega
      have prev := ih kl.le
      have partialSum : ∑ i ∈ range k,a i ≤ 1/2 := (sum_le_sum_of_subset_of_nonneg
        (range_mono kl.le) (fun i _ _ => live i)).trans budget
      have fw : ‖f k‖ ≤ 2*‖f 0‖ := by
        have tri := norm_add_le (f k-f 0) (f 0)
        rw [sub_add_cancel] at tri
        nlinarith only [tri,prev,mul_le_mul_of_nonneg_left partialSum (norm_nonneg (f 0))]
      have tri := norm_add_le (f (k+1)-f k) (f k-f 0)
      rw [sub_add_sub_cancel] at tri
      rw [sum_range_succ]
      linarith only [tri,prev,steps k kl,mul_le_mul_of_nonneg_left fw (live k)]
  exact induction_bound len le_rfl

/-- The prefix condition number and an adjacent signed estimate on the named leg bound
the drift of either true fourth-horizon leg uniformly in its birth date.
The reporting vector is taken from the same physical cutoff lift. -/
theorem column (simple : G.Simple) (B k : ℕ) (hk : 0<k)
    (K L : ℝ) (hnK : 0≤K) (hnL : 0≤L) :
    ∀ᶠ m in atTop, ∀ N per, (ref : R.family.ref 4 ≤ m) → (top : m≤N) →
    ∀ (A : Group R.family 6) (leg : Fin 2) (filed : ℕ → X ≃ₗ[ℂ] X),
    (∀ l, l<N-m → ‖op R (coarseProduct R filed m l)‖*‖op R (coarseProduct R filed m l).symm‖ ≤
      K*(H (m+l)/H m)^B) →
    let v := fun i => (scalars R).mkQ (coordinates R A i N per leg.succ)
    (∀ i, m ≤ i → i < N → ‖filed i (v (i+1))-v i‖ ≤
      L*(g N per i)^(2*(B+k+1))*Real.log (R.family.S.block i).val*‖v i‖) →
    ‖coarseProduct R filed m (N-m) (v N)-v m‖ ≤
      2*‖v m‖*K*L*((2:ℝ)^(2*(B+k)+2)/G.slopeConstant)*(g N per m)^(2*(B+k)) := by
  let C := K*L*((2:ℝ)^(2*(B+k)+2)/G.slopeConstant)
  have sp := Gauge.slopeConstant_pos simple
  have Cnon : 0≤C := by dsimp [C]; positivity
  have hp (i : ℕ) : 0<H i := zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  filter_upwards [WilsonNeutralWeightedDates.original R simple B k hk,
    (RG01.Physical.hats simple R.family.path.levels).eventually_ge_atTop (max 2 (4*C))] with
    m dates large N per ref top A leg filed prefixPaid
  dsimp only
  intro signed
  let v := fun i => (scalars R).mkQ (coordinates R A i N per leg.succ)
  let f := fun l => coarseProduct R filed m l (v (m+l))
  let a := fun l => K*L*((H (m+l)/H m)^B * (g N per (m+l))^(2*(B+k+1)) *
      Real.log (R.family.S.block (m+l)).val)
  have ln (i : ℕ) : 0≤Real.log (R.family.S.block i).val :=
    Real.log_nonneg (by exact_mod_cast (R.family.S.block i).property)
  have gn (i : ℕ) : 0≤g N per i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have non (l : ℕ) : 0≤a l := by
    dsimp [a]
    exact mul_nonneg (mul_nonneg hnK hnL) (mul_nonneg
      (mul_nonneg (pow_nonneg (div_nonneg (hp _).le (hp _).le) _) (pow_nonneg (gn _) _)) (ln _))
  have sum_paid : ∑ i ∈ range (N-m),a i ≤ C*(g N per m)^(2*(B+k)) := by
    dsimp only [a,C]; rw [←mul_sum]
    exact (mul_le_mul_of_nonneg_left (dates N per top) (mul_nonneg hnK hnL)).trans_eq (by ring)
  have small : C*(g N per m)^(2*(B+k)) ≤ 1/2 := by
    have b := (R.makes.wilson.represents N per m top).band.1
    change H m / 2 ≤ R.family.path.β N per m at b
    have bp := (half_pos (hp m)).trans_le b
    have sq : (g N per m)^2 ≤ 2/H m := by
      rw [regulatorRun,inv_pow,Real.sq_sqrt bp.le,←one_div,div_le_div_iff₀ bp (hp m)]
      linarith only [b]
    have u : (g N per m)^2 ≤ 1 := sq.trans ((div_le_one (hp m)).mpr ((le_max_left ..).trans large))
    have h : ((g N per m)^2)^(B+k) ≤ (g N per m)^2 := by
      simpa using pow_le_pow_of_le_one (sq_nonneg (g N per m)) u (show 1≤B+k by omega)
    rw [pow_mul]
    apply (mul_le_mul_of_nonneg_left (h.trans sq) Cnon).trans
    rw [←mul_div_assoc,div_le_iff₀ (hp m)]
    linarith only [(le_max_right (2:ℝ) (4*C)).trans large]
  have successive (l : ℕ) (hl : l<N-m) : ‖f (l+1)-f l‖ ≤ a l*‖f l‖ := by
    let i := m+l
    have mi : m ≤ i := Nat.le_add_right ..; have it : i < N := by dsimp [i]; omega
    have edit := signed i mi it
    let P := coarseProduct R filed m l
    have qa := (op R P).le_opNorm (filed i (v (i+1))-v i)
    have qb := (op R P.symm).le_opNorm (P (v i))
    change ‖P (filed i (v (i+1))-v i)‖ ≤ _ at qa
    change ‖P.symm (P (v i))‖ ≤ _ at qb
    rw [LinearEquiv.symm_apply_apply] at qb
    let d := L*(g N per i)^(2*(B+k+1))*Real.log (R.family.S.block i).val
    have nd : 0≤d := mul_nonneg (mul_nonneg hnL (pow_nonneg (gn _) _)) (ln _)
    have r := (edit.trans (mul_le_mul_of_nonneg_left qb nd))
    have w := qa.trans (mul_le_mul_of_nonneg_left r (norm_nonneg _))
    have price := mul_le_mul_of_nonneg_right (prefixPaid l hl)
      (mul_nonneg nd (norm_nonneg (P (v i))))
    change ‖P (filed i (v (i+1)))-P (v i)‖ ≤ a l*‖P (v i)‖
    calc
      _ = ‖P (filed i (v (i+1))-v i)‖ := congrArg norm (P.map_sub _ _).symm
      _ ≤ ‖op R P‖*(d*(‖op R P.symm‖*‖P (v i)‖)) := w
      _ = (‖op R P‖*‖op R P.symm‖)*(d*‖P (v i)‖) := by ring
      _ ≤ _ := price
      _ = _ := by dsimp [a,d,i]; ring
  have result := finite_change f a (N-m) non (sum_paid.trans small) successive
  have last : f (N-m) = coarseProduct R filed m (N-m) (v N) :=
    congrArg (fun j => coarseProduct R filed m (N-m) (v j)) (Nat.add_sub_of_le top)
  have first : f 0 = v m := by change v (m+0) = v m; rfl
  rw [last,first] at result
  change ‖coarseProduct R filed m (N-m) (v N)-v m‖ ≤ _
  change ‖coarseProduct R filed m (N-m) (v N)-v m‖ ≤ _ at result
  exact (result.trans (mul_le_mul_of_nonneg_left sum_paid (by positivity))).trans_eq (by dsimp [C,v]; ring)

theorem original (simple : G.Simple) (B k : ℕ) (hk : 0<k)
    (K L : ℝ) (hnK : 0≤K) (hnL : 0≤L) :
    ∀ᶠ m in atTop, ∀ N per, (ref : R.family.ref 4 ≤ m) → (top : m≤N) →
    ∀ (A : Group R.family 6) (leg : Fin 2) (filed : ℕ → X ≃ₗ[ℂ] X),
    (∀ l, l<N-m → ‖op R (coarseProduct R filed m l)‖*‖op R (coarseProduct R filed m l).symm‖ ≤
      K*(H (m+l)/H m)^B) →
    (∀ (i : ℕ) (mi : m ≤ i) (it : i < N) (x : X),
      ‖filed i ((onQuotient R (p:=per) (ref.trans mi) i.le_succ it).symm x) - x‖ ≤
        L*(g N per i)^(2*(B+k+1))*Real.log (R.family.S.block i).val*‖x‖) →
    let v := fun i => (scalars R).mkQ (coordinates R A i N per leg.succ)
    ‖coarseProduct R filed m (N-m) (v N)-v m‖ ≤
      2*‖v m‖*K*L*((2:ℝ)^(2*(B+k)+2)/G.slopeConstant)*(g N per m)^(2*(B+k)) := by

  filter_upwards [column R simple B k hk K L hnK hnL] with m chain N per ref top A leg filed paid signed
  apply chain N per ref top A leg filed paid
  intro i mi it
  let v := fun i => (scalars R).mkQ (coordinates R A i N per leg.succ)
  let T := onQuotient R (p:=per) (ref.trans mi) i.le_succ it
  have hop : T (v (i+1))=v i :=
    (WilsonNeutralGradeFourTransport.original R (p:=per) (ref.trans mi) i.le_succ it A leg).2
  have pull : T.symm (v i)=v (i+1) := T.symm_apply_eq.mpr hop.symm
  have edit := signed i mi it (v i)
  change ‖filed i (T.symm (v i))-v i‖ ≤ _ at edit
  rw [pull] at edit
  exact edit

end YM.Integration.WilsonNeutralColumnComparison
