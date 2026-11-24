import YM.Integration.LocalComparisonPackets

/-! The literal active mode/power fibres of a paid packet family.
Every fibre is a subtype of the original row index. The only new estimate is
qualitative summability obtained from the existing paid root bill. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace YM.Integration.NativePaidPacketGroups

open Function Finset Lattice Wilson RG Marker Precision
open Comparison.Density.RenderM LocalComparison
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}
variable {D : V → ComparisonDensity.Address.Orbit} {G : Gauge} {n : Side}
variable (P : MarkedPackets D G n R)

/-- An original active row with one fixed original mode and coupling power. -/
def Fiber (s : R.Mode) (z : ℤ) :=
  {i : ℕ // P.mode i = s ∧ P.power i = z ∧ (P.packet i).isSome}

def token (s : R.Mode) (z : ℤ) (i : (NativePaidPacketGroups.Fiber P) s z) :
    Token G n (fun v => (D v).Mood) (P.rank i.val) :=
  (P.packet i.val).get i.property.2.2

theorem token_eq (s : R.Mode) (z : ℤ) (i : (NativePaidPacketGroups.Fiber P) s z) :
    P.packet i.val = some ((NativePaidPacketGroups.token P) s z i) :=
  (Option.some_get i.property.2.2).symm

theorem rank_le (s : R.Mode) (z : ℤ) (i : (NativePaidPacketGroups.Fiber P) s z) :
    P.rank i.val ≤ P.rankCap :=
  P.rank_bounded i.val _ ((NativePaidPacketGroups.token_eq P) s z i)

theorem power_le (s : R.Mode) (z : ℤ) (i : (NativePaidPacketGroups.Fiber P) s z) :
    z.natAbs ≤ P.powerCap := by
  simpa only [i.property.2.1] using
    P.power_bounded i.val _ ((NativePaidPacketGroups.token_eq P) s z i)

theorem grade_le (s : R.Mode) (z : ℤ) (i : (NativePaidPacketGroups.Fiber P) s z) :
    (-z).toNat ≤ P.rank i.val := by
  have h := P.nonnegative_grade i.val _ ((NativePaidPacketGroups.token_eq P) s z i)
  rw [i.property.2.1] at h
  omega

private lemma scale_all {s : Finset V}
    {f : TestSpace D → ℂ}
    (hf : RG3.Held.Letter ℂ (fun v => (D v).Mood) s f)
    (x : TestSpace D) (c : V → ℂ) :
    f (fun v => c v • x v) = (∏ v ∈ s, c v) * f x := by
  let U (a : Finset V) := piecewise a (fun v => c v • x v) x
  have hu (a : Finset V) (ha : a ⊆ s) :
      f (U a) = (∏ v ∈ a, c v) * f x := by
    induction a using Finset.induction with
    | empty => simp [U]
    | insert v a hv ih =>
      rw [show U (insert v a) = update (U a) v (c v • x v) from by
        funext j
        by_cases hj : j = v
        · subst j; simp [U]
        · simp [U, hj]]
      have he : update (U a) v (x v) = U a := by
        rw [← show U a v = x v from piecewise_eq_of_notMem _ _ _ hv, update_eq_self]
      rw [hf.scale (U a) v (ha (mem_insert_self ..)), he,
        ih ((subset_insert ..).trans ha), prod_insert hv]
      ring
  rw [hf.stay (fun v => c v • x v) (U s)
    (fun v hv => by simp [U, hv]),
    hu s (Subset.refl _)]

omit [DecidableEq V] in
private lemma normalize (x : TestSpace D) :
    ∃ (u : TestSpace D) (c : V → ℂ),
      (∀ v, (D v).Bill (u v).val 1) ∧
      ∀ v, x v = c v • u v ∧ c v ≠ 0 := by
  choose J hJ using fun v => (D v).admits (x v)
  let b (v) : ℝ := J v + 1
  have hb v : 0 < b v := add_pos_of_nonneg_of_pos (hJ v).nonneg zero_lt_one
  let c (v) : ℂ := b v
  have hc v : c v ≠ 0 := Complex.ofReal_ne_zero.mpr (hb v).ne'
  let u v := (c v)⁻¹ • x v
  refine ⟨u, c, fun v => ?_, fun v => ⟨(smul_inv_smul₀ (hc v) _).symm, hc v⟩⟩
  apply ComparisonDensity.Address.Orbit.Bill.more ((hJ v).smul _)
  rw [norm_inv, Complex.norm_of_nonneg (hb v).le]
  apply le_trans (mul_le_mul_of_nonneg_left
    (show J v ≤ b v from le_add_of_nonneg_right zero_le_one)
    (inv_nonneg.mpr (hb v).le))
  rw [inv_mul_cancel₀ (hb v).ne']

variable {P} {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}
variable (paid : P.Paid p address region w g width budget offset slope)

include paid in
private lemma coefficient_all_tests (s : R.Mode) (x : TestSpace D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z (i : (NativePaidPacketGroups.Fiber P) s z),
      (∑ j, ‖((NativePaidPacketGroups.token P) s z i).gem j x‖) ≤ M * ((NativePaidPacketGroups.token P) s z i).coin := by
  obtain ⟨u, c, hu, hx⟩ := normalize x
  let t : IndependentTests D := fun v => ⟨(u v).val, hu v⟩
  have ht : testInclusion D t = u := by
    funext v
    apply Subtype.ext
    rfl
  let M : ℝ := ‖∏ v ∈ s.val, c v‖
  refine ⟨M, norm_nonneg _, fun z i => ?_⟩
  have hs := paid.coefficient i.val ((NativePaidPacketGroups.token P) s z i) ((NativePaidPacketGroups.token_eq P) s z i)
  have hgem j :
      ((NativePaidPacketGroups.token P) s z i).gem j x =
        (∏ v ∈ s.val, c v) * ((NativePaidPacketGroups.token P) s z i).gem j u := by
    rw [show x = (fun v => c v • u v) from funext fun v => (hx v).1]
    have h := scale_all
      (paid.multilinear i.val ((NativePaidPacketGroups.token P) s z i) ((NativePaidPacketGroups.token_eq P) s z i) j) u c
    simpa only [i.property.1] using h
  calc
    _ = M * ∑ j, ‖((NativePaidPacketGroups.token P) s z i).gem j u‖ := by
      simp_rw [hgem, norm_mul]
      rw [mul_sum]
    _ ≤ M * ((NativePaidPacketGroups.token P) s z i).coin :=
      mul_le_mul_of_nonneg_left (ht ▸ hs.2 t) (norm_nonneg _)

/-- Real and imaginary atoms retain the original paths and row root. -/
def component {t : ℕ} (T : Token G n (fun v => (D v).Mood) t)
    (x : TestSpace D) (imaginary : Bool) : Atom G t :=
  if imaginary then T.im x else T.re x

omit [DecidableEq V] in
private lemma component_length {t : ℕ}
    (T : Token G n (fun v => (D v).Mood) t) (x : TestSpace D) (b : Bool) :
    (component T x b).length = (T.re x).length := by
  cases b <;> rfl

omit [DecidableEq V] in
private lemma component_magnitude {t : ℕ}
    (T : Token G n (fun v => (D v).Mood) t) (x : TestSpace D) (b : Bool) :
    (component T x b).magnitude ≤ ∑ j, ‖T.gem j x‖ := by
  cases b
  · exact sum_le_sum fun j _ => Complex.abs_re_le_norm _
  · exact sum_le_sum fun j _ => Complex.abs_im_le_norm _

include paid in
/-- The actual root bill pays each fixed mode/power atom series at every test. -/
theorem budget_summable (hg : g ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) (imaginary : Bool) :
    Summable (fun i : (NativePaidPacketGroups.Fiber P) s z => (component ((NativePaidPacketGroups.token P) s z i) x imaginary).budget width) := by
  have hne : s.val.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    apply hs
    apply Subtype.ext
    exact he
  obtain ⟨v, hv⟩ := hne
  obtain ⟨M, hM, hcoef⟩ := coefficient_all_tests paid s x
  let L : ℝ := Poly.toll w s * ‖(g : ℂ) ^ z‖
  have hL : 0 < L := mul_pos (Poly.worth paid.positive s)
    (norm_pos_iff.mpr (zpow_ne_zero z (Complex.ofReal_ne_zero.mpr hg)))
  have hc : Summable (fun i : (NativePaidPacketGroups.Fiber P) s z =>
      L * (((NativePaidPacketGroups.token P) s z i).coin * Real.exp (width * ((NativePaidPacketGroups.token P) s z i).fall))) := by
    have h := (paid.roots v).2.1.subtype
      (fun i => P.mode i = s ∧ P.power i = z ∧ (P.packet i).isSome)
    change Summable (fun i : (NativePaidPacketGroups.Fiber P) s z => _) at h
    apply h.congr
    intro i
    simp only [Function.comp_def, if_pos hv, (NativePaidPacketGroups.token_eq P) s z i,
      i.property.1, i.property.2.1]
    dsimp [L]
    ring
  have hc0 : Summable (fun i : (NativePaidPacketGroups.Fiber P) s z =>
      ((NativePaidPacketGroups.token P) s z i).coin * Real.exp (width * ((NativePaidPacketGroups.token P) s z i).fall)) := by
    have h := hc.mul_left L⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] using h
  apply (hc0.mul_left M).of_nonneg_of_le
  · intro i
    unfold Atom.budget Atom.magnitude
    positivity
  intro i
  have hcoin := (paid.coefficient i.val ((NativePaidPacketGroups.token P) s z i) ((NativePaidPacketGroups.token_eq P) s z i)).1
  have hlen := (paid.paths i.val ((NativePaidPacketGroups.token P) s z i) ((NativePaidPacketGroups.token_eq P) s z i) x).1
  calc
    _ = (component ((NativePaidPacketGroups.token P) s z i) x imaginary).magnitude *
        Real.exp (width * (component ((NativePaidPacketGroups.token P) s z i) x imaginary).length) := rfl
    _ ≤ (M * ((NativePaidPacketGroups.token P) s z i).coin) *
        Real.exp (width * ((NativePaidPacketGroups.token P) s z i).fall) := by
      apply mul_le_mul
      · exact (component_magnitude _ _ _).trans (hcoef z i)
      · apply Real.exp_le_exp.mpr
        rw [component_length]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) paid.width_pos.le
      · positivity
      · exact mul_nonneg hM hcoin
    _ = _ := by ring

end YM.Integration.NativePaidPacketGroups
