import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
import YM.Next.MULTISOURCE.Formal

/-!
# Cumulant calculus on `YM.Marker.Poly`

`connected` is the cumulant (logarithm) convention of
`YM.Extra.Trajectories`, for a table *already* normalized to constant one.

The calculus is polynomial. A useful pointed form uses Euler mark
operators. `λᵢ∂/∂λᵢ`, unlike `∂/∂λᵢ`, descends to the marker
quotient. This works with *any* exclusion census; in particular marker
variables eliminated for support geometry don't present a log/inverse
problem lower in the ideal. The hypothesis of unit vacuum coefficient in the
answers is essential; never treat `connected` without it as a logarithm.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RG02.Marks
open Finset Marker Extra.Trajectories
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι] {R : Census ι}

/-- Euler mark derivation. -/
def euler (i : ι) : Poly R →ₗ[ℂ] Poly R where
  toFun x := Poly.inject fun s => if i ∈ s.val then x.part s else 0
  map_add' x y := Poly.ext fun s => by
    rw [Poly.part_plus]
    change (if i ∈ s.val then (x+y).part s else 0) =
      (if i ∈ s.val then x.part s else 0)+(if i ∈ s.val then y.part s else 0)
    split <;> simp [*]
  map_smul' r x := Poly.ext fun s => by
    simp only [RingHom.id_apply, Poly.part_smul]
    change (if i ∈ s.val then (r • x).part s else 0) = r*(if i ∈ s.val then x.part s else 0)
    split <;> simp [*]

@[simp] theorem part_euler (i : ι) (x : Poly R) (s : R.Mode) :
    (euler i x).part s = if i ∈ s.val then x.part s else 0 := rfl

theorem quiet_euler (i : ι) (x : Poly R) : (euler i x).part R.quiet = 0 := by simp [Census.quiet]

/-- A table on any down-set is determined by pointing and the vacuum entry. -/
theorem ext_euler {x y : Poly R} (hq : x.part R.quiet = y.part R.quiet) (hm : ∀ i : ι, euler i x = euler i y) :
    x = y := by
  ext s
  by_cases h : s.val.Nonempty
  · obtain ⟨i, hi⟩ := h
    simpa only [part_euler, if_pos hi] using congr_arg (fun p : Poly R => p.part s) (hm i)
  exact (show s = R.quiet from Subtype.ext (not_nonempty_iff_eq_empty.mp h)).symm ▸ hq

theorem euler_one (i : ι) : euler i (1 : Poly R) = 0 := by
  ext s
  by_cases h : s = R.quiet
  · subst s; simp [Census.quiet]
  simp [h]

theorem euler_mul (i : ι) (x y : Poly R) : euler i (x*y) = (euler i x)*y + x*(euler i y) := by
  ext s
  simp only [part_euler, Poly.part_plus, Poly.part_mul]
  rw [← sum_add_distrib]
  by_cases hi : i ∈ s.val
  · rw [if_pos hi]; apply sum_congr rfl; intro p _; rw [← sum_add_distrib]
    apply sum_congr rfl; intro q _
    split
    next h =>
      obtain hp|hq := mem_union.mp (h.2.symm ▸ hi : i ∈ p.val ∪ q.val)
      · have he : i ∉ q.val := fun hh => disjoint_left.mp h.1 hp hh
        simp [hp,he]
      have he : i ∉ p.val := fun hh => disjoint_left.mp h.1 hh hq
      simp [hq,he]
    next h => simp
  rw [if_neg hi]; symm; apply sum_eq_zero; intro p _; rw [← sum_add_distrib]
  refine sum_eq_zero fun q _ => ?_
  split <;> rename_i h
  · have hp : i ∉ p.val := fun hh => hi (h.2 ▸ mem_union_left _ hh)
    have hq : i ∉ q.val := fun hh => hi (h.2 ▸ mem_union_right _ hh)
    simp [hp,hq]
  simp

theorem euler_pow (i : ι) (x : Poly R) (k : ℕ) :
    euler i (x^(k+1)) = (k+1 : ℂ) • (x^k * euler i x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ x (k+1), euler_mul, ih]
    rw [smul_mul_assoc, show x^k * (euler i x)*x = x^(k+1)*euler i x by rw [pow_succ]; ac_rfl]
    simp only [Nat.cast_add_one, add_smul, one_smul]

section ExpLog
variable [Fintype ι]

theorem euler_pass {x : Poly R} (hx : x.part R.quiet = 0) (i : ι) :
    euler i (Poly.pass x) = Poly.pass x * euler i x := by
  let n := Fintype.card ι
  -- allow one more, even though a^n * D a=0 in the quotient
  have h : n ≤ n+1 := Nat.le_succ _
  conv_lhs => rw [Multi.pass_extended x hx h]
  unfold Poly.pass
  rw [map_sum, sum_range_succ', sum_mul]
  simp only [map_smul, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    euler_one, smul_zero, add_zero, euler_pow, smul_smul, smul_mul_assoc]
  refine sum_congr rfl fun k _ => ?_
  have he : ((k+1).factorial:ℂ)⁻¹ * (k+1:ℂ) = (k.factorial:ℂ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
    have ht : (k+1:ℂ) ≠ 0 := by exact_mod_cast (by omega : (k+1:ℕ) ≠ 0)
    rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ ht, mul_one]
  rw [he]

theorem recover_connected {x : Poly R} (hx : x.part R.quiet = 0) :
    connected (Poly.pass x) = x :=
  pass_inj (connected_quiet (Poly.pass_part x hx)) hx (pass_connected (Poly.pass_part x hx))

theorem euler_connected {x : Poly R} (hx : x.part R.quiet = 1) (i : ι) :
    euler i x = x * euler i (connected x) := by
  nth_rw 1 [← pass_connected hx]
  rw [euler_pass (connected_quiet hx), pass_connected hx]

theorem unit_of_quiet_one {x : Poly R} (hx : x.part R.quiet = 1) : IsUnit x := by
  let y := connected x
  have hy : y.part R.quiet = 0 := connected_quiet hx
  have hg : Poly.pass y = x := pass_connected hx
  have hxy : x * Poly.pass (-y) = 1 := by
    rw [← hg, ← pass_add hy (by simp [hy]), add_neg_cancel, pass_zero]
  exact ⟨⟨x, Poly.pass (-y), hxy, (mul_comm ..).trans hxy⟩, rfl⟩

/-- `logTable x` is the Taylor rule for `log(x)`, including the vacuum
subtraction. Only for constant coefficient `1`. -/
def logTable (x : Poly R) : Poly R :=
  ∑ j∈range (Fintype.card ι), (((-1 : ℂ)^j)/(j+1 : ℂ)) • (x-1)^(j+1)

theorem euler_logTable_point (x : Poly R) (i : ι) :
    euler i (logTable x) = ∑ j∈range (Fintype.card ι), (1-x)^j * euler i x := by
  rw [logTable,map_sum]
  simp_rw [map_smul,euler_pow]
  apply sum_congr rfl
  intro j _
  have ht : (j+1:ℂ) ≠ 0 := by exact_mod_cast (by omega : (j+1:ℕ) ≠ 0)
  rw [smul_smul,div_mul_cancel₀ _ ht,map_sub,euler_one,sub_zero, ← smul_mul_assoc,
    ← smul_pow, show (-1:ℂ) • (x-1) = 1-x by simp]

theorem euler_logTable {x : Poly R} (hx : x.part R.quiet = 1) (i : ι) :
    x * euler i (logTable x) = euler i x := by
  let y := 1-x
  have hy : y.part R.quiet = 0 := by simp [y,Extra.Trajectories.part_sub,hx]
  let d := euler i x
  suffices x * euler i (logTable x) = d - y^(Fintype.card ι) * d by
    rw [this, Multi.final_vanish y d hy (quiet_euler ..),sub_zero]
  let n := Fintype.card ι
  rw [euler_logTable_point, ← sum_mul, ← mul_assoc]
  change (x * ∑ j∈range n, y^j) * d = _
  rw [show x=1-y from by simp [y], mul_comm (1-y), geom_sum_mul_neg y n,sub_mul,one_mul]

theorem quiet_logTable {x : Poly R} (hx : x.part R.quiet = 1) :
    (logTable x).part R.quiet = 0 := by
  rw [logTable,Poly.part_sum]; refine sum_eq_zero fun k _ => ?_
  rw [Poly.part_smul,pow_succ,Poly.quiet_mul, Extra.Trajectories.part_sub,hx,Poly.one_part,if_pos rfl]
  simp only [sub_self,mul_zero]

/-- The exact table algorithm of `connected` agrees with log Taylor
(in particular we can use either algorithm also on physical inputs). -/
theorem connected_eq_logTable {x : Poly R} (hx : x.part R.quiet = 1) :
    connected x = logTable x := by
  refine ext_euler ((connected_quiet hx).trans (quiet_logTable hx).symm) fun i => ?_
  exact (unit_of_quiet_one hx).mul_right_inj.mp ((euler_connected hx i).symm.trans (euler_logTable hx i).symm)

/-- Disconnected background factors must already be unit normalized. -/
theorem connected_mul {x y : Poly R} (hx : x.part R.quiet = 1) (hy : y.part R.quiet = 1) :
    connected (x*y) = connected x + connected y := by
  refine pass_inj (connected_quiet (by simp only [Poly.quiet_mul,hx,hy,mul_one])) ?_ ?_
  · simp only [Poly.part_plus, connected_quiet hx, connected_quiet hy, add_zero]
  rw [pass_connected (by simp only [Poly.quiet_mul,hx,hy,mul_one]),
    pass_add (connected_quiet hx) (connected_quiet hy), pass_connected hx,pass_connected hy]

/-- Radial rescaling includes any physical power per slot (in particular
fiber/cell powers, even zeros for excluded markers). No condition on
permitted co-occurrence. -/
theorem dilation_connected {x : Poly R} (a : ι → ℂ) (hx : x.part R.quiet = 1) :
    connected (Multi.dilation R a x) = Multi.dilation R a (connected x) := by
  have he (p : Poly R) : (Multi.dilation R a p).part R.quiet = p.part R.quiet := by
    rw [Multi.dilation_part]; simp [Census.quiet]
  apply pass_inj
  · exact connected_quiet ((he x).trans hx)
  · exact (he (connected x)).trans (connected_quiet hx)
  rw [pass_connected ((he x).trans hx), ← Multi.pass_map (Multi.dilation R a) _
    (connected_quiet hx) ((he (connected x)).trans (connected_quiet hx)),pass_connected hx]
end ExpLog
end YM.RG02.Marks
