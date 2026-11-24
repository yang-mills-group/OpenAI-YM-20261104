import YM.Comparison.Stencils.Feed

/-!
# Power counting for the log-to-radial-variables projection

Slots are factored in the basis of commuting polynomial coordinates,
not inferred from the field's name. In particular raw projection doesn't
decrease slot rank; it can (and is allowed to) increase it. At unchanged
rank the projection is purely the linear link substitution with physical
orientation and normalization; no stencil artifacts discarded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Feed
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter
open Planned.PrimaryIntegral295.Place (Spot Dev slant placeEdge pore pore_site polynomial_smooth plog_velocity)
open Next.Foundations
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {d : ℕ} {S : Finset Cover}

section Grades
variable (P : Pol G)

lemma cap_portion (d i : ℕ) : capRead d (portion i P) = portion i (capRead d P) := by
  apply MvPolynomial.ext; intro m
  rw [coeff_capRead, portion_coeff, portion_coeff, coeff_capRead]
  split <;> split <;> rfl

lemma slots_le (h : P ∈ limited G d) : ∀ i ∈ P.support, slots i ≤ d := by
  intro i hi
  have he := Labels.power_le i
  rw [Labels.weight_slot] at he
  exact he.trans ((MvPolynomial.mem_restrictSupport_iff ℂ).mp (show P∈limited G d from h) hi)

lemma slots_past (h : P ∈ limited G d) {k : ℕ} (hk : d < k) : portion k P = 0 := by
  apply MvPolynomial.ext; intro m
  rw [portion_coeff]
  by_cases he : m ∈ P.support
  · rw [if_neg ((slots_le P h _ he|>.trans_lt hk).ne), MvPolynomial.coeff_zero]
  · simp [MvPolynomial.notMem_support_iff.mp he]

lemma slots_full (h : P ∈ limited G d) : ∑ l ∈ Finset.range (d+1), portion l P = P := by
  apply MvPolynomial.ext; intro i
  simp_rw [MvPolynomial.coeff_sum, portion_coeff]
  by_cases hi : i ∈ P.support
  · have he := slots_le P h _ hi
    simp [he]
  simp [MvPolynomial.notMem_support_iff.mp hi]
end Grades

lemma portion_letter (H : Hol G) (d : ℕ) (P : LocalPol G S) (k : ℕ) (hk : k ≤ d) :
    portion k (projector H d P) = capRead d (letter H d P k) := by
  change portion k (capRead d _) = _
  rw [← cap_portion, polynomial, map_sum]
  apply congrArg (capRead d)
  have he (j : ℕ) : portion k (letter H d P j) = if k=j then letter H d P j else 0 :=
    on_rank (letter H d P j) j (band_degree ..) k
  simp_rw [he]; simp [hk]

lemma rule_tangent (H : Hol G) (d : ℕ) (i : Var G S) (V : Snap G d) :
    HasDerivAt (fun t : ℝ => coordinate i (rule S H d (t • V)))
      (access V (placeEdge i.1) i.2) 0 := by
  let B := placeEdge i.1
  let F := fun t : ℝ => G.mat (H.links d (expand d (t • V)) 1 B)
  have hh := Work.G02.linkGerm H d B
  have he : HasDerivAt F (G.colorMat (access V B)) 0 := hh.2.2 V
  have hF : F 0 = 1 := by simp only [F, zero_smul, hh.2.1, G.mat_one]
  have hz := ((G.plog_diff.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt_of_eq 0 he hF.symm
  have hx := hz.congr_deriv (plog_velocity (access V B))
  let L : G.Color →L[ℝ] ℝ := EuclideanSpace.proj i.2
  exact L.hasFDerivAt.comp_hasDerivAt 0 hx

/-- Remove a slot's one factor of X *before* composing with polynomials. -/
def ruleTape (H : Hol G) (d : ℕ) (i : Var G S) (J : Jet G) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => term (n+1) (fun r : ℝ =>
    (↑(coordinate i (rule S H d (r • trunk d J))) : ℂ)))

@[simp] lemma tape_start (H : Hol G) (d : ℕ) (i : Var G S) (J : Jet G) :
    PowerSeries.constantCoeff (ruleTape H d i J) =
      (↑(coordinate i (Symbols.patch S (access (trunk d J)))) : ℂ) := by
  let f : ℝ → ℝ := fun r => coordinate i (rule S H d (r • trunk d J))
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, ruleTape, PowerSeries.coeff_mk]
  change term 1 (fun t => Complex.ofRealCLM (f t)) = _
  rw [term_one]; exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (rule_tangent H d i (trunk d J))).deriv

lemma tape_correct (H : Hol G) (d : ℕ) (i : Var G S) (J : Jet G) :
    recording (fun r : ℝ => (↑(coordinate i (rule S H d (r • trunk d J))) : ℂ)) =
      PowerSeries.X * ruleTape H d i J := by
  ext1 n
  cases n with
  | zero => rw [recorded, term_zero]; simp [rule_zero]
  | succ n => rw [recorded, PowerSeries.coeff_succ_X_mul, ruleTape, PowerSeries.coeff_mk]

lemma letter_substitute (H : Hol G) (d : ℕ) (J : Jet G) {P : LocalPol G S}
    {k : ℕ} (h : Rank P k) :
    recording (fun t => reading H d P (t • trunk d J)) = PowerSeries.X ^ k *
      MvPolynomial.eval₂Hom PowerSeries.C (fun i => ruleTape H d i J) P := by
  let u (i : Var G S) (r : ℝ) : ℂ := coordinate i (rule S H d (r • trunk d J))
  have hu (i : Var G S) : ContDiffAt ℝ ω (u i) 0 := by
    have he : ContDiffAt ℝ ω (fun r : ℝ => rule S H d (r • trunk d J)) 0 :=
      (show ContDiffAt ℝ ω (rule S H d) ((0:ℝ) • trunk d J) by rw [zero_smul]; exact rule_diff S H d).comp
        (f := fun r : ℝ => r • trunk d J) 0 (contDiffAt_id.smul contDiffAt_const)
    exact (Complex.ofRealCLM.contDiff.comp (coordinate i).contDiff).contDiffAt.comp 0 he
  change recording (fun t => MvPolynomial.eval (fun i => u i t) P) = _
  have hp := (rank_slot P k).mp h
  rw [recording_pol P hu]; simp_rw [u, tape_correct]
  rw [undress_exact (fun a ha => (hp a ha).ge), undress_pure hp]

lemma letter_low (H : Hol G) (d : ℕ) {P : LocalPol G S} {k m : ℕ} (h : Rank P k) (hm : m < k) :
    letter H d P m = 0 := by
  refine Labels.eval_ext _ _ fun J => ?_
  rw [radial_amplitude, map_zero, ← recorded, letter_substitute H d J h,
    PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr hm)]

lemma projection_rank (H : Hol G) (d : ℕ) {P : LocalPol G S} {k m : ℕ} (h : Rank P k) (hm : m < k) :
    portion m (projector H d P) = 0 := by
  by_cases he : m ≤ d
  · rw [portion_letter H d P m he, letter_low H d h hm]; simp [capRead]
  exact slots_past (projector H d P) (raw_cap ..) (Nat.lt_of_not_ge he)

lemma projection_zero (H : Hol G) (d : ℕ) {P : LocalPol G S} {k : ℕ} (h : Rank P k) (hk : d < k) :
    projector H d P = 0 := by
  rw [← slots_full (projector H d P) (raw_cap H d P)]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact projection_rank H d h ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans_lt hk)

/-- Before engineering truncation, linear tests are literally link integration,
with one real jet tested on all links, independent of path choices and the
symbol representation. -/
theorem letter_diagonal (H : Hol G) (d : ℕ) {P : LocalPol G S} {k : ℕ} (h : Rank P k)
    (J : Jet G) :
    Labels.read J (letter H d P k) = inscribe (Symbols.patch S (access (trunk d J))) P := by
  rw [radial_amplitude, ← recorded, letter_substitute H d J h,
    PowerSeries.coeff_X_pow_mul', if_pos (show k ≤ k from le_rfl), Nat.sub_self]
  -- evaluate the power series hom at X=0
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  clear h
  induction P using MvPolynomial.induction_on with
  | C a => simp [inscribe]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.eval₂Hom_X']
    rw [tape_start]; simp [inscribe]

/-- Same slot count projection through the specified engineering horizon. -/
theorem reads_diagonal (H : Hol G) (d : ℕ) {P : LocalPol G S} {k : ℕ} (h : Rank P k)
    (hk : k ≤ d) (J : Jet G) {s : ℕ} (hs : s ≤ d) :
    iteratedDeriv s (fun t => Labels.read (scaleJet J t) (portion k (projector H d P))) 0 =
      iteratedDeriv s (fun t : ℝ => inscribe (Symbols.patch S (access (trail J d t))) P) 0 := by
  rw [portion_letter H d P k hk, deriv_read, tier_capRead d _ _ hs, ← deriv_read]
  have he t := letter_diagonal H d h (scaleJet J t)
  rw [funext he]; rfl
end YM.Comparison.Stencils.Feed
