import YM.FormalOPE.RG10.Selected

/-!
# Connected-to-ordinary report, with coupling degrees and inclusion coherence

The usual moment-log with output-to-log convention: connected mark reports do NOT include a
vacuum log. A temporary operation `logWord` also works on inputs before restoring that unit:
as long as `boot = 1`, it discards pure constant and uses the combined *positive* grades
(coupling OR nonempty markers). All operations are coefficientwise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Filter Finset Polar
open scoped BigOperators

variable {V I : Type} [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    {R : Census V} {S : Census I}

namespace PolyUtil
/-- All marker subsets allowed. Still finite. -/
def freely (I : Type) [Fintype I] [DecidableEq I] : Census I where
  choices := Finset.univ
  blank := mem_univ _
  solo _ := mem_univ _
  down _ _ _ := mem_univ _

lemma connected_one : connected (1 : Poly R) = 0 := by
  apply pass_inj (connected_quiet (by simp)) rfl
  rw [pass_connected (by simp), pass_zero]

lemma conn_mul {A B : Poly R} (hA : A.part R.quiet=1) (hB : B.part R.quiet=1) :
    connected (A * B) = connected A + connected B := by
  have h : (A * B).part R.quiet = 1 := by simp [hA,hB]
  apply pass_inj (connected_quiet h) (by simp [connected_quiet hA, connected_quiet hB]);
  rw [pass_add (connected_quiet hA) (connected_quiet hB), pass_connected hA, pass_connected hB,
    pass_connected h]

lemma conn_pass (A : Poly R) (hA : A.part R.quiet=0) : connected (Poly.pass A) = A :=
  pass_inj (connected_quiet (Poly.pass_part A hA)) hA (pass_connected (Poly.pass_part A hA))

lemma conn_map (f : Poly R →ₐ[ℂ] Poly S) (h : ∀ A, (f A).part S.quiet = A.part R.quiet)
    (A : Poly R) (hA : A.part R.quiet=1) : f (connected A) = connected (f A) := by
  have hB := connected_quiet hA
  have hy : (f A).part S.quiet=1 := (h A).trans hA
  have hC := (h (connected A)).trans hB
  apply pass_inj hC (connected_quiet hy)
  rw [← YM.Multi.pass_map f (connected A) hB hC, pass_connected hy, pass_connected hA]
end PolyUtil

namespace Word

/-- Evaluate ONLY the series degree zero unmarked value. -/
def boot (A : Word R) : ℂ := coeff 0 (vac R A)
omit [Fintype V] in
lemma boot_mul (A B : Word R) : boot (A*B) = boot A * boot B := by
  unfold boot; rw [map_mul]; simp [coeff_mul]

omit [Fintype V] [Fintype I] in
lemma boot_restrict (f : Names R S) (A : Word S) : boot (eraseMarks f A) = boot A := by
  unfold boot; rw [vac_eq, see_eraseMarks, f.quiet, ← vac_eq]

/-- Divide out τ multiplicity to convert the `connected` Poly back to Taylor coefficients.
Allows a positive-coupling vacuum grade. The output-to-log of a normalized MarkedSeries will
have **all** empty-subset coefficients zero. -/
def logWord (A : Word R) : Word R := PowerSeries.mk fun k => Poly.inject fun s : R.Mode =>
  ((k.factorial:ℂ))⁻¹ * (connected (certify (Fin k) A)).part (pay s (univ (α:=Fin k)))

lemma log_grade (A : Word R) (s : R.Mode) (k : ℕ) :
    (PowerSeries.coeff k (logWord A)).part s =
      ((k.factorial:ℂ))⁻¹ * (connected (certify (Fin k) A)).part (pay s (univ (α:=Fin k))) := by
  rw [logWord, PowerSeries.coeff_mk]; rfl

/-- Coherence of the connected logarithm: from any finite order via the same marker ring.
Merges, supports, forbidden choices, common tags exactly retained in use. -/
lemma consistent (A : Word R) (h : boot A = 1) :
    certify I (logWord A) = connected (certify I A) := by
  ext s; rw [← pay_sep s]
  generalize mark s = a
  generalize tickets s = t
  have hu : (certify I A).part (budget R I).quiet=1 := (present_quiet A).trans h
  obtain ⟨e,he⟩:= issues t
  let u := nominate (remain R) e
  have hw := u.connected_restrict hu
  rw [show u.restriction (certify I A) = _ from Polar.pay_more e A] at hw
  have hs := congr_arg (fun z => Poly.part z (pay a (univ (α:=Fin t.card)))) hw
  change (connected (certify I A)).part ((nominate _ e).share _) = _ at hs
  rw [share_pay, supports, he] at hs
  rw [hs, certify_present (I:=I)]; rw [present_pay, log_grade]; field_simp [Nat.factorial_ne_zero]

@[simp] lemma log_one : logWord (1 : Word R) = 0 := by
  apply detects; intro k; rw [consistent, map_one, PolyUtil.connected_one, map_zero]
  rw [boot, map_one]; simp

lemma restrict_log (A : Word S) (h : boot A = 1) (f : Names R S) :
    eraseMarks f (logWord A) = logWord (eraseMarks f A) := by
  apply detects; intro k
  let E : Fin k ↪ Fin k := Function.Embedding.refl _
  rw [consistent _ (by rw [boot_restrict,h]), ← pays_compatibly f E, ← pays_compatibly f E,
    consistent A h, Names.connected_restrict]; exact (present_quiet A).trans h

omit [Fintype V] in
private def nothing (R : Census V) : Names (PolyUtil.freely Empty) R where
  e := Function.Embedding.ofIsEmpty
  visible s := by rw [show s.val = ∅ from Finset.eq_empty_of_isEmpty _, Finset.image_empty]; exact R.blank

lemma vac_log (A : Word R) (h : vac R A = 1) : vac R (logWord A) = 0 := by
  let u := nothing R
  have he : eraseMarks u A = 1 := by
    apply observe_ext; intro s
    rw [show s=(PolyUtil.freely Empty).quiet from Subtype.ext (Finset.eq_empty_of_isEmpty _),
      see_eraseMarks, Names.quiet, ← vac_eq, ← vac_eq, h, map_one]
  rw [vac_eq, ← Names.quiet u, ← see_eraseMarks, restrict_log _ (by unfold boot; rw [h]; simp),
    he, log_one, see_zero]

lemma boot_conn (A : Word R) (h : boot A = 1) : boot (logWord A)=0 := by
  rw [boot, ← present_quiet (I:=Fin 0)]
  rw [← certify_present, consistent A h]; exact connected_quiet ((present_quiet A).trans h)

lemma log_mul (A B : Word R) (hA : boot A = 1) (hB : boot B = 1) :
    logWord (A*B) = logWord A + logWord B := by
  apply detects; intro k
  rw [map_add, consistent _ (by rw [boot_mul,hA,hB]; simp), consistent _ hA, consistent _ hB, map_mul]
  exact PolyUtil.conn_mul (show (certify _ A).part _ = 1 from (present_quiet (I:=Fin k) _).trans hA) (show (certify _ B).part _ = 1 from (present_quiet (I:=Fin k) _).trans hB)

/-- On sources with NO empty-subset column at any order. Taylor exp in the MarkedSeries nilpotent
ideal only. Uniform nilpotence even before truncating the coupling order. -/
def expMark (A : Word R) : Word R :=
  ∑ i ∈ range (Fintype.card V + 1), (i.factorial:ℂ)⁻¹ • A^i

lemma models (A : Word R) (h : vac R A = 0) :
    certify I (expMark A) = Poly.pass (certify I A) := by
  rw [expMark, map_sum]; simp_rw [map_smul, map_pow]
  unfold Poly.pass
  have ht : Fintype.card V ≤ Fintype.card (V ⊕ I) := by simp
  refine Finset.sum_subset (range_mono (by omega)) (fun j hj hv => ?_)
  rw [← map_pow, marker_nil h ?_, map_zero, smul_zero]
  simp only [Finset.mem_range, not_lt] at hv; omega

/-- Ordinary from connected. -/
lemma exp_log (A : Word R) (h : vac R A = 1) : expMark (logWord A) = A := by
  have he : boot A=1 := by unfold boot; rw [h]; simp
  apply detects; intro k
  rw [models _ (vac_log A h), consistent _ he]
  exact pass_connected (show (certify _ A).part _ = 1 from (present_quiet (I:=Fin k) _).trans he)

lemma vac_exp (A : Word R) (h : vac R A=0) : vac R (expMark A)=1 := by
  unfold expMark
  simp_rw [map_sum,map_smul,map_pow,h]
  rw [Finset.sum_eq_single 0] <;> simp 
  intros; omega

lemma log_exp (A : Word R) (h : vac R A = 0) : logWord (expMark A) = A := by
  have he : boot (expMark A)=1 := by unfold boot; rw [vac_exp _ h]; simp
  apply detects; intro k
  rw [consistent _ he, models _ h]; apply PolyUtil.conn_pass
  exact (present_quiet _).trans (by rw [h]; simp)

lemma exp_add (A B : Word R) (h : vac R A=0) (k : vac R B=0) :
    expMark (A+B) = expMark A * expMark B := by
  apply detects; intro n
  rw [models (A+B) (by rw [map_add,h,k,zero_add]), map_mul, models A h, models B k,
    map_add]; apply pass_add
  · exact ((present_quiet A).trans (by rw [h]; simp))
  exact ((present_quiet B).trans (by rw [k]; simp))

end Word
end YM.FormalOPE.RG10
