import YM.FormalOPE.RG10.Reclosure
import YM.FormalOPE.RG10.Linear
import YM.Next.MULTISOURCE.Evaluate

/-!
# Extract the log of formal multi-mark integrations before assigning any supports

Width/locality never assumed on the log. This calculus expresses a representation that can then
be paid recursively by Gaussian costs. Only the nonempty MARK parts are connected after full
denominator computation. Do not send the auxiliary degree markers to the physical comparison as
stochastic choices.
-/

set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10.Joins
open MeasureTheory PowerSeries Finset Marker Extra.Trajectories FlatFeed Word Polar Function
open scoped BigOperators Topology Classical

variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E) (W : Vertices (Θ × E))
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {R : Census V} {S : Census I}


omit [Fintype V] in
lemma cancel (A : Θ × E → Word R) : sing R.quiet (F.den W) * F.close W A = F.columns (totalize W A) := by
  apply observe_ext; intro s
  rw [spike_mul, close_part, step_den, column_eq, totalize_read]

lemma log_unseen {b : Series} (h : PowerSeries.coeff 0 b = 1) {s : R.Mode} (hs : s.val.Nonempty) :
    see s (logWord (sing R.quiet b))=0 := by
  let A := sing R.quiet b
  obtain ⟨i,hi⟩:=hs
  have hv : boot A=1 := by unfold A boot; rw [vac_eq, see_sing, if_pos rfl, h]
  have he : withLeaf i A=0 := by
    refine observe_ext fun u => ?_
    by_cases he : i∈u.val
    · have ht : u≠R.quiet := fun hb => Finset.notMem_empty i (show i∈R.quiet.val from hb ▸ he)
      simp [leaf_pick,he,A,ht]
    simp [he]
  have hw := adjoin i A hv; rw [he] at hw
  have hi' : A * sing R.quiet b⁻¹ = 1 := by
    refine observe_ext fun u => ?_
    rw [spike_mul, see_sing, see_one]; split
    · apply PowerSeries.mul_inv_cancel
      rw [← coeff_zero_eq_constantCoeff, h]; exact one_ne_zero
    apply mul_zero
  have hh : withLeaf i (logWord A)=0:=by
    calc
      _ = withLeaf i (logWord A) * (A * sing R.quiet b⁻¹) := by rw [hi',mul_one]
      _ = _ := by rw [← mul_assoc,← hw,zero_mul]
  rw [← show A = sing R.quiet b from rfl, ← show see s (withLeaf i (logWord A))= _ from leaf_pick i (logWord A) s |>.trans (if_pos hi), hh]; exact see_zero _

lemma before_capture (A : Θ × E → Word R) (h : read R.quiet A = 1) (s : R.Mode) (hs : s.val.Nonempty) :
    see s (F.contraction W A) = see s (logWord (F.columns (totalize W A))) := by
  have ht : boot (sing (R:=R) R.quiet (F.den W))=1:= by unfold boot; simp [den0]
  have he : boot (F.close W A) = 1 := by unfold boot; rw [preserve_one F W h]; simp
  rw [← cancel F W A, log_mul _ _ ht he, see_add, log_unseen (den0 F W) hs,zero_add]; rfl

variable (A : Θ × E → Word R) (h : read R.quiet A = 1)
include h
omit [Fintype V] in
lemma numerator_unit : boot (F.columns (totalize W A))=1:= by
  rw [← cancel F W A, boot_mul]; unfold boot; rw [F.preserve_one W h]; simp [den0]
omit [Fintype Θ] [MeasurableSpace E] [Fintype V] in
lemma weight_and_input (x : Θ × E) : boot (totalize W A x) = 1 := by
  rw [totalize, boot_mul]; unfold boot; rw [show vac R (A x) = 1 from congr_fun h x];
  simp only [coeff_one, ↓reduceIte, vac_eq, see_sing, mul_one]; exact congr_fun W.weight0 x
omit [Fintype Θ] [MeasurableSpace E] in
lemma unit_present (x : Θ × E) :
    (present I (totalize W A x)).part (budget R I).quiet = 1 := (present_quiet _).trans (weight_and_input W A h x)
omit h in
lemma measurement (q : (budget R I).Mode) :
    (present I (F.columns (R:=R) A)).part q = F.mean (fun x => (present I (A x)).part q) := by
  rw [← pay_sep q]; simp_rw [present_pay, ← unfold_see, column_eq, average_coeff]
  exact (mean_smul ..).symm

lemma disbursed (s : R.Mode) (hs : s.val.Nonempty) (k : Finset I) :
    (k.card.factorial:ℂ) * (PowerSeries.coeff k.card (see s (F.contraction W A))) =
    (connected (present I (F.columns (totalize W A)))).part (Polar.pay s k) := by
  rw [before_capture F W A h s hs, unfold_see, ← present_pay, ← certify_present, consistent _ (numerator_unit F W A h)]
  rfl
end YM.FormalOPE.RG10.Joins
