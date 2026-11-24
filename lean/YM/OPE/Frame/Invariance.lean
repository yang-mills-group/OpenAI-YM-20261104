import YM.OPE.Frame.Reading
/-!
# One equivariant splitting measured by compact fixed detector orbits

Instead of increasing detector stages in the errors through a row, the
readout of a row will use that row's own fixed projection. Get coherence
by choosing the invariant filtration splitting *as well*, using all the
lower-stage readouts to pick an invariant complement with the exact
biorthogonality on each higher field space.
-/
set_option autoImplicit false
noncomputable section

open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector Splitting)
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S} {X : Rotation S} {a d m k : ℕ}
    (H : S.Hierarchy) (hX : X.Laws P H.spin)
    (A : ∀ d : ℕ, Detector S d)
    (hp : P.Inclusions S) (ho : X.Oriented S) (hP : P.Orientation H.spin)

private def tape : ∀ d m, S.Field m →ₗ[ℂ] S.Field d
 | 0,m => notch H hX (A 0) m
 | d+1,m => let N := notch H hX (A (d+1)) m
            N + ((P.rise (Nat.le_succ d)).comp (tape d m - (tape d (d+1)).comp N))

private lemma tape_step (v : S.Field m) : tape H hX A (d+1) m v =
    notch H hX (A (d+1)) m v + P.rise (Nat.le_succ d) (tape H hX A d m v - tape H hX A d (d+1) (notch H hX (A (d+1)) m v)) := by rw [tape]; rfl
include hp
private lemma tape_fresh (e : m ≤ a) (v : S.Field m) : tape H hX A d a (P.rise e v) = tape H hX A d m v := by
  induction d with
  | zero => exact notch_rises H hX (A 0) hp e v
  | succ d ih => rw [tape_step,tape_step, notch_rises H hX (A (d+1)) hp e v, ih]
include ho
omit hp in
private lemma tape_fits (v : S.Field d) : tape H hX A d d v = v := by
  cases d with
  | zero => exact notch_complete H hX ho (A 0) v
  | succ d => rw [tape_step,notch_complete H hX ho,sub_self,map_zero,add_zero]

def splitMeasured : Splitting P where
  down d := tape H hX A d (d+1)
  left d x := (tape_fresh H hX A hp (d := d) _ x).trans (tape_fits H hX A ho x)

include hP
lemma splitCovariant : (splitMeasured H hX A hp ho).Covariant X H.spin := by
  have he (d k) (v : S.Field k) : tape H hX A d k (S.conj H.spin _ v) = S.conj H.spin _ (tape H hX A d k v) := by
    induction d generalizing k with
    | zero => exact notch_real H hX (A 0) v
    | succ d ih => rw [tape_step,tape_step,map_add,hP.realInc,map_sub,notch_real,ih,ih]; simp only [map_sub]
  have hf (d k) (K : Ortho) (v : S.Field k) : tape H hX A d k (X.act k K v) = X.act d K (tape H hX A d k v) := by
    induction d generalizing k with
    | zero => exact notch_act H hX ho (A 0) v K
    | succ d ih => rw [tape_step,tape_step,map_add,hX.filtered,map_sub,notch_act H hX ho,ih,ih]; simp only [map_sub]
  exact ⟨fun d v => (he ..).symm, fun d K v => (hf d (d+1) K v).symm⟩
omit hP
private lemma tape_lowers (v : S.Field a) : (splitMeasured H hX A hp ho).down d (tape H hX A (d+1) a v) = tape H hX A d a v := by
  rw [tape_step, map_add, (splitMeasured H hX A hp ho).left]; exact add_sub_cancel .. -- ? orientation
private lemma part_tape {m k : ℕ} (hm : m ≤ k) (v : S.Field a) :
    let B := splitMeasured H hX A hp ho; B.part m k (tape H hX A k a v) = B.part m m (notch H hX (A m) a v) := by
  intro B
  induction k,hm using Nat.le_induction with
  | base =>
    rw [B.top_part]; cases m with
    | zero => rw [tape]
    | succ i => rw [tape_step,map_add]; simp [Splitting.top, B.left]
  | succ k he ih =>
    rw [Splitting.part,dif_neg (by omega), LinearMap.comp_apply]; exact (congrArg _ (tape_lowers H hX A hp ho v)).trans ih

/-- Coherence identity. Readouts `notch w` through their exact-grade row are compatible
without any demand parameter. -/
lemma coherent_row (v : S.Field m) :
    let B := splitMeasured H hX A hp ho; B.part d d (notch H hX (A d) m v) = B.part d m v := by
  intro B; rcases le_total d m with hl|hl
  · rw [← part_tape H hX A hp ho hl,tape_fits H hX A ho]
  rw [← notch_rises H hX (A d) hp hl, notch_complete H hX ho, B.part_rise H.laws.toSymmetric hp]
end YM.OPE.Frame
