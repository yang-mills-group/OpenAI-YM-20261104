import YM.Integration.WilsonPhysicalHistoryGroupedEligibility
import YM.Integration.WilsonPhysicalHistoryGroupedHealthy
import YM.RG3.Script.Reserve

/-! The regular and forced mixed components of a single entered gallery
satisfy the original turning-date input conditions on its actual mask. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryCorrectionCarton
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] [Fintype V] {Z : Census V}
  {G : Gauge} {n : Side} {P : Rep G n} {o : V → Site n} (A : Gallery T I o P Z)

def regularRows : Set I := {i | ¬ A.E.clear i ∧ 2 ≤ (A.E.mode i).val.card}

def regular (t : T) := WilsonPhysicalHistoryGroupedLamps.grouped A.E (regularRows A) t

def forced (t : T) := WilsonPhysicalHistoryGroupedHard.grouped P o A.K
  (Finset.univ.filter (fun s : Z.Mode => 2 ≤ s.val.card)) t

omit [Fintype V] in
private theorem lower {X Y : Type*} (shape : X → Support n) (f : X → Y → Poly Z) (w : V → ℝ)
    (positive : ∀ v, 0 < w v) {B : ℕ} {a b h : ℝ} (less : b ≤ a)
    (paid : Towed w shape f B a h) : Towed w shape f B b h := by
  obtain ⟨fee, total, rent, fields⟩ := paid
  exact ⟨fee, total, RG3.Script.Reserve.hit_down rent (fun x => (Loci.fares (fields x) positive).1) less, fields⟩

variable [Countable I] (w : V → ℝ) (pos : ∀ v, 0 < w v)
include pos in
theorem original {a q h : ℝ} (expo : 0 ≤ a) (regularPaid : A.E.Paid w P.p.B (a+2) q)
    (hardPaid : A.K.Paid w P.p.B a h) (t : T) :
    Carton o (regular A t) (forced A t) P.p.threshold ∧
    Towed w id (regular A t) P.p.B (a-1) q ∧
    Towed w Prod.fst (forced A t) P.p.B (a-1) h := by
  have more : 0 ≤ a+2 := by linarith
  refine ⟨⟨fun x => ⟨?_,?_⟩, fun x => ⟨?_,?_⟩⟩,?_,?_⟩
  · exact WilsonPhysicalHistoryGroupedHealthy.fields A.E w pos (regularRows A) more regularPaid
      (fun _ eligible => eligible.1) t x
  · exact WilsonPhysicalHistoryGroupedHealthy.mixed A.E w pos (regularRows A) more regularPaid
      (fun _ eligible => eligible.2) t x
  · exact WilsonPhysicalHistoryGroupedEligibility.physical P o A.K w pos _ expo hardPaid t x
  · exact WilsonPhysicalHistoryGroupedEligibility.mixed P o A.K w pos expo hardPaid t x
  · exact lower id (regular A t) w pos (by linarith : a-1 ≤ a+2)
      (WilsonPhysicalHistoryGroupedLamps.original A.E w pos (regularRows A) more regularPaid t)
  · exact lower Prod.fst (forced A t) w pos (by linarith : a-1 ≤ a)
      (WilsonPhysicalHistoryGroupedHard.original P o A.K w pos _ expo hardPaid t)

end YM.Integration.WilsonPhysicalHistoryCorrectionCarton
end

