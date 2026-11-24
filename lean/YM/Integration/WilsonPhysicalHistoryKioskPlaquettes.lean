import YM.Push.ABSOLUTE_SUMS.Animals
import YM.OPE.Therm.Bath
import YM.Work.E01

/-! The plaquettes capable of flagging the genuine occupied source collar
form a single enlarged microscopic ball, uniformly in the torus side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskPlaquettes
open Finset Lattice Wilson RG OPE.Therm Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {n : Side}

def faces (H : ℕ) (x : Site n) : Finset (Face (Per n)) :=
  neighbors (H+H+2) x ×ˢ (Finset.univ : Finset PlaqAxes)

theorem count (H : ℕ) (x : Site n) :
    (faces H x).card ≤ 625*ballCost H*Fintype.card PlaqAxes := by
  rw [faces,Finset.card_product,Finset.card_univ]
  apply Nat.mul_le_mul_right
  refine (neighbors_card (H+H+2) x).trans ?_
  dsimp only [ballCost]
  calc
    _ ≤ (5*(H+H+1))^4 := Nat.pow_le_pow_left (by omega) 4
    _ = _ := by ring

theorem healthy {G : Gauge} {θ : ℝ} (H : ℕ) (x : Site n) (U : Config G n)
    (clean : U∈House.chilly (faces H x) θ) : Healthy θ (neighbors (H+H) x) U := by
  apply Finset.disjoint_left.mpr
  intro z hz alarm
  obtain ⟨p,visit,failed⟩ := (flags_spec _ _ _).mp alarm
  have corner : separation p.1 z≤2 := by
    change z∈(visits p.1 (square p.2.val.1 p.2.val.2)).toFinset at visit
    rw [List.mem_toFinset,square_corners] at visit
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visit
    rcases visit with rfl|rfl|rfl|rfl|rfl
    · simp
    · exact (Work.E01.sep_step_le ..).trans (by decide)
    · exact (separation_triangle _ (p.1+step p.2.val.1) _).trans
        (Nat.add_le_add (Work.E01.sep_step_le ..) (Work.E01.sep_step_le ..))
    · exact (Work.E01.sep_step_le ..).trans (by decide)
    · simp
  have near : separation x p.1 ≤ H+H+2 := by
    apply (separation_triangle x z p.1).trans
    exact Nat.add_le_add ((neighbors_mem _ _ _).mp hz) ((separation_comm z p.1).symm ▸ corner)
  exact (not_lt_of_ge (clean p (Finset.mem_product.mpr
    ⟨(neighbors_mem _ _ _).mpr near,Finset.mem_univ _⟩))) failed

end YM.Integration.WilsonPhysicalHistoryKioskPlaquettes
end
