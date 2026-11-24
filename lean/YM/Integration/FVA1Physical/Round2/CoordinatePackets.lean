import YM.Integration.FVA1Physical.Round2.RectangleLedger

/-! A finite-order anchored decomposition of the whole field increment.
Stop at exactly the requested number of selected coordinates and evaluate that
mixed difference on the remaining actual background. Terms of lower arity
are evaluated with the untouched coordinates held at their initial value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped BigOperators Classical
variable {σ : Type}

def coordinateWalk (h : σ→ℝ) (L : List σ) : Positions σ :=
  (L.map (fun i=>h i • bolt i)).sum

def coordinatePackets : ℕ → List σ → List (List σ × List σ)
  | 0, L => [([],L)]
  | _+1, [] => [([],[])]
  | q+1, i::L => coordinatePackets (q+1) L ++
      (coordinatePackets q L).map (fun p=>(i::p.1,p.2))

private theorem rectangle_add_point (h : σ→ℝ) (L : List σ) (F : Positions σ→ℝ) (x v : Positions σ) :
    rectangle h L (fun y=>F (y+v)) x = rectangle h L F (x+v) := by
  induction L generalizing x with
  | nil => rfl
  | cons i l ih => simp only [rectangle,ih]; rw [add_right_comm x]

private theorem rectangle_sub_maps (h : σ→ℝ) (L : List σ) (F H : Positions σ→ℝ) (x : Positions σ) :
    rectangle h L (fun y=>F y-H y) x = rectangle h L F x - rectangle h L H x := by
  induction L generalizing x with
  | nil => rfl
  | cons i l ih => simp only [rectangle,ih]; abel

/-- No conditional expectations or reconstruction hypotheses are used: the sum
is exactly the original function at the fully changed field. -/
theorem coordinate_packets_exact (q : ℕ) (h : σ→ℝ) (L : List σ) (F : Positions σ→ℝ) (x : Positions σ) :
    ((coordinatePackets q L).map (fun p=>rectangle h p.1 F (x+coordinateWalk h p.2))).sum =
      F (x+coordinateWalk h L) := by
  induction L generalizing q F with
  | nil => cases q <;> simp [coordinatePackets,rectangle,coordinateWalk]
  | cons i l ih =>
    cases q with
    | zero => simp [coordinatePackets,rectangle]
    | succ q =>
      let D := fun y=>F (y+h i • bolt i)-F y
      have term (p : List σ × List σ) :
          rectangle h (i::p.1) F (x+coordinateWalk h p.2) =
            rectangle h p.1 D (x+coordinateWalk h p.2) := by
        unfold D
        rw [rectangle,rectangle_sub_maps,rectangle_add_point]
      rw [coordinatePackets,List.map_append,List.sum_append,List.map_map,ih]
      change _ + ((coordinatePackets q l).map (fun p=>rectangle h (i::p.1) F (x+coordinateWalk h p.2))).sum = _
      simp_rw [term]
      rw [ih]
      simp only [D,coordinateWalk,List.map_cons,List.sum_cons]
      rw [add_comm _ (_ - _),sub_add_cancel]
      congr 1
      abel

theorem coordinate_packet_shape (q : ℕ) (L : List σ) (p : List σ × List σ)
    (hp : p∈coordinatePackets q L) : p.1.length≤q ∧
      (p.1.length<q → p.2=[]) ∧ (p.1++p.2).Sublist L := by
  induction L generalizing q p with
  | nil =>
    cases q <;> simp only [coordinatePackets,List.mem_singleton] at hp <;> subst p <;> simp
  | cons i L ih =>
    cases q with
    | zero => simp only [coordinatePackets,List.mem_singleton] at hp; subst p; simp
    | succ q =>
      rw [coordinatePackets,List.mem_append,List.mem_map] at hp
      rcases hp with no | ⟨p',yes,eq⟩
      · obtain ⟨len,z,sub⟩ := ih _ _ no
        exact ⟨len,z,sub.cons _⟩
      · subst p
        obtain ⟨len,z,sub⟩ := ih q p' yes
        exact ⟨Nat.succ_le_succ len,fun H=>z (Nat.lt_of_succ_lt_succ H),sub.cons_cons i⟩

end YM.Integration.FVA1Physical.Round2
