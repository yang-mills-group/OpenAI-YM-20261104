import YM.XSpace.Carnation

/-! The first coefficient of the signed seven-face position detector for arbitrary
incoming fields. Each monomial in the connected expression uses each of the
three occupied slots exactly once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerInteracting
open Function Set Filter Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose
open XSpace.Cirrus XSpace.Photo PowerSeries
open scoped Topology BigOperators Classical

variable {G : Gauge}

/-- Differentiate the three-point connected expression, before removing its regulator. -/
def first (v w : Badge → ℂ) : ℂ :=
  w Finset.univ -
    (w {0,1}*v {2} + v {0,1}*w {2} +
     (w {0,2}*v {1} + v {0,2}*w {1}) +
     (w {1,2}*v {0} + v {1,2}*w {0})) +
    2*(w {0}*v {1}*v {2} + v {0}*w {1}*v {2} + v {0}*v {1}*w {2})

theorem coefficient (f : Badge → PS) :
    coeff 1 (b3 f) = first (fun s => coeff 0 (f s)) (fun s => coeff 1 (f s)) := by
  simp only [b3, first, map_sub, map_add, two_smul, coeff_one_mul,
    coeff_zero_eq_constantCoeff_apply, map_mul]
  ring

def face (v : Point G 6 3) (p : Tags G 6 3) (s : Badge) : ℂ := v (missing p s)

private theorem placed (v : Point G 6 3) (p : Tags G 6 3) (i : Fin 3)
    (x : Sec G 6) (s : Badge) :
    face v (Function.update p i x) s =
      if i∈s then v.toLinearMap (missing p s) i x else face v p s := by
  by_cases h : i∈s
  · rw [if_pos h]; unfold face
    change v _ = v (Function.update (missing p s) i x)
    congr 1; funext k
    by_cases e : k=i
    · subst k; simp [missing,h]
    · by_cases h' : k∈s <;> simp [missing,Function.update_of_ne e,h']
  · rw [if_neg h]; unfold face; congr 1; funext k
    by_cases e : k=i
    · subst k; simp [missing,h]
    · by_cases h' : k∈s <;> simp [missing,Function.update_of_ne e,h']

/-- Both the actual regulated and continuum first coefficient are linear in every
occupied input, including the three products of singleton readings. -/
def row (v w : Point G 6 3) : Point G 6 3 := MultilinearMap.mk'
  (fun p => first (face v p) (face w p))
  (fun p i x y => by fin_cases i <;> simp [first, placed, map_add] <;> ring)
  (fun p i a x => by fin_cases i <;> simp [first, placed, map_smul, smul_eq_mul] <;> ring)

theorem read (v w : Point G 6 3) (p : Tags G 6 3) :
    row v w p = first (face v p) (face w p) := rfl

end YM.Integration.WilsonMaxwellThermometerInteracting
end
