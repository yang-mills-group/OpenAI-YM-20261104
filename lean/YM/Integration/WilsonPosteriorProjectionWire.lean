import YM.Integration.WilsonPosteriorProjectionRay

/-! The directions in a component of the outgoing formal wire tensor.
A wire selects a site, an axis face and a Lie color. Each such component
charges a single Wilson edge; any polarization subset costs at most its
number of slots, including when several slots coincide. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionWire
open Finset Set Lattice Wilson RG Precision Tree Exterior Push.Uniform
open WilsonPosteriorProjectionRay
open scoped BigOperators Classical
variable {G : Gauge} {c : Side}

def display (a : Directions G c) : Positions (Primary c G) :=
  (tint G _).symm (fun l => a (l.1,axisEquiv.symm l.2))

theorem direction_display (g : ℝ) (a : Directions G c) :
    direction g (display a) = g • a := by
  funext e
  unfold direction display
  rw [map_smul,ContinuousLinearEquiv.apply_symm_apply]
  change g • a (e.1,axisEquiv.symm (axisEquiv e.2)) = g • a e
  rw [axisEquiv.symm_apply_apply]

abbrev Letter (G : Gauge) (c : Side) := Site c × TypeFace 1 × G.ColorIndex

def edge (b : Letter G c) : Edge (Site c) := (b.1,axisEquiv.symm b.2.1)
def color (b : Letter G c) : G.Color := PiLp.single 2 b.2.2 1
def impulse (b : Letter G c) : Directions G c := Pi.single (edge b) (color b)

theorem chart_letter (b : Letter G c) :
    display (impulse b) = Pi.single ((b.1,b.2.1),b.2.2) (1:ℝ) := by
  funext i
  obtain ⟨⟨x,l⟩,a⟩ := i
  change (impulse b (x,axisEquiv.symm l)) a = _
  obtain ⟨u,q,k⟩ := b
  by_cases hx : x=u <;> by_cases hl : l=q <;> by_cases ha : a=k <;>
    simp [impulse,edge,color,PiLp.single_apply,hx,hl,ha]

def selected {r : ℕ} (v : Fin r → Letter G c) (I : Finset (Fin r)) : Directions G c :=
  ∑ j ∈ I, impulse (v j)

def photograph : Directions G c →ₗ[ℝ] Positions (Primary c G) where
  toFun := display
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blend {r : ℕ} (v : Fin r → Letter G c) : (Fin r → ℝ) →ₗ[ℝ] Directions G c :=
  ∑ j, (LinearMap.proj j (R:=ℝ)).smulRight (impulse (v j))

def studio {r : ℕ} (v : Fin r → Letter G c) :
    (Fin r → ℝ) →L[ℝ] Positions (Primary c G) :=
  (photograph.comp (blend v)).toContinuousLinearMap

theorem studio_basis {r : ℕ} (v : Fin r → Letter G c) (i : Fin r) :
    studio v (Pi.single i (1:ℝ)) = display (impulse (v i)) := by
  change display (blend v (Pi.single i (1:ℝ))) = _
  congr 1
  simp [blend,LinearMap.sum_apply,LinearMap.smulRight_apply,Pi.single_apply,ite_smul]

theorem studio_toll {r : ℕ} (v : Fin r → Letter G c) (u : Fin r → ℝ) (g : ℝ) :
    ∑ l, ‖direction g (studio v u) l‖ ≤ |g| * ∑ j, |u j| := by
  change ∑ l, ‖direction g (display (blend v u)) l‖ ≤ _
  rw [direction_display]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg g)
  calc
    _ ≤ ∑ l, ∑ j, ‖(u j) • impulse (v j) l‖ := by
      apply sum_le_sum
      intro l _
      simp only [blend,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply,
        Finset.sum_apply,Pi.smul_apply]
      exact norm_sum_le ..
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [norm_smul,Real.norm_eq_abs,← mul_sum]
      rw [sum_eq_single (edge (v j))]
      · simp [impulse,color]
      · intro l _ hl
        simp [impulse,hl]
      · simp

theorem selected_toll {r : ℕ} (v : Fin r → Letter G c) (I : Finset (Fin r)) (g : ℝ) :
    ∑ l, ‖direction g (display (selected v I)) l‖ ≤ |g| * I.card := by
  rw [direction_display]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg g)
  calc
    _ ≤ ∑ l, ∑ j ∈ I, ‖impulse (v j) l‖ := by
      apply sum_le_sum
      intro l _
      simp only [selected,Finset.sum_apply]
      exact norm_sum_le ..
    _ = _ := by
      rw [sum_comm]
      have unit (j : Fin r) : ∑ l, ‖impulse (v j) l‖ = 1 := by
        rw [sum_eq_single (edge (v j))]
        · simp [impulse,color]
        · intro l _ h
          simp [impulse,h]
        · simp
      simp_rw [unit]
      simp

end YM.Integration.WilsonPosteriorProjectionWire

