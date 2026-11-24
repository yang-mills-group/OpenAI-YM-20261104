import YM.Comparison.RG02.Bulk.Fk
import YM.Push.STATIONARY_UNIFORM.Array
import YM.Push.LOOP_COEFFICIENT.Paths.Calculus

/-! Literal coordinates for the original full joint action. None is the
coupling coordinate; every some-coordinate is an original Array coordinate.
Gaussian directions occupy only the free-fine summand. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualJointCoordinateMap
open Function Lattice RG Precision Tree Exterior Push.Uniform Comparison.RG02
open scoped BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

abbrev Index := Option (Push.Uniform.Joint F G)

def fieldPart : Positions (Index (G := G) F) →L[ℝ]
    Positions (Push.Uniform.Joint F G) :=
  ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.proj (φ := fun _ : Index (G := G) F => ℝ) (some i))

def lift : Positions (Index (G := G) F) →L[ℝ] Bulk.Joint S F (G := G) :=
  (ContinuousLinearMap.proj (φ := fun _ : Index (G := G) F => ℝ) none).prod
    ((paint F G).toContinuousLinearMap.comp (fieldPart (G := G) F))

def fieldVector (v : Positions (Push.Uniform.Joint F G)) :
    Positions (Index (G := G) F) := fun i => i.elim 0 v

/-- None carries exactly the original coupling direction. -/
theorem coupling_value : lift (G := G) F (Pi.single (none : Index (G := G) F) (1 : ℝ)) = (1, 0) := by
  have ht : fieldPart (G := G) F (Pi.single (none : Index (G := G) F) (1 : ℝ)) = 0 := by
    ext i
    simp [fieldPart]
  change ((Pi.single (none : Index (G := G) F) (1 : ℝ) :
      Positions (Index (G := G) F)) none,
    paint F G (fieldPart (G := G) F (Pi.single (none : Index (G := G) F) (1 : ℝ)))) = (1, 0)
  rw [ht, map_zero]
  simp

/-- Every field coordinate remains the same Array basis vector. -/
theorem field_value (i : Push.Uniform.Joint F G) :
    lift F (Pi.single (some i) 1) = (0, paint F G (bolt i)) := by
  have ht : fieldPart (G := G) F (Pi.single (some i) 1) = bolt i := by
    ext j
    simp [fieldPart, bolt, Pi.single_apply]
  change ((Pi.single (some i) (1 : ℝ) : Positions (Index (G := G) F)) none,
    paint F G (fieldPart (G := G) F (Pi.single (some i) 1))) = _
  rw [ht]
  simp

/-- A physical field vector has zero coupling component. -/
theorem field_vector_value (v : Positions (Push.Uniform.Joint F G)) :
    lift F (fieldVector F v) = (0, paint F G v) := rfl

/-- The Gaussian map occupies the exact original free-fine coordinates. -/
theorem gaussian_value (z : Precision.Key F G → ℝ) :
    lift F (fieldVector F (Sum.elim (fun _ => 0) z)) = Bulk.hinge F z := by
  rw [field_vector_value]
  rfl

variable {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O)

def rayVector (B : fieldDir G c 1) : Positions (Index (G := G) F) :=
  fieldVector F ((paint F G).symm (Bulk.classical S F (K.b F) B))

/-- The fixed physical ray is the literal original stationary direction. -/
theorem ray_value (B : fieldDir G c 1) :
    lift F (rayVector F K B) = (0, Bulk.classical S F (K.b F) B) := by
  unfold rayVector
  rw [field_vector_value, ContinuousLinearEquiv.apply_symm_apply]

/-- Adding the zero coupling entry changes no physical coordinate mass. -/
theorem ray_mass (B : fieldDir G c 1) :
    (∑ i : Index (G := G) F, |rayVector F K B i|) =
      ∑ i : Push.Uniform.Joint F G,
        |(paint F G).symm (Bulk.classical S F (K.b F) B) i| := by
  unfold rayVector fieldVector
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, abs_zero, zero_add]

/-- Every full derivative is transported through the exact linear coordinate
map. This preserves all ordered directions, including repeated indices. -/
theorem derivative {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {h : Bulk.Joint S F (G := G) → W}
    (hh : ContDiffAt ℝ ω h 0) (n : ℕ)
    (v : Fin n → Positions (Index (G := G) F)) :
    iteratedFDeriv ℝ n (h ∘ lift F) 0 v =
      iteratedFDeriv ℝ n h 0 (fun i => lift F (v i)) := by
  simpa only [map_zero, zero_add, Function.comp_def] using
    Push.Loops.Paths.iterated_affine (lift F) 0 0
      (show ContDiffAt ℝ ω h (0 + lift F 0) by simpa only [map_zero, zero_add] using hh) v

end YM.Integration.ActualJointCoordinateMap
end
