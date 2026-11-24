import YM.Integration.ActualFoundryMatrix
import YM.Integration.JointSignedExterior

/-!
The complete detector is initialized in one physical marked polynomial.
The central region contains the product-minus-candidate discrepancy. Each
exterior region contains its original physical field minus the actual zero
label of the same Family. Explicit unit entries pad the common product
arity. Exterior roots and motions remain separate from the central region.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualFoundryDetectorSource
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent MergeProof.Replicum Extra.Histories Extra.Trajectories
open NativeSignedBranches ActualFoundryInitialization
open scoped Classical BigOperators

variable {G : Gauge} {E : Type} [Fintype E] [DecidableEq E] {arity : ℕ}

abbrev Region (E : Type) := Unit ⊕ E

abbrev Slot (arity : ℕ) (E : Type) := Name arity (Branch (Region E))

/-- The exterior zero is an actual label, not an assumed zero observable. -/
theorem item_zero (C : Family G) (N p d : ℕ)
    (o : ∀ m, Site (C.side m p)) (z : Motion) :
    item C d N p (0 : C.label d) o z = 0 := by
  have hz := ((C.linearO N p d 0).mk' _).map_zero
  change C.O N p (0 : C.label d) 0 = 0 at hz
  unfold item
  rw [hz]
  funext U
  simp [stepUp, Motion.scalar]

def products (C : Family G)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (e : E → (d : ℕ) × C.label d) (unitDegree : ℕ) :
    Region E → Fin (arity + 1) → (d : ℕ) × C.label d :=
  Sum.elim (fun _ => v)
    (fun i j => if j = 0 then e i else ⟨unitDegree, C.refUnit unitDegree⟩)

def counters (C : Family G) (z : (d : ℕ) × C.label d) (zeroDegree : ℕ) :
    Region E → (d : ℕ) × C.label d :=
  Sum.elim (fun _ => z) (fun _ => ⟨zeroDegree, 0⟩)

/-- All physical labels are fixed before the marked polynomial is formed. -/
def table (C : Family G)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (unitDegree zeroDegree : ℕ) : Slot arity E → (d : ℕ) × C.label d :=
  matrixToken C (products C v e unitDegree) (counters C z zeroDegree) unitDegree

variable (C : Family G) (N p : ℕ)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (unitDegree zeroDegree : ℕ)
    (o : ∀ m, Slot arity E → Site (C.side m p))
    (motions : Slot arity E → Motion)

def centralFactors : Fin (arity + 1) → Config G (C.side N p) → ℂ :=
  fun j => item C (v j).1 N p (v j).2
    (fun m => o m ((Sum.inl (), true), j)) (motions ((Sum.inl (), true), j))

def centralCounter : Config G (C.side N p) → ℂ :=
  item C z.1 N p z.2
    (fun m => o m ((Sum.inl (), false), 0)) (motions ((Sum.inl (), false), 0))

def exteriorFields : E → Config G (C.side N p) → ℂ :=
  fun i => item C (e i).1 N p (e i).2
    (fun m => o m ((Sum.inr i, true), 0)) (motions ((Sum.inr i, true), 0))

def fields : Region E → Config G (C.side N p) → ℂ :=
  Sum.elim (fun _ U => (∏ j, centralFactors C N p v o motions j U) -
      centralCounter C N p z o motions U)
    (exteriorFields C N p e o motions)

def source : Config G (C.side N p) → Poly (Aged arity (Branch (Region E))) :=
  let t := table C v z e unitDegree zeroDegree
  PhysicalJoin.Marked.topJoint (fun a => (t a).1) (fun a => (t a).2)
    o motions (Aged arity (Branch (Region E))) N

variable (hC : C.Makes) (hUnit : C.ref unitDegree ≤ N)
include hC hUnit

/-- The complete central and exterior input has one original vacuum.
No exterior field is moved into the central region. -/
theorem full_birth :
    (fun U => compress (source C N p v z e unitDegree zeroDegree o motions U)) =
      birth (Bud (Region E)) (C.path.rep N p N) (fields C N p v z e o motions) := by
  let F := fun a j => item C (products C v e unitDegree a j).1 N p
    (products C v e unitDegree a j).2
    (fun m => o m ((a, true), j)) (motions ((a, true), j))
  let K := fun a => item C (counters C z zeroDegree a).1 N p
    (counters C z zeroDegree a).2
    (fun m => o m ((a, false), 0)) (motions ((a, false), 0))
  have hF : F = JointSignedInitialization.exteriorFactors 0
      (fun _ : Unit => centralFactors C N p v o motions)
      (exteriorFields C N p e o motions) := by
    funext a j U
    cases a with
    | inl a => rfl
    | inr i =>
      by_cases hj : j = 0
      · subst j
        rfl
      · have ht : products C v e unitDegree (Sum.inr i) j =
            ⟨unitDegree, C.refUnit unitDegree⟩ := by
          simp [products, hj]
        change item C (products C v e unitDegree (Sum.inr i) j).1 N p
            (products C v e unitDegree (Sum.inr i) j).2
            (fun m => o m ((Sum.inr i, true), j))
            (motions ((Sum.inr i, true), j)) U = if j = 0 then _ else 1
        rw [if_neg hj, ht]
        exact congr_fun (item_refUnit C hC N p unitDegree hUnit _ _) U
  have hK : K = JointSignedInitialization.exteriorCounter
      (fun _ : Unit => centralCounter C N p z o motions) := by
    funext a U
    cases a with
    | inl a => rfl
    | inr i =>
      exact congr_fun (item_zero C N p zeroDegree
        (fun m => o m ((Sum.inr i, false), 0))
        (motions ((Sum.inr i, false), 0))) U
  have hSource : source C N p v z e unitDegree zeroDegree o motions =
      birth (Aged arity (Branch (Region E))) (C.path.rep N p N) (matrix F K) :=
    matrix_topJoint C hC N p (products C v e unitDegree)
      (counters C z zeroDegree) unitDegree hUnit o motions
  rw [hSource, compress_birth, hF, hK, JointSignedInitialization.signed_exterior]
  rfl

/-- The full regional coefficient is exactly both complete physical
products with their identical exterior factors. -/
theorem full_coefficient (U : Config G (C.side N p)) :
    (compress (source C N p v z e unitDegree zeroDegree o motions U)).part
        (Stock.final (Region E)) =
      (C.path.rep N p N).eval U *
        (((∏ j, centralFactors C N p v o motions j U) -
          centralCounter C N p z o motions U) *
          ∏ i, exteriorFields C N p e o motions i U) := by
  rw [congr_fun (full_birth C N p v z e unitDegree zeroDegree o motions hC hUnit) U]
  unfold birth Mach
  simp only [Poly.part_smul, pass_fire]
  change ((C.path.rep N p N).eval U : ℂ) * (∏ i, fields C N p v z e o motions i U) = _
  rw [Fintype.prod_sum_type]
  simp only [fields, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique]

/-- Every region is pushed together through the original actual history. -/
theorem full_gust {m : ℕ} (hm : m ≤ N) :
    gust C.path N p N
        (birth (Bud (Region E)) (C.path.rep N p N) (fields C N p v z e o motions)) m hm =
      fun U => compress
        (gust C.path N p N (source C N p v z e unitDegree zeroDegree o motions) m hm U) := by
  rw [← full_birth C N p v z e unitDegree zeroDegree o motions hC hUnit]
  apply compress_gust
  exact PhysicalJoin.Marked.topLive _ _ o motions hC _ N

end YM.Integration.ActualFoundryDetectorSource
