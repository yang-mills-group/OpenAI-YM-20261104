import YM.Integration.RootedJointSignedInitialization
import YM.Integration.NativeReplicaServed
import YM.Integration.NativeRestrictionServed
import YM.PE.Arc.Focal

/-!
The literal product and counterterm branches used by native product grouping.
Every counterterm occurs once; the remaining entries in its finite product
are the unit.  The two branches are kept separate until compatibility has
been imposed, and their signed aggregation is the actual physical difference.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeSignedBranches
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent MergeProof.Replicum Extra.Trajectories
open RG3.Annuncia
open JointSignedInitialization
open scoped Classical BigOperators

variable {I X : Type} [DecidableEq I] [Fintype I] {arity : ℕ}

abbrev Branch (I : Type) := I × Bool

def sign (i : Branch I) : ℂ := if i.2 then 1 else -1

def field (F : I → Fin (arity + 1) → X → ℂ) (K : I → X → ℂ) :
    Branch I → X → ℂ :=
  fun i U => if i.2 then ∏ j, F i.1 j U else K i.1 U

def matrix (F : I → Fin (arity + 1) → X → ℂ) (K : I → X → ℂ) :
    Replicum.Name arity (Branch I) → X → ℂ :=
  fun i U => if i.1.2 then F i.1.1 i.2 U else if i.2 = 0 then K i.1.1 U else 1

omit [DecidableEq I] [Fintype I] in
/-- Padding does not duplicate the physical counterterm. -/
theorem matrix_product (F : I → Fin (arity + 1) → X → ℂ) (K : I → X → ℂ)
    (i : Branch I) (U : X) :
    (∏ j, matrix F K (i, j) U) = field F K i U := by
  rcases i with ⟨i, b⟩
  cases b <;> simp [matrix, field]

/-- Both alternatives are aggregated only after they share one region slot. -/
theorem aggregate_field (F : I → Fin (arity + 1) → X → ℂ) (K : I → X → ℂ) :
    Rooted.aggregate (Prod.fst : Branch I → I) sign (field F K) =
      JointSignedInitialization.signed F K := by
  funext i U
  unfold Rooted.aggregate
  rw [Fintype.sum_prod_type]
  simp [field, sign, JointSignedInitialization.signed,
    sub_eq_add_neg, add_comm]

variable {G : Gauge} {n : Side}

/-- Native complete-product projection starts from the same original
unmarked density, including the counterterm's explicit unit entries. -/
theorem matrix_birth (P : Rep G n)
    (F : I → Fin (arity + 1) → Config G n → ℂ) (K : I → Config G n → ℂ) :
    (fun U => reap (birth (Aged arity (Branch I)) P (matrix F K) U)) =
      birth (Bud (Branch I)) P (field F K) := by
  funext U
  apply Marker.Poly.ext
  intro s
  change (birth (Aged arity (Branch I)) P (matrix F K) U).part (plena s) =
    (birth (Bud (Branch I)) P (field F K) U).part s
  unfold birth Mach
  simp only [Poly.part_smul, pass_fire]
  congr 1
  unfold plena
  rw [Finset.prod_product]
  exact Finset.prod_congr rfl (fun i _ => matrix_product F K i U)

/-- Impose the actual alternative exclusion before applying the native
mouth.  Multiplication is used only by these genuine homomorphisms, never
by the complete-product projection `reap`. -/
def merge : Poly (Bud (Branch I)) →L[ℂ] Poly (Bud I) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun p => Replica.mouth Prod.fst (Bud I) sign
          ((NativeRestrictionServed.intoStock (Replica Prod.fst (Bud I))).restriction p)
       map_add' := by intro p q; rw [map_add, map_add]
       map_smul' := by
         intro c p
         rw [Names.smul, Replica.csmul]
         rfl } : Poly (Bud (Branch I)) →ₗ[ℂ] Poly (Bud I))

/-- The full linear initialization map: complete products, then exact
alternative exclusion, then signed regional aggregation. -/
def compress : Poly (Aged arity (Branch I)) →L[ℂ] Poly (Bud I) :=
  (merge (I := I)).comp reap

theorem merge_birth (P : Rep G n)
    (F : I → Fin (arity + 1) → Config G n → ℂ) (K : I → Config G n → ℂ) :
    (fun U => merge (birth (Bud (Branch I)) P (field F K) U)) =
      birth (Bud I) P (JointSignedInitialization.signed F K) := by
  let r := NativeRestrictionServed.intoStock
    (Replica (Prod.fst : Branch I → I) (Bud I))
  have hr := NativeRestrictionServed.restriction_birth r P (field F K)
  have hm := Rooted.mouth_birth (Prod.fst : Branch I → I) (Bud I) sign P (field F K)
  calc
    _ = (fun U => Replica.mouth Prod.fst (Bud I) sign
        (birth (Replica Prod.fst (Bud I)) P (field F K) U)) :=
      congrArg (fun f => fun U => Replica.mouth Prod.fst (Bud I) sign (f U)) hr
    _ = _ := by rw [hm, aggregate_field]

/-- The grouped signed input is exactly the old full-array birth on P. -/
theorem compress_birth (P : Rep G n)
    (F : I → Fin (arity + 1) → Config G n → ℂ) (K : I → Config G n → ℂ) :
    (fun U => compress (birth (Aged arity (Branch I)) P (matrix F K) U)) =
      birth (Bud I) P (JointSignedInitialization.signed F K) := by
  funext U
  simp only [compress, ContinuousLinearMap.comp_apply]
  rw [congr_fun (matrix_birth P F K) U]
  exact congr_fun (merge_birth P F K) U

/-- This exact linear operation commutes with each push on one history. -/
theorem compress_gust (H : History G) (N p : ℕ)
    (X : Config G (H.S.side N p) → Poly (Aged arity (Branch I)))
    (hX : Integrable X (prior G _)) {m : ℕ} (hm : m ≤ N) :
    gust H N p N (fun U => compress (X U)) m hm =
      fun U => compress (gust H N p N X m hm U) := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i hi ih =>
    rw [gust_step H N p N _ hi, ih]
    funext U
    rw [gust_step H N p N _ hi]
    unfold StepData.push
    let L := (compress (I := I) (arity := arity)).restrictScalars ℝ
    have he := L.integral_comp_comm
      (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i + 1)))
        U _ (gust_live H N p N X hX hi))
    simp_rw [L.map_smul] at he
    exact he

theorem signed_gust (H : History G) (N p : ℕ)
    (F : I → Fin (arity + 1) → Config G (H.S.side N p) → ℂ)
    (K : I → Config G (H.S.side N p) → ℂ)
    (hX : Integrable
      (birth (Aged arity (Branch I)) (H.rep N p N) (matrix F K)) (prior G _))
    {m : ℕ} (hm : m ≤ N) :
    gust H N p N (birth (Bud I) (H.rep N p N)
      (JointSignedInitialization.signed F K)) m hm =
      fun U => compress (gust H N p N
        (birth (Aged arity (Branch I)) (H.rep N p N) (matrix F K)) m hm U) := by
  rw [← compress_birth (H.rep N p N) F K]
  exact compress_gust H N p _ hX hm

/-- Apply the genuine restriction and mouth receipts to an already
constructed Deck output.  No degree or root is dropped except the exact
exclusion of simultaneous alternatives; its price is unchanged. -/
theorem merge_served (P : Rep G n)
    (Φ : Branch I → Config G n → ℂ)
    (ω : Branch I → Box n → Config G n → ℂ)
    (Z : Config G n → Poly (Bud (Branch I))) (o : I → Site n) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {e c : ℝ}
    (h : Served P Φ ω Z (o ∘ Prod.fst) (w ∘ Prod.fst) e c) :
    Served P (Rooted.aggregate Prod.fst sign Φ)
      (fun v s U => Rooted.aggregate Prod.fst sign (fun i => ω i s) v U)
      (fun U => merge (Z U)) o w e c := by
  have hr := NativeRestrictionServed.stock_served
    (Replica Prod.fst (Bud I)) P Φ ω Z (o ∘ Prod.fst) (w ∘ Prod.fst)
    (fun i => hw i.1) h
  have hsign : ∀ i : Branch I, ‖sign i‖ ≤ (1 : ℝ) := by
    intro i
    unfold sign
    split <;> norm_num
  apply NativeReplicaServed.mouth_served Prod.fst (Bud I) sign P Φ ω _ o w
    (fun _ => 1) hw (fun _ => zero_le_one) hsign
  simpa only [one_mul, Function.comp_def] using hr

end YM.Integration.NativeSignedBranches
