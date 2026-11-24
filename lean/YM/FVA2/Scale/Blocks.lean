import YM.FVA2.Scale.Mesh
/-!
# Grading for Scale conversion

On exactly physical fields. Need every coefficient through each engineering
horizon. `Band` and `Pure` on matrices independent of position choices/MS.
Use NormStab, the **actual** real infinitesimal frame stabilizer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open scoped Topology ContDiff BigOperators Classical
open Dframe
variable {G:Gauge}{d j m:ℕ}
local notation "L"=> FieldEnd G d
local notation "S"=> Sec G d
local notation "D"=> Fin (d+1)
namespace Level
-- interpolation projections diagonal only; dimensions not ranks!
abbrev E (d:ℕ) := Fin (d+1)
theorem within (i:E d): i.val ≤ d:= by have h:=i.isLt; omega
def proj (i:E d) : FieldEnd G d:= (en (within i)) ∘ₗ (part d i)
variable (p:Sec G d)(s:Ortho)(i: Fin (d+1))
lemma all : ∑ i:D, proj i p=p:= enfits p
lemma distinct (j:D)(h:i≠j): proj i (proj j p)=0:= by unfold proj; simp only [LinearMap.comp_apply, part_other _ (fun e=> h ( Fin.ext e )) _,map_zero]
lemma same (h:j≤d) (v:On.Grade G j): proj (⟨j,Nat.lt_succ_of_le h⟩) (en h v)=en h v:= by unfold proj; rw [LinearMap.comp_apply, part_same (d:=d) ]; -- he
lemma again : proj i (proj i p)=proj i p:= same (within i) (part d i p)
lemma orient : proj i (ori s d p)=ori s d (proj i p):= Subtype.ext (part_ori _ _ _)
lemma real : proj i (reel d p)=reel d (proj i p):= Subtype.ext (part_reel p i)
lemma top (p:Toon G d) : proj ( d:=d ) p.1 ( Dframe.theory p )=theory p:= by rw [ ← pure_sig ]; exact same ..
lemma leaf_0 : proj (0:D) (leaf G d)=leaf G d:= by
    have he:proj (d:=0) (0:Fin 1) (leaf G 0)=leaf G 0:= by
        obtain he:= all (leaf G 0); rw [Finset.sum_eq_single (0:Fin (0+1))] at he; exact he; · intro j hj hne; exact False.elim (hne (@Subsingleton.elim ( Fin 1 ) _ _ _))
        simp
    suffices proj (0:D) (leaf G d)=up (Nat.zero_le d) (proj (d:=0) (0:Fin 1) (leaf G 0)) by rw [ this,he ]; rfl
    rfl
lemma leaf_h (h:i≠0): proj i (leaf G d)=0:= by
    conv_lhs=>rhs; rw [ ← leaf_0 (G:=G) ];
    exact distinct _ _ _ h
-- characteristic filtration.
abbrev Band (T:FieldEnd G d) : Prop:= ∀ (i:ℕ) (_h:i ≤ d) (p:Sec G d),p.val∈shellSector G i → (T p).val∈shellSector G i
lemma bottom : (proj i p).val∈ shellSector G i.val := (part d i p).property.1
lemma bound (j:ℕ)(h:p.val∈shellSector G j) (he:j < i.val): proj i p=0:= by
    let v:Sec G j:= ⟨p.val,h⟩; obtain hh: j≤ d:= by have h:=i.isLt; omega
    unfold proj; rw [ LinearMap.comp_apply, show p=up hh v from rfl, part_up,part_zero he, map_zero]
lemma remains : Band ( proj i (G:=G) ):= by
    intro l hl p h; by_cases hp:i.val ≤ l; exact Maxwell.Free.chain hp (bottom p i); rw [bound p i _ h (Nat.lt_of_not_ge hp)]; exact Submodule.zero_mem _ -- namespace?
lemma one_band : Band (1:L):= fun _ _ _ hp=> hp
lemma stop {T : FieldEnd G d}(h:Band T)(j:D)(he:i>j): proj i ( T ( proj j p ))=0:= bound _ i _ ( h _ ( within j ) _ (bottom p j) ) he
lemma rise_p (t:ℝ) (p:ℕ) : Extent.token t p≠ 0:= pow_ne_zero _ ( Complex.ofReal_ne_zero.mpr (Real.exp_pos _|>.ne') )
-- Block projection onto graded-end subspace (diag)
def diag : FieldEnd G d→ₗ[ℂ] FieldEnd G d where
    toFun a:= ∑ i:D,proj i * a * proj i
    map_add' a b:= by simp only [mul_add,add_mul,Finset.sum_add_distrib]
    map_smul' c a:= by rw [RingHom.id_apply, Finset.smul_sum ]; apply Finset.sum_congr rfl; intro i _; rw [ mul_smul_comm, smul_mul_assoc ]
variable (A B: FieldEnd G d)
lemma diagonals : diag A ( proj i p )= proj i (A (proj i p)):= by
    unfold diag; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, Module.End.mul_apply ]; rw [ Finset.sum_eq_single i ]; · rw [again]
    · intro j _ h; rw [ distinct p _ _ h,map_zero,map_zero ]
    simp
lemma diagonal_one : diag (1:L)=1:= by
    ext p; conv_lhs=>arg 2; rw [ ← all p ]; -- unfolds binder loc
    rw [map_sum]; simp_rw [diagonals, Module.End.one_apply, again, all ]; -- rhs one_apply
lemma diagonal_band (h:Band A): Band (diag A):= by
    intro j hj p hp; change ( (∑ i:D,proj (G:=G) i * A * proj i:L) p).val∈_
    rw [LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum ]; apply Submodule.sum_mem; intro i _; exact remains i _ hj _ (h _ hj _ ( remains i _ hj _ hp ))
lemma diagonal_change (h:A∈ Normalize.Change G d): diag A∈ Normalize.Change G d:= by
    refine ⟨ ?_, diagonal_band A h.2.1 ,fun p=>?_,fun s p=>?_⟩
    · rw [← leaf_0, diagonals, leaf_0, h.1,map_zero]
    · conv_lhs=>arg 2; arg 2; rw [← all p]
      conv_rhs=>arg 2; arg 2; rw [← all p]
      simp_rw [map_sum, ← real p, diagonals,real,h.2.2.1, real ] -- may orientation loop
    conv_lhs=>arg 2; arg 2; rw [← all p]
    conv_rhs=>arg 2; arg 2; rw [← all p]
    simp_rw [map_sum, ← orient p, diagonals,orient,h.2.2.2,orient]
lemma diagonal_react : diag ( diag A )=diag A:= by ext1 p; rw [← all p,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [diagonals, diagonals, again]
lemma diagonal_mul (hu:Band A)(hv:Band B) : diag (A*B)=diag A*diag B:= by
    ext1 p; rw [ ← all p ]; rw [map_sum,map_sum]; refine Finset.sum_congr rfl (fun i _=>?_ ); rw [ diagonals, Module.End.mul_apply, Module.End.mul_apply, diagonals, diagonals ]; -- reduce rhs again
    let v:= B (proj i p); change proj i (A v)=proj i (A (proj i v)); nth_rw 1 [ ← all v ]; rw [map_sum,map_sum, Finset.sum_eq_single i ]; intro j _ hij; by_cases h:j < i; · exact stop v i hu j h
    unfold v; rw [ stop p j hv i (lt_of_le_of_ne (le_of_not_gt h) ( Ne.symm hij ) ), map_zero, map_zero ]; -- check h inequality; then simp
    simp
abbrev Graded (T:FieldEnd G d) : Prop:= diag T=T
lemma graded_test : Graded A ↔ ∀ (p:S)(i:D), proj i (A (proj i p))= A (proj i p):= by
    constructor; intro H p i; rw [ ← diagonals, H ]
    intro h; ext1 p; rw [ ← all p, map_sum,map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [diagonals,h]
end Level
end YM.FVA2.Scale
