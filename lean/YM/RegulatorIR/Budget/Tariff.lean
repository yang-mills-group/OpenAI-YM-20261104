import YM.RegulatorIR.Budget.Spatial
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Absolute momentum-free position budgets; full total variation with separated
anchor in measurement coordinates, or held at any one vertex leg for
translation-free tensors. ENNReal avoids totalized estimates on nonsummable
series.
-/

noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget

open Set Function Lattice Spatial Motion
open scoped ENNReal NNReal Topology BigOperators Classical

structure Tariff (X : Type) where
  road : X → X → ℝ≥0∞
  unit x y : 1≤ road x y
  own x : road x x=1
  symm x y : road x y=road y x
  tri x y z : road x z ≤ road x y * road y z

structure Premium {X:Type} (A:Tariff X) where
  mark : X→ℝ≥0∞
  unit x : 1≤mark x
  travel x y : mark x ≤ mark y * A.road x y

namespace Tariff
variable {X Y : Type}

/-- Pull back displacement costs to a label space, allowing several labels at
one position. -/
def uses (A:Tariff X)(pos:Y→X): Tariff Y :=
 { road := fun a b=> A.road (pos a) (pos b)
   unit := fun _ _=>A.unit _ _
   own := fun _=>A.own _
   symm := fun _ _=>A.symm _ _
   tri := fun _ _ _=>A.tri _ _ _ }

/-- Position moment order u, with cost radius l (physical units). -/
def amount (l : ℝ) (u : ℕ) (d:ℝ) := ENNReal.ofReal (1 + d/l)^u
lemma amount_mono {l : ℝ} (h:0<l) (u:ℕ) {d e:ℝ} (he:d≤e): amount l u d ≤ amount l u e := by
  unfold amount
  gcongr
lemma amount_add (l : ℝ) (u v:ℕ)(d:ℝ): amount l (u+v) d=amount l u d*amount l v d:=pow_add ..
@[simp] lemma amount_zero (l : ℝ) (u) : amount l u 0=1:=by simp [amount]
lemma amount_unit {l : ℝ} (h:0<l) (u) {d} (hd:0≤d) : 1≤amount l u d:=(amount_zero l u).symm.trans_le (amount_mono h u hd)
lemma moment_mono {l:ℝ} (h:0<l) {u v:ℕ} (he:u≤v) {d} (hd:0≤d): amount l u d ≤ amount l v d := by
  apply pow_le_pow_right₀ _ he
  have hh := amount_unit h 1 hd
  simpa only [amount,pow_one] using hh
lemma amount_tri {x y z:ℝ}(h:x≤y+z){l:ℝ}(hl:0<l)(u:ℕ)(hr:0≤y)(hh:0≤z): amount l u x≤ amount l u y * amount l u z := by
 apply (amount_mono hl u h).trans
 unfold amount; rw [← mul_pow,← ENNReal.ofReal_mul (by positivity)]
 have hs : 1+(y+z)/l ≤ (1+y/l)*(1+z/l) := by
    rw [add_div];nlinarith only [div_nonneg hr hl.le,div_nonneg hh hl.le]
 gcongr

-- Tariffs shared on all positions at a step.
def native (l : ℝ)(h:0<l)(u:ℕ): Tariff Room where
  road x y := amount l u (dist x y)
  unit x y := amount_unit h u dist_nonneg
  own x := by simp
  symm x y:=by rw [dist_comm]
  tri x y z:=amount_tri (dist_triangle ..) h u dist_nonneg dist_nonneg

def onFold (P:ℝ)(hp:0<P)(l : ℝ)(h:0<l)(u:ℕ): Tariff Room where
  road x y := amount l u (distance P x y)
  unit x y := amount_unit h u (distance_nonneg ..)
  own x := by rw [distance_self hp]; apply amount_zero
  symm x y:=by rw [distance_comm hp]
  tri x y z:=amount_tri (distance_triangle hp ..) h u (distance_nonneg ..) (distance_nonneg ..)

/-- Cost on a tensor insensitive to permutation of its positions. This
counts diameter in the underlying space. -/
def diameter (A : Tariff X) {r:ℕ}(x : Fin r → X) := (⨆ p,⨆ q,A.road (x p) (x q)) ⊔ 1
lemma diameter_unit (A:Tariff X){r:ℕ}(x:Fin r→X): 1≤A.diameter x:=le_sup_right
lemma diameter_le {r:ℕ} (A:Tariff X){x:Fin r→X}{c:ℝ≥0∞}(hc:1≤c)(h:∀ p q,A.road (x p) (x q) ≤ c) : A.diameter x≤c:=sup_le (iSup_le fun p=>iSup_le fun q=>h p q) hc
lemma diameter_ge {r:ℕ} (A:Tariff X)(x:Fin r→X) p q : A.road (x p) (x q) ≤ A.diameter x :=
  le_trans (le_iSup₂ (f:=fun p q=>A.road (x p) (x q)) p q) le_sup_left
lemma diameter_perm {r:ℕ} (A:Tariff X) (x:Fin r→X)(e:Equiv.Perm (Fin r)) : A.diameter (x ∘ e)=A.diameter x := by
  have h (x:Fin r→X)(e:Equiv.Perm (Fin r)) : A.diameter (x ∘ e)≤ A.diameter x := A.diameter_le (A.diameter_unit _) fun _ _=>A.diameter_ge _ _ _
  exact le_antisymm (h ..) (by simpa only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using h (x ∘ e) e.symm)
end Tariff

namespace Premium
variable {X Y : Type} {A : Tariff X}

def free (A : Tariff X) : Premium A where
 mark _ := 1
 unit _ := le_rfl
 travel x y := by rw [one_mul]; apply A.unit

def rooted (A : Tariff X) (x:X) : Premium A where
 mark y := A.road x y
 unit _ := A.unit _ _
 travel a b := by rw [A.symm a b]; apply A.tri

def uses (B:Premium A)(pos:Y→X): Premium (A.uses pos) :=
 { mark := B.mark ∘ pos
   unit := fun _=>B.unit _
   travel := fun _ _=>B.travel _ _ }

def remnant (P:ℝ)(hp:0<P)(l:ℝ)(h:0<l)(u:ℕ) : Premium (Tariff.onFold P hp l h u) where
 mark a:=Tariff.amount l u (singular P a)
 unit _:=Tariff.amount_unit h u (singular_nonneg ..)
 travel a b:=Tariff.amount_tri (singular_lip hp a b) h u (singular_nonneg ..) (distance_nonneg ..)

def width (B:Premium A) {r:ℕ} (x:Fin r→X) := A.diameter x ⊔ ⨆ i,B.mark (x i)
lemma width_diameter (B:Premium A) {r:ℕ} (x:Fin r→X): A.diameter x≤B.width x:=le_sup_left
lemma width_unit (B:Premium A) {r:ℕ} (x:Fin r→X): 1≤B.width x:=le_trans (A.diameter_unit _) (width_diameter ..)
lemma width_ge (B:Premium A) {r:ℕ} (x:Fin r→X)(p): B.mark (x p)≤B.width x:=(le_iSup (fun p=>B.mark (x p)) p).trans le_sup_right
lemma width_le (B:Premium A) {r:ℕ} {x:Fin r→X}{c:ℝ≥0∞} (h:A.diameter x≤c)(hp:∀ i,B.mark (x i)≤c): B.width x≤c:=sup_le h (iSup_le hp)
lemma width_perm (B:Premium A){r:ℕ} (x:Fin r→X)(e:Equiv.Perm (Fin r)): B.width (x ∘ e)=B.width x:=by
  have h (x:Fin r→X)(e:Equiv.Perm (Fin r)): B.width (x ∘ e)≤ B.width x := B.width_le ((A.diameter_perm ..).trans_le (B.width_diameter _)) fun _=>B.width_ge x _
  exact le_antisymm (h ..) (by simpa only [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using h (x ∘ e) e.symm)
@[simp] lemma free_cost (A:Tariff X){r:ℕ}(x:Fin r→X) : width (free A) x=A.diameter x:= sup_eq_left.mpr <| iSup_le fun _=> A.diameter_unit x
end Premium
end YM.RegulatorIR.Budget
