import YM.QuadraticLocal.Poetry.Oculus
/-!
# Analytic packet appearance at earliest not-yet-completed rank (without color averaging yet)
 Direct endpoint materializes EACH mark and multiplier root, count and sizes in cost unit. New field
 genuine constituents, not cooked.L.Runtime guard.Owner root.W.Still needs uniform budgets after extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Rovers
-- partition inputs and spectators
local notation "p'"=> Point α
local notation "Q"=> Slip (Point (α⊕M))
def primary (q: Slip (Point (α⊕M))): Slip (Point α):= q.filterMap (fun i=> i.2.elim (fun v=> some (i.1,v)) fun _=> none)
def second (q: Slip (Point (α⊕M))): Slip (Point M):= q.filterMap (fun i=> i.2.elim (fun _=>none) fun v=> some (i.1,v))
lemma flushed (L:Slip (Point (α⊕M))) : tally (swallow α (second L)) q=tally L q:= by
 induction L with
 | nil=>rfl
 | cons i L ih=>
   rcases i with ⟨x,v|v⟩; · rw [Focus.stamped]; exact ih.trans (zero_add _).symm
   change tally ((x,Sum.inr v):: _) q=_; rw [Focus.stamped,Focus.stamped]; exact congr_arg (Focus.calls (α:=α) (.inr v) q+·) ih
lemma owned (v:p')(L: Slip (Point (α⊕M))): (v∈primary L) ↔ (v.1,Sum.inl v.2)∈L := by
 induction L with
 | nil=> simp [primary]
 | cons i L ih=> rcases v with ⟨p,x⟩; rcases i with ⟨i,j|j⟩ <;> simp [primary] at ih ⊢ <;> aesop
lemma knows (q:Point M)(L: Slip (Point (α⊕M))): (q∈second L) ↔ (q.1,Sum.inr q.2)∈L := by induction L with
 | nil=> simp [second]
 | cons i L ih=> rcases q with ⟨p,x⟩; rcases i with ⟨i,j|j⟩ <;> simp [second] at ih ⊢ <;> aesop
lemma size_at (L:Q): L.length=(primary L).length+(second L).length:=by induction L with
 | nil=>rfl
 | cons x L h=> rcases x with ⟨x,z|z⟩ <;> simp [primary,second,h,Nat.add_assoc,Nat.add_comm, Nat.add_left_comm]
lemma meter_at (L:Q): meter L=meter (primary L)+meter (second L):=by induction L with
 | nil=>rfl
 | cons x L h=> rcases x with ⟨x,z|z⟩ <;> simp [meter,primary,second] at h ⊢ <;> omega
lemma spent (p:p'→ℝ) (q:Point M→ℝ)(L:Q): paid (fun i:Point (α⊕M)=> i.2.elim (fun x=>p (i.1,x)) (fun x=> q (i.1,x))) L= paid p (primary L)*paid q (second L):= by
 induction L with
 | nil=>exact (one_mul _).symm
 | cons i L h=> rcases i with ⟨x,v|v⟩
                case inl=> change (p (x,v))*paid _ L=((p (x,v))*paid _ (primary L))*paid _ (second L); rw [h]; ring
                case inr=> change q (x,v)*paid _ L=paid _ (primary L)*(q (x,v)*paid _ (second L)); rw [h]; ring

variable (L:Slip (Point (Coarse G⊕M)))
local notation "W"=> primary L
abbrev rank:= (primary L).length
def pier (i:Fin (rank L)): Point (Coarse G):= (primary L).get i
local notation "α₁"=> pier L
abbrev edge (x:Point (Coarse G)): Edge Cover:= (x.1, Exterior.axisEquiv.symm x.2.1)
local notation "γ" i:max=> edge (pier L i)
open Pinned Knot
abbrev Project (L: Slip (Point (Coarse G⊕M))) := (i:Fin (rank L)) → BooksC G (edge (pier L i))
set_option quotPrecheck false
variable (θ:Project L)
local notation "C₁" i=> cite G (γ i) (θ i)
def path (i:Fin (rank L)) : Slot:= let t:=cite G (γ i) (θ i); walkSlot t.face t.start
def coin : Texture.Tooth G (rank L):=fun i=> (pier L i).2.2
def coat : ℝ:= ∏ i:Fin (rank L),Pinned.sign (C₁ i)
def star (v:ℝ): Atom G (rank L) where
 leg:= path L θ
 coeff:= Pi.single (coin L) (v * coat L θ)
local notation "g" v:max=> Rovers.star L θ v
lemma linger (v:ℝ): (g v).magnitude=|v|:= by
 have ht:|coat L θ|=1:= by unfold Rovers.coat; rw [Finset.abs_prod]; apply Finset.prod_eq_one; intro i _; unfold Pinned.sign; split <;> norm_num
 unfold Atom.magnitude; change (∑ i:Texture.Tooth G _, |Pi.single (coin L) (v*coat L θ) i|)= _; rw [Finset.sum_eq_single (coin L),Pi.single_eq_same,abs_mul,ht,mul_one]; · intro i _ hi; simp [Pi.single_apply,hi]
 simp
lemma sojourn : (g (b)).length=meter (primary L) + 4*rank L ∨ (g (b)).length < meter (primary L)+4*rank L:= by -- simplify
   apply or_iff_not_imp_left.mpr; intro h; apply lt_of_le_of_ne _ h; let v(i:Fin (rank L)):= size (pier L i).1; have hz : meter (primary L)=∑ i,v i:= by unfold meter; nth_rw 1 [← List.ofFn_get (primary L)]; rw [List.map_ofFn,List.sum_ofFn]; rfl
   rw [hz]; unfold Atom.length; change (∑ i,(path L θ i).length)≤ _; calc
      _ ≤ ∑ i:Fin (rank L),(v i+4):= Finset.sum_le_sum (s:=Finset.univ) (fun i _=> by unfold Rovers.path; dsimp only; rw [walkSlot_cost]; exact Nat.add_le_add_right (native_zone ..) _)
      _ = _:= by rw [sum_add_distrib]; simp [mul_comm]
lemma quantity : (g (b)).length ≤ meter L + 4*rank L:=by have h:= Rovers.sojourn (b:=b) L θ; have he:= meter_at L; omega
end Rovers
end YM.QuadraticLocal.Poetry
