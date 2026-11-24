import YM.MS.Graphical.Ladder
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Diagram

/-!
# Sum of the ordered scale sectors at fixed n

Pump in closing edges. Though coupling order stays constant we still have a
finite computation (bound on remaining possible field slots). Integrate each
contributing level including its counterterm. We show the result satisfies
`Dock.Bob`; here the tree/closure-base forcing `input` is from the graph at
the bottom of the ladder and `step0` acts on the sum, so `Joint` is taken
with the *filed* (node plus further cycles) inhomogeneity. This is the key
step to using the LPT uniqueness results.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical.Diagram
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open Lattice Cylinder Motif Literal Halo Outlook Mach
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} {g b' : Diagram} {b : Bool} {h j k n : ℕ}


lemma ladder_order (g : Diagram) (hx : Valid g b) (k : ℕ) (j : Diagram) (hj : j ∈ ladder g k) :
  order j = order g ∧ Valid j b := by
  induction k generalizing g with
  | zero => simpa only [Multiset.mem_singleton.mp (show j ∈ ({g} : Multiset Diagram) from hj)] using And.intro (Eq.refl (order g)) hx
  | succ k ih =>
    rw [ladder, Multiset.mem_add] at hj; rcases hj with h|h
    · rw [Multiset.mem_singleton] at h; exact h.symm ▸ ⟨rfl,hx⟩
    exact ih (close g) (by rwa [Valid]) h

lemma total_add {α A : Type} [AddCommMonoid A] (u v : Multiset α) (f : α → A) :
    total (u+v) f = total u f + total v f := by simp [total]
lemma total_bind {α β A : Type} [AddCommMonoid A] (u : Multiset α) (f : α → Multiset β) (v : β→A) :
    total (u.bind f) v = total u (fun i=> total (f i) v) := by
  induction u using Multiset.induction with
  | empty => simp [total]
  | cons i u ih => rw [Multiset.cons_bind,total_add,ih]; simp [total]
lemma total_congr {α A : Type} [AddCommMonoid A] (u : Multiset α) (f g : α → A)
    (h : ∀ x∈u, f x = g x) : total u f=total u g := by unfold total; congr 1; exact Multiset.map_congr rfl h

variable (a : ℕ→ Mob G)
variable (h)
local notation "evalD" => evaluate G a h


def allCT (f : Multiset Diagram) (b : Bool) := total f (fun i => (evalD i b).ct)

lemma bob_add {v u j j' : Flats G} {p q f g : Coat G} {r : ℤ}
    (hp : Bob b h 0 r j u f p) (hx : Bob b h 0 r j' v g q) :
    Bob b h 0 r (j+j') (u+v) (f+g) (p+q) := by
  refine ⟨?_,Cap0.heap.plus hp.2.1 hx.2.1,hp.2.2.add hx.2.2⟩
  obtain ht := hp.1.plus hx.1; rwa [map_add, add_add_add_comm]

abbrev ladderBob (b : Bool) (n : ℕ) (r : ℤ) (g : Diagram) :=
   Bob b (dimTarget h b) 0 r (input a h g b) (allPages h a (ladder g n) b)
       (initialVertex a g b) (allCT h a (ladder g n) b)

lemma ladder_paid (ha : ∀ i, VertexOK false h (a i)) (g : Diagram) (b : Bool)
    (k : ℕ) (hk : rankBound h g b ≤ (k:ℤ)) : ladderBob h a b k (rankBound h g b) g := by
  induction k generalizing g with
  | zero =>
       unfold ladderBob allPages allCT; simp only [ladder,total, Multiset.map_singleton, Multiset.sum_singleton]
       obtain ⟨ht,H,hx⟩:= (ordered a ha g b).2
       obtain he := mine H ht.toll
       have hv : Pact (step0 G (evaluate G a h g b).pages) 0 := pact0 ⟨_, (by omega : rankBound h g b - 2 < 0), clockCap he.eye⟩
       refine ⟨Joint.via ht ?_, H,hx⟩; simpa only [add_zero] using
          common (show Pact (input a h g b) _ from (show Pact _ _ from fun i=>EventuallyEq.rfl)) (pact_sym hv)
  | succ k ih =>
       obtain ⟨ht,H,hx⟩:= (ordered a ha g b).2
       obtain ⟨R,Q,P⟩:= ih (close g) (by rw [rankBound]; omega)
       rw [initialVertex,input] at R
       have hR : (rankBound h (close g) b) ≤ rankBound h g b := by rw [rankBound]; omega
       unfold ladderBob allPages allCT
       rw [ladder,total_add,total_add];
       simp only [total,Multiset.map_singleton,Multiset.sum_singleton]
       refine ⟨ ?_, Cap0.heap.plus H (clockTrans Q hR), hx.add (P.collects hR)⟩
       obtain hP := ht.plus (R.via (common (closeForce_eq _ (clockMoon H))
               (fun _ => EventuallyEq.rfl)))
       rw [add_zero] at hP
       rw [map_add]
       exact hP

lemma wide_ladder (b : Bool) (g : Diagram) (k : ℕ) (hv : Valid g b) (ht : k = rankRoom h b (order g))
    (hp : ∀ i, VertexOK false h (a i)) : ladderBob h a b k k g := by
  obtain he : rankBound h g b ≤ (k:ℤ) := ht.symm ▸ expand_order h g hv
  obtain ⟨hX,hR,hY⟩:= ladder_paid h a hp g b k he
  exact ⟨hX,clockTrans hR he,hY.collects he⟩
end YM.MS.Graphical.Diagram
