import YM.SchemeRG11.Flare.Shift
/-!
Tri color-stripped interaction applied to fan field legs.
Open scalar readings both over real & complex coefficient ring.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SchemeRG11.Flare
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

abbrev Gem := Bool × Eye
def coin (i : Gem) := fan i.1 i.2
def tick (i j : Eye)(a b : Axis) : Sl := if i=j then [a,b] else [b]

variable (z x y : E4) (I J K : Gem) (X : Tri)
def roll {R : Type} [AddCommGroup R] [Module ℝ R] (i j k : Gem) (f : Sl→Sl→Sl→R) : Roll R:= fun s a b c d=>
    ∑ u,∑ v,∑ w,(coin i u b*coin j v c*coin k w d) • f (tick s 0 a u) (tick s 1 a v) (tick s 2 a w)

def Crew := roll I J K (fun l m n=>yolk l m n X)
lemma crews (hx:X∈clearance 4)(a b c d : Axis): Crew I J K X 0 a b c d + Crew I J K X 1 a b c d + Crew I J K X 2 a b c d=0:= by
    simp only [Crew,roll, ← Finset.sum_add_distrib, ← smul_add]; apply Finset.sum_eq_zero; intro u _; apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro w _
    have ht:=(stations a [u] [v] [w] hx)
    exact Eq.trans (congrArg ((coin I u b * coin J v c * coin K w d) • ·) ht) (smul_zero _)
lemma rotate1 (a b c d): Crew I J K (castEye z x y) 1 a d b c=Crew J K I (castEye x y z) 0 a b c d := by
    unfold Crew roll
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro w _; apply Finset.sum_congr rfl; intro u _
    change (coin I u d*coin J v b*coin K w c) •yolk [u] [a,v] [w] _=(coin J v b*coin K w c*coin I u d) •yolk [a,v] [w] [u] _
    rw [twists]; ring
lemma rotate2 (a b c d): Crew I J K (castEye z x y) 2 a c d b=Crew K I J (castEye y z x) 0 a b c d := by
    unfold Crew roll
    symm; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _
    change (coin K w b*coin I u c*coin J v d) • yolk [a,w] [u] [v] _= (coin I u c *coin J v d*coin K w b) •yolk [u] [v] [a,w] _
    rw [twists]; ring

def pin := ∑ a, ∑ b, ∑ c,∑ d,low a b c d*Crew I J K X 0 a b c d
-- name arguments auto-lean order
lemma inspect (hx : castEye z x y∈ clearance 4) :
    street (Crew I J K (castEye z x y)) = 2 * (pin I J K (castEye z x y) + pin J K I (castEye x y z) + pin K I J (castEye y z x)) := by
  rw [ledger _ (crews I J K _ hx)]
  simp only [rum,pin,strum,rotate1,rotate2,mul_add,Finset.sum_add_distrib]

local notation "Piz" => Axis × Axis × Axis × Axis

def yard (i : Eye) (p : Piz) := fan false i p.1 p.2.1 * coin J p.2.2.1 p.1*coin K p.2.2.2 p.2.1
private lemma sums (f : Axis→Axis→Piz→ℝ) :
    (∑ a,∑ b,∑ p,f a b p)=∑ p,∑ a,∑ b,f a b p := by
      rw [show (∑ a,∑ b,∑ p,f a b p)=∑ a,∑ p,∑ b,f a b p from Finset.sum_congr rfl (fun a _=> Finset.sum_comm)]; rw [Finset.sum_comm]
private lemma signaled (i : Eye)(a b c d): fan false i a b * fan false i c d*Crew I J K X 0 a b c d=∑ u, ∑ v,∑ w,fan false i a b*coin I u b*(yard J K i (c,d,v,w)*yolk [a,u] [v] [w] X) := by
  simp only [Crew,roll,Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro w _; unfold yard
  change _*((coin I u b*coin J v c*coin K w d)*yolk [a,u] [v] [w] X)=_; ring
lemma pile (i : Eye) :
    (∑ a,∑ b,∑ c,∑ d,fan false i a b*fan false i c d*Crew I J K X 0 a b c d) = -(∑ p:Piz,yard J K i p*central I.1 I.2 false i [p.2.2.1] [p.2.2.2] X) := by
  let F (p : Piz) (a b u):= fan false i a b *coin I u b *(yard J K i p*yolk [a,u] [p.2.2.1] [p.2.2.2] X)
  have hm a b c d : fan false i a b*fan false i c d*Crew I J K X 0 a b c d=∑ v,∑ w,∑ u,F (c,d,v,w) a b u := by
    rw [signaled,Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_comm]
  simp only [hm]
  rw [show (∑ a,∑ b,∑ c : Axis,∑ d,∑ v,∑ w,∑ u,F (c,d,v,w) a b u)=∑ p:Piz,∑ a,∑ b,∑ u,F p a b u by rw [←sums (fun a b p=> ∑ u,F p a b u)]; simp only [Fintype.sum_prod_type]]
  rw [←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro p _
  simp only [central,mul_neg,neg_neg]; rw [Finset.sum_comm (f:=fun u (a:Axis)=>rotatedProduct I.1 I.2 false i u a * yolk [u,a] [p.2.2.1] [p.2.2.2] X)]
  simp only [rotatedProduct,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro b _
  unfold F coin; rw [Storm.commute X]; ring

lemma ridge : pin I J K X = -(∑ i:Eye,∑ p:Piz,yard J K i p*central I.1 I.2 false i [p.2.2.1] [p.2.2.2] X):= by
  unfold pin low; simp_rw [Finset.sum_mul]

  have hp:= Finset.sum_comm (s:=(Finset.univ:Finset (Piz))) (t:= (Finset.univ:Finset Eye)) (f:=fun p i=> fan false i p.1 p.2.1*fan false i p.2.2.1 p.2.2.2 *Crew I J K X 0 p.1 p.2.1 p.2.2.1 p.2.2.2)
  simp only [Fintype.sum_prod_type] at hp
  rw [hp]; simp only [pile, Finset.sum_neg_distrib]
end YM.SchemeRG11.Flare
