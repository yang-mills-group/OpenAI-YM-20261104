import YM.X.Sage.Batch
/-!
# diagnostic color factor. unnormalized rational. ARITH equality scripted.S
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund Imprint
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ}{V I:Type*} {q:ℕ+} {n:Side} {r s e:ℝ}
local notation "U"=> G.ColorIndex
local notation "T"=>Tet
local notation "o"=> side q k
local notation "K"=> wrap o
local notation "ε"=>epsilon q k
local notation "Q"=>qu q G k
local notation "B"=>βDeck q G
local notation "W"=>μDeck q G
local notation "θ"=>BMark q G
local notation "μ"=>Umark q G
variable (Z X Y:Fielding.Walk)
local notation "x"=> transit q X k
local notation "y"=> transit q Y k
local notation "z"=> transit q Z k
local notation "Vτ"=> Settlement Z X Y θ μ μ
local notation "Iτ"=> ripple Z X Y W W θ
local notation "sf"=>4*count G
lemma chir_Class : Iτ k=↑(sf * (∑ i:T,tithe o ε 1 z x y z i i)):= by
    unfold ripple; push_cast; simp_rw [Finset.sum_apply, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; have he:=processors (G:=G) (q:=q) (k:=k) (Z k) (X k) (Y k) (Z k) i i 1; unfold spotK BMark; push_cast at he; exact he
local notation "Gτ"=> flock θ μ μ Z X Y
lemma flashJ (d:Site (side q k)) : Gτ k d= ↑(sf* ∑ p:T,∑ i:T,Wpp ε 1 p (-1) i o z d* tithe o ε (-1) z x y d p i):= by
     unfold flock; rw [Finset.sum_comm]; simp_rw [Finset.sum_apply,Pi.mul_apply]; rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun i p=> Wpp ε 1 i (-1) p o z d * tithe o ε (-1) z x y d i p)]; rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm,Complex.ofReal_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; rw [← Finset.mul_sum]; have he: (∑ a:U, Lapiz (t:=-1) μ ((BMark q G).shade p a) Z X Y i a μ k d)= ↑(sf*tithe o ε (-1) z x y d p i):= by
          simp_rw [← lofty]; have he:=processors (G:=G) (q:=q) (k:=k) (Z k) (X k) (Y k) (lift d) p i (-1); rw [wrap_lift] at he; exact he
     rw [he]; push_cast; change (Wpp ε 1 p (-1) i o z d:ℂ)* _=_; ring
-- move sums via per-arity arms scaling
variable (u v p i:Tet)
lemma engage (a t w:Site n):
  ∑ j:T,∑ l:T, segmentA n e a t w p j l * (∑ c:T,Union_z n e t w a c j l p)= e^4*∑ k:Site n,∑ i:T,Wpp e 1 p (-1) i n a k * tithe n e (-1) a t w k p i:= by
    let f(k:Site n)(i j l:T):= Wpp e 1 p (-1) i n a k*(segmentA n e a t w p j l*ester n e (-1) i j l t w k); let g(j:T)(k:Site n):=∑ i:T,∑ l:T,f k i j l; have he (j l i:T): segmentA n e a t w p j l * Union_z n e t w a i j l p=e^4*∑ k:Site n,f k i j l:= by unfold Union_z galley; rw [mul_left_comm, Finset.mul_sum]; apply congr_arg; apply Finset.sum_congr rfl; intro k _; unfold f; ring
    simp_rw [Finset.mul_sum (Finset.univ (α:=Tet)) (fun i:Tet=>Union_z _ _ _ _ _ i _ _ _) (_:ℝ), he, ← Finset.mul_sum (Finset.univ (α:=T)) _ (e^4), tithe]; apply congr_arg (e^4 * ·); simp_rw [Finset.mul_sum]; change _=∑ k:Site n,∑ i:T,∑ j:T,∑ l:T,f k i j l; -- LHS ∑ j l i k. commute.
    have ht(j l:T):∑ i:T,∑ k:Site n,f k i j l=∑ k:Site n,∑ i:T,f k i j l:= by rw [Finset.sum_comm];
    have hu(j:T): ∑ l:T,∑ k:Site n,∑ i:T,f k i j l =∑ k:Site n,g j k:= by rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold g; rw [Finset.sum_comm];
    simp_rw [ht,hu]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold g; rw [Finset.sum_comm]
def insideV (e:ℝ)(a t w:Site n):ℝ:= e^4 * ∑ k:Site n,∑ i:T,∑ l:T,Wpp e 1 i (-1) l n a k * tithe n e (-1) a t w k i l
lemma trion_bench (w a b:Site n): trion e a b w=(∑ p:T,tithe n e 1 w a b w p p)-insideV e w a b:= by
     unfold insideV; rw [Finset.sum_comm,Finset.mul_sum,← Finset.sum_sub_distrib]; unfold trion; refine Finset.sum_congr rfl fun i _=> ?_; rw [← engage]; unfold tithe segmentA; simp_rw [mul_sub, Finset.sum_sub_distrib]
-- PP class minus.
lemma assay : Iτ k-Vτ k=↑(sf*trion ε x y z):= by
    rw [chir_Class]; unfold Settlement crow; simp_rw [flashJ]; rw [trion_bench,mul_sub,Complex.ofReal_sub]; apply congr_arg (_- ·); unfold insideV; rw [mul_left_comm sf, Finset.mul_sum (Finset.univ (α:=Site (side q k)))]; push_cast; simp only [Finset.mul_sum,volS]
end YM.PositionX.Sage
