import YM.OPE.Compatible.Slope.Value
import YM.Planned.PRIMARY_INTEGRAL_295.Paint
/-!
# Soft moment algebra for repeatable powers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r n j k:ℕ} {L:Side} {η x U a:ℝ} {X:Lines L}
lemma odds (p:Lieu (Keys r))(u: Keys r) (a:ℝ) : (fun x:Lieu (Keys r)=> (a• x+p) u)∈Flavor (Keys r) 1:= (Flavor _ _).add_mem ((Flavor _ _).smul_mem a (flavor_position u)) (flavor_cast _ _)
lemma wedge_input (p:Shift (Keys r))(x:Shift (Keys r)) : translit (x+p)=translit x+translit p:=by ext; simp [translit]
def tasteE (l:List (Keys r))(i:Fin r) :List Axis := trances _ i l
lemma topping (l:List (Keys r))(x:Lieu (Keys r)) : tasting l x=∏ i:Fin r,tasting (tasteE l i) (curry x i):=by
   induction l with
   | nil=>simp [tasteE,trances,tasting]
   | cons i l ih=>
      obtain ⟨j,y⟩:=i; change x (j,y)*tasting l x=_; rw [ih]
      let q (i:Fin r):=tasting (tasteE l i) (curry x i); let w i:=tasting (tasteE ((j,y)::l) i) (curry x i)
      have hh i(hi:i∈univ.erase j):w i=q i:=by simp [w,q,tasteE,trances,ne_of_mem_erase hi]
      rw [← Finset.mul_prod_erase _ q (mem_univ j),← Finset.mul_prod_erase _ w (mem_univ j),prod_congr rfl hh, show w j = x (j,y)*q j by simp [w,q,tasteE,trances,tasting],mul_assoc]
-- one leg
lemma tastePower (l:List Axis) (x:E4): ∏ i:Fin l.length, (EuclideanSpace.proj (𝕜:=ℝ) (l.get i)) x=tasting l (fun i=> x i):=by
    induction l with
    | nil=>simp [tasting]
    | cons i l ih=>
      change (∏ j:Fin (l.length+1), _) = x i* tasting l (fun i=> x i)
      rw [Fin.prod_univ_succ, ← ih]; rfl
variable {G:Gauge}{v:ℝ}{P: Flight j k} (hk:4≤k)(hp:0<v)
local notation "L!"=> linesOf P v
local notation "M"=> P.L
include hp hk
lemma guise (l:List Axis)(h:l.length<j) (a b:Axis) (x:Cover):
   let p:=translit x; let u:ℝ:= (P.L.val:ℝ)⁻¹
   (∑' y,fling L! a b x y*tasting l (translit y))=∑' y: Cover, fling L! a b 0 y *tasting l (u • p + translit y):=by
       intro p u
       let y:= cellar M x
       rw [← (Equiv.addLeft y).tsum_eq]
       have hh:= axes_eq v hp P hk x a b (fun i=> EuclideanSpace.proj (l.get i)) h
       dsimp only at hh
       calc
         _ = ∑' z,member L! x a b z * ∏ i:Fin l.length, (EuclideanSpace.proj (𝕜:=ℝ) (l.get i)) (Place.seat (y+z)):= tsum_congr fun z=>by
             unfold fling; rw [show Equiv.addLeft y z-cellar P.L x=z from add_sub_cancel_left .. ,tastePower]; rfl
         _ = _:= hh.trans (tsum_congr fun z=> by rw [tastePower]; unfold fling; rw [zero_cellar,sub_zero]; rfl)
end YM.OPE.Flume
