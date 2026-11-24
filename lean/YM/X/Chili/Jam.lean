import YM.X.Chili.Virgin
import YM.X.Chili.Cake
/-!
# Resummations at local aperture. Handle apparent motions by directions at opposite pace.
Jar generic ∗finite∗ programs (not completed).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark Tensor Ocean
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d w:ℕ} {G:Gauge} {R T':ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
def glass (a:Mist ℂ): Deck G:= fun i z=> C (a i z)
theorem glass₁ (h:Mist ℂ)(p:Deck G): glass h * p = fun i z=> h i z • p i z:= funext fun i=> funext fun z=> MvPolynomial.C_mul' ..
lemma bottles {f:Mist ℂ}(h:Visa q R 0 (-(n:ℤ)) f)(hx:k≤n)(hq:1<q.val)(hr:R≥0):Visa q R 0 (-(k:ℤ)) f:= Visa.stretch hq h hr le_rfl (by omega)
inductive Jar (b:Bool)(G:Gauge)(q:ℕ+)(R:ℝ): ℕ→Deck G→Prop where
   | glass (n:ℕ)(f:Mist ℂ) : Visa q R 0 (-(n:ℤ)) f → Jar b G q R n (Clove.glass f)
   | letter (k n:ℕ)(p:Fan G)(q':Deck G): p∈Reed.grads G k → Jar b G q R n q' →Jar b G q R (k+1+n) (fresh b p*q')
   | add {p s:Deck G}{n:ℕ}: Jar b G q R n p → Jar b G q R n s→ Jar b G q R n (p+s)
   | weaken {k n:ℕ}{p:Deck G}: Jar b G q R n p → k≤n → Jar b G q R k p
variable (b:Bool)
lemma jar_glass {f:Mist ℂ}{n:ℕ}(h:Visa q R 0 (-(n:ℤ)) f){p:Deck G}{k:ℕ}(he:Jar b G q R k p) :Jar b G q R (n+k) (glass f*p):= by
   induction he with
   | glass m g hg=> have hp : Visa q R 0 (-((n+m:ℕ):ℤ)) (f*g):= by simpa [add_comm] using h.mulC hg
                    rw [show glass f*glass (G:=G) g=glass (f*g) from funext fun t=> funext fun z=> (map_mul MvPolynomial.C (f t z) (g t z)).symm]; exact Jar.glass _ _ hp
   | letter k m s p hf hp IH=> rw [mul_left_comm,show n+(k+1+m)=k+1+(n+m) by omega]; exact Jar.letter k (n+m) s _ hf IH
   | add x y ih ii=> rw [mul_add]; exact Jar.add ih ii
   | weaken h hk IH=> exact IH.weaken (Nat.add_le_add_left hk n)
namespace Jar
variable {b} {p s : Deck G}
lemma plus (h:Jar b G q R n p)(hp:Jar b G q R m s): Jar b G q R (n+m) (p*s):= by
    induction h with
    | glass n f h=>exact jar_glass _ h hp
    | letter k n x p h ht ih=> rw [mul_assoc,Nat.add_assoc (k+1)]; exact letter k _ _ _ h ih
    | add x y a d=> rw [add_mul];exact add a d
    | weaken x h ib=> exact weaken ib (Nat.add_le_add_right h m)
lemma unit : Jar b G q R 0 (1:Deck G):= by rw [show (1:Deck G)= Clove.glass (1:Mist ℂ) from funext fun i=> funext fun x=> (map_one MvPolynomial.C).symm]; exact Jar.glass _ _ (by simp only [Nat.cast_zero, neg_zero]; exact Visa.fix (1:ℂ))
lemma fume (f:Fan G)(hf:f∈Reed.grads G k): Jar b G q R (k+1) (fresh b f):= by rw [← mul_one (fresh b f)]; exact Jar.letter k 0 f _ hf unit
lemma scale (a:ℂ)(h:Jar b G q R n p): Jar b G q R n (a • p):= by
    rw [show a • p= Clove.glass (Once (fun _:ℕ=>a))*p from (glass₁ ..).symm]; rw [← Nat.zero_add n]; exact jar_glass _ (show Visa q R 0 (-((0:ℕ):ℤ)) _ from Visa.fix a) h
lemma zero (n:ℕ):Jar b G q R n (0:Deck G):= by rw [show (0:Deck G)= Clove.glass 0 from funext (fun i=>funext fun z=> (map_zero MvPolynomial.C).symm)]; exact Jar.glass n _ Visa.zero
lemma sub (h:Jar b G q R n p)(ht:Jar b G q R n s):Jar b G q R n (p-s):= by rw [sub_eq_add_neg, ← neg_one_smul ℂ]; exact h.add (ht.scale _)
lemma fin {I:Type*}{f:I→Deck G}(w:Finset I)(h:∀ i∈w,Jar b G q R n (f i)): Jar b G q R n (∑ i∈w,f i):= by induction w using Finset.induction_on with | empty=>rw [sum_empty]; exact zero n| insert i w hi ih=> rw [sum_insert hi]; exact (h i (by simp)).add (ih (fun j hj=>h j (by simp [hj])))
end Jar
variable {b}{A:ℕ→Brush G} {B:Rich G} {P:Deck G}
include hq
lemma Jar.read (hr:0≤R)(hp:R<T')(h:Tide q T' A)(ht:Grasp B)(hb: Fill (gate q T') (fun i=> epsilon q i^(d+1)) d 0 A (emerge q B))(p:Jar b G q R n P): Grove q R A B d n P:= by
    induction p with
    | glass n f hf=>exact Grove.constant hf
    | letter k n x p hg hp' IH=> exact Grove.mul hq hr ht (fresh_grove hq b hr hp h ht hb x hg) IH
    | add a c ma mb=> exact Submodule.add_mem (grove q R A B d _) ma mb
    | weaken h hk IH=>exact Grove.weaken hq IH hr hk
end YM.PositionX.Clove
