import YM.MS.Puff.Euler
import YM.MS.Puff.Jet
/-!
# Exponentiating the finite relations lifted through distinct markers and cycles

Let E be the even part, θ a power operation `C`. We define exp(B) using the grading cap
(failing normal definition if B_0≠0). Σ robust associativity. For solutions whose currents
 obey B' = L B + 1/2 C(B,B), prove exp is linear flow by differentiating the terms through
 one spare order in necessary grade; version at diagonal `F` scalar evaluated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve
open scoped Topology ContDiff Interval
variable {I J E : Type} [AddCommGroup E][Module ℂ E]
variable {M:Actors E}
structure Dynamics (M:Actors E) where
    valid : E → E→ Prop
    mono : valid M.unit 0
    empty : valid 0 0
    plus x y u v: valid x u→valid y v→valid (x+y) (u+v)
    price x y (c:ℂ): valid x y→ valid ( c • x ) ( c • y )
    duop x y u v: valid x u → valid y v→ valid ( M.core x y ) ( M.core u y + M.core x v )
variable (P:SplitP I)
namespace Actors
variable (M)(B:E)
local infix:70 " ⋆ " => M.core
-- raw factorial powers, to keep arithmetic out of budgets.Mk
lemma p_well (hp:B ∈ M.guard)(k:ℕ): M.power B k∈ M.guard := by induction k with| zero=> exact M.holds | succ k ih=> exact M.close _ hp _ ih
-- graded power sums
section eval
local notation "gP"=> M.stack P
variable (b:I→E)
abbrev Happy (b:I→E):= b P.origin=0
include P M
lemma pole (h:Happy P b){k:ℕ}{a:I}(hx:P.grade a<k): (gP).power b k a=0:= by
   induction k generalizing a with
   | zero=> omega
   | succ k IH=>
      change ∑ i∈P.pieces a,b i.1 ⋆ ((gP).power b k i.2)=0; refine Finset.sum_eq_zero fun i hi=>?_ ; by_cases he:P.grade i.2<k; rw [IH he,map_zero]; obtain hh:=P.pays hi; rw [show i.1=P.origin from ( P.zeroC i.1 ).mp (by omega), (show b P.origin=0 from h),map_zero]; rfl
include b
lemma overbook (h:Happy P b){n:ℕ}{x:I}(hx:P.grade x ≤ n): (gP).cheers b n x=Cheer M P b x:= by
   rw [Cheer]; unfold cheers; rw [Finset.sum_apply,Finset.sum_apply]; symm; apply Finset.sum_subset ?_ (fun i hi he=>?_); · exact Finset.range_mono (by omega)
   unfold wages; rw [Pi.smul_apply,pole M P b h (by simp at he hi; omega),smul_zero]
end eval
end Actors
namespace Dynamics
variable (V:Dynamics M) {B:E}
lemma continueF {f g:I→E} (s:Finset I)(h:∀ i∈s,V.valid (f i) (g i)): V.valid (∑ i∈s,f i) (∑ i∈ s,g i) := by classical induction s using Finset.induction_on with| empty=> simpa using V.empty| insert i s hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact V.plus _ _ _ _ (h i (by simp)) ( ih fun j hj=> h j (Finset.mem_insert_of_mem hj) )
-- lift

def extrapolate : Dynamics (M.stack P):={
   valid f g:= ∀ i, V.valid (f i) (g i)
   empty _:=V.empty -- fails field expects valid syntax
   mono i := by unfold Actors.stack; dsimp only; unfold SplitP.refineV; split; exact V.mono; exact V.empty
   price _ _ u h i:= V.price _ _ u ( h i )
   plus _ _ _ _ h ht i:= V.plus _ _ _ _ ( h i ) ( ht i )
   duop x y u v h he i:= by
      change V.valid ( P.Lift M.core x y i ) ((P.Lift M.core u y i) + P.Lift M.core x v i);
      rw [ P.loan,P.loan,P.loan, ← Finset.sum_add_distrib ]; exact V.continueF _ (fun j _=> V.duop _ _ _ _ ( h j.1 ) ( he j.2 )) }
-- prove for engine K. let G = 1/2 Conn.W.
local infix:70 " ⋆ " => M.core
variable (K:Engine M)(c:E)
local notation "d"=> ((2:ℂ)⁻¹) • K.join c c
local notation "A"=> K.move c+d
open Actors Engine
variable (hc:c∈ M.guard)(hp: V.valid c A)
include hc
lemma line_wage (n:ℕ) (x:E)(hx:x∈M.guard): K.join x (M.power c (n+1))=(n+1:ℂ) • ( K.join x c ⋆ M.power c n ):= by
    induction n with
    | zero=> simp only [Actors.power]; rw [ M.identityR,M.identityR]; simp -- change n=0
    | succ n ih=>
        let a:= K.join x c; let D:= M.power c n; have h:c ⋆ (a ⋆ D)=a ⋆ (c ⋆ D):= by rw [ ← M.star_a, ← M.star_a,M.turns _ hc _ (K.join_close hx hc) ];
        rw [show M.power c (n+1+1)=c ⋆ M.power c (n+1) from rfl, K.leib _ _ _ hx hc (M.p_well c hc _), ih ]; -- `power` arg
        change (a ⋆ M.power c _) + c ⋆ _ = _; rw [ map_smul, h,power ]; -- `← def`
        module -- inspect
lemma join_wage (n:ℕ) (x:E)(hx:x∈M.guard): K.join x ( M.wages c (n+1) )= K.join x c ⋆ M.wages c n:= by
   unfold wages; rw [map_smul,line_wage K c hc n x hx, map_smul ]; -- syntax
   rw [smul_smul]; have hT : phase (n+1)*(n+1:ℂ)=phase n:= by unfold phase; rw [Nat.factorial_succ]; push_cast; field_simp; -- nonzero
   rw [hT]
end Dynamics
end YM.MS.Puff
