import YM.MS.Arts.Range
import YM.MS.Arts.Column
/-!
# Rotating pilot and Sturdy families

Extension types include gauge color/natural covariance. Orthogonal pair traces computed later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot
open scoped Topology ContDiff
variable {G:Gauge}{A B C P:Type}[Fintype A][Fintype B][Fintype C]
 [DecidableEq A][DecidableEq B][DecidableEq C]{b:Bool}{m n k:ℕ}
namespace Spin
-- component complex points, exact

def shadow (K:Spin A): Option A→Option A→ℂ
| none, none=>1
| some i,some j=> K.profile i j
| _,_=>0

def rayS (K:Spin A)(i j: Atom A):ℂ:= if i.2=j.2 then shadow K i.1 j.1 else 0
def prop (K:Spin A)(i j:Leg A C):ℂ:= if i.2=j.2 then rayS K i.1 j.1 else 0
variable (C)
def leggo (K:Spin A): Pilot ℂ (Momentum A) (Landau.parity (C:=C) (A:=A)) where
   volp:= K.turn.toLinearEquiv.toAddEquiv
   fieldC:= K.prop
   pair_zero a b H:= by
       rcases a with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases b with ⟨⟨_|b,_|_⟩,j⟩ <;> simp [prop,rayS,shadow] at H <;> rfl

lemma chore (K:Spin A) (x:Legs (Mode (Leg A C) (Momentum A)))(f: Plane.Row (Leg A C) (Momentum A) ℂ) (i:Atom A)(c:C)(p:Momentum A): (leggo C K).beam f (((i,c),p)::x)= ∑ j:Atom A,K.rayS i j * (leggo C K).beam (Koszul.D ((j,c),K.turn p) f) x:= by rw [met]; unfold leggo; simp only [prop,Fintype.sum_prod_type,ite_mul,zero_mul]; simp -- result
variable {C}
lemma choreO (K:Spin A) (x:Legs (Mode (Leg A C) (Momentum A)))(f) i b (c:C)(p:Momentum A): (leggo C K).beam f (((( (i,b),c),p))::x)= ∑ j:Option A,K.shadow i j * (leggo C K).beam (Koszul.D (((j,b),c),K.turn p) f) x:= by rw [chore]; simp [rayS,Fintype.sum_prod_type,ite_mul]
lemma fromV (K:Spin A) (x:Legs (Mode (Leg A C) (Momentum A)))(f) (i:A) b (c:C)(p:Momentum A): (leggo C K).beam f (((( (some i,b),c),p))::x)= ∑ j:A, (K.profile i j:ℂ) * (leggo C K).beam (Koszul.D (((some j,b),c),K.turn p) f) x:= by rw [choreO]; simp [Fintype.sum_option,shadow]
lemma fromG (K:Spin A) (x:Legs (Mode (Leg A C) (Momentum A)))(f) b (c:C)(p:Momentum A): (leggo C K).beam f (((( (none,b),c),p))::x)= (leggo C K).beam (Koszul.D (((none,b),c),K.turn p) f) x:= by rw [choreO]; simp [Fintype.sum_option,shadow]

end Spin
abbrev moveG {P:Type}(T:P→Momentum A) := Landau.send (C:= G.ColorIndex) T -- G implicit unresolved maybe need specify
-- embed, prefix
variable (h:m≤n)
def flagS (X:Spin (L m))(G:Gauge):= Spin.leggo G.ColorIndex X
structure Sturdy (b:Bool)(F:Mob G): Prop where
    turn m (X:Spin (L m)): X.within b → (flagS X G).beam (F m)=F m
    grows {m n:ℕ}(h:m≤n) : ∀ i, F n (lift h i)=F m i
structure Ruddy (b:Bool)(U:Rip G): Prop where
    turn m (X:Spin (L m)): X.within b→ Transport (flagS X G) (U m) (U m)
    grows {m n:ℕ}(h:m≤n)(i j p): U n (embA (rises h) i) (embA (rises h) j) (Left h p)= U m i j p
-- Morph cost & Csyms later
variable {U:Rack G m}{F H:Mob G}
end YM.MS.Arts
