import YM.Integration.WilsonIndependentEvenPassport
import YM.RegulatorIR.Oracle.Arrange

/-! The two-length passport has the prescribed Wilson torus and an exact measuring page in the original units. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentExactPlate
open Lattice RG XSpace RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonIndependentEvenPassport (power count old young)
open scoped Classical BigOperators
variable (V:XSpace.Run)(a:ℕ)

abbrev Requests (a:ℕ) := Subtype (fun i : ℕ => a ≤ i)
def M := fun i:Requests a => count V a i.val
def outer (i:Requests a) := (V.reserve*i.val*i.val)%a
def residue (i:Requests a) := i.val%a

def exp (p:Page (M V a)) :=
  outer V a p.bindW + a*(M V a p.bindW-p.downW) + if p.downW=0 then residue a p.bindW else 0

def n (p:Page (M V a)):Side :=
  ⟨V.finalSide.side.val*V.ratio^(exp V a p),
    Nat.mul_pos V.finalSide.side.pos (V.den_pos _)⟩

def sizeL (f:Flap (M V a)):Side:=power V (if f.offset=0 then a+residue a f.volW else a)
def stage (j:ℕ) (p:Page (M V a)):= if p.downW=0 then j+1 else j

theorem starting (i:Requests a) : n V a (Page.opening (M V a) i)=(V.step i.val).p.side := by
  apply Subtype.ext
  have f:=Nat.mod_add_div i.val a
  have g:=Nat.mod_add_div (V.reserve*i.val*i.val) a
  change V.finalSide.side.val*V.ratio^_=V.finalSide.side.val*V.ratio^(i.val+V.reserve*i.val*i.val)
  congr 2
  change (V.reserve*i.val*i.val)%a + a*((V.reserve*i.val*i.val)/a + i.val/a) + i.val%a = _
  rw [Nat.mul_add]
  omega

private theorem tier (f:Flap (M V a)) :
   exp V a f.prev=exp V a f.next+(if f.offset=0 then a+residue a f.volW else a):=by
  have gap : M V a f.volW-f.offset=M V a f.volW-(f.offset+1)+1 := by have:=f.ok;omega
  simp only [exp,Flap.prev,Flap.next,Nat.add_one_ne_zero,if_false,add_zero,gap,Nat.mul_succ]
  by_cases h:f.offset=0 <;> simp only [h,if_true,if_false] <;> omega

theorem seats (f:Flap (M V a)) : n V a f.prev=n V a f.next*sizeL V a f := by
  apply Subtype.ext
  change V.finalSide.side.val*V.ratio^(exp V a f.prev)=V.finalSide.side.val*V.ratio^(exp V a f.next)*V.ratio^_
  rw [tier,pow_add,mul_assoc]

def S (ha:0<a)(j:ℕ)(hj:4≤j) : Circuit (M V a) (n V a) where
  l p:= ((V.step p.bindW.val).p.side.val:ℝ)/(n V a p).val
  P i:=((V.step i.val).p.side.val:ℝ)
  sizeL:=sizeL V a
  J:=stage V a j
  seats:=seats V a
  odd f:=V.odd.pow
  holds f:=by
    apply V.large.trans (Nat.le_self_pow _ _)
    split_ifs <;> omega
  stands p:= V.finalSide.large.trans (Nat.le_mul_of_pos_right _ (V.den_pos _))
  dual p:=even_iff_two_dvd.mpr (dvd_mul_of_dvd_left V.finalSide.even _)
  week p:=by dsimp [stage];split_ifs <;> omega
  shakes f:=by simp only [stage,Flap.next,Flap.prev,Nat.add_one_ne_zero,if_false];split_ifs <;> omega
  slow f:=by simp only [stage,Flap.next,Flap.prev,Nat.add_one_ne_zero,if_false];split_ifs <;> omega
  l_p p:=div_pos (by exact_mod_cast (V.step p.bindW.val).p.side.pos) (by exact_mod_cast (n V a p).pos)
  comet p:=div_mul_cancel₀ _ (by exact_mod_cast (n V a p).pos.ne')

def report (i:Requests a):Page (M V a):=⟨i,young a i.val,Nat.le_add_left _ _⟩

theorem count_report (ha:0<a)(i:Requests a):
    (n V a (report V a i)).val=V.finalSide.side.val*V.ratio^(V.reserve*i.val*i.val) := by
  have hi : (0 : ℕ) < (i : ℕ) / a :=Nat.div_pos i.property ha
  have rem:=Nat.mod_add_div (V.reserve*i.val*i.val) a
  change V.finalSide.side.val*V.ratio^(exp V a (report V a i))=_
  congr 2
  simp only [exp,report,M,count,Nat.add_sub_cancel,young,old,outer,ne_of_gt hi,if_false,add_zero]
  exact rem

theorem units (ha:0<a)(j:ℕ)(hj:4≤j)(i:Requests a) :
    (S V a ha j hj).l (Page.opening (M V a) i)=1 ∧
    (V.step i.val).spacing*(S V a ha j hj).l (report V a i)=1 := by
  constructor
  · change ((V.step i.val).p.side.val:ℝ)/((n V a (Page.opening _ i)).val:ℝ)=1
    rw [starting,div_self (by exact_mod_cast (V.step i.val).p.side.pos.ne')]
  · change (↑(V.ratio^i.val):ℝ)⁻¹ * (((V.step i.val).p.side.val:ℝ)/(n V a (report V a i)).val)=1
    rw [count_report V a ha]
    change (↑(V.ratio^i.val):ℝ)⁻¹ * ((↑(V.finalSide.side.val*V.ratio^(i.val+V.reserve*i.val*i.val)):ℝ)/_)=1
    have pos : 0<(V.ratio:ℝ):=by exact_mod_cast (by have:=V.large;omega:0<V.ratio)
    have term : 0<(V.finalSide.side.val:ℝ):=by exact_mod_cast V.finalSide.side.pos
    push_cast
    rw [pow_add]
    field_simp [pos.ne',term.ne']

end YM.Integration.WilsonIndependentExactPlate
