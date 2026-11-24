import YM.Integration.WilsonIndependentExactPlate
import YM.Integration.WilsonPositionProgramInfraredCircuit

/-! A common auxiliary side for a physical sequence and a two-length sequence, with the original initial residue. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalHelperShape
open Lattice RG RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger
open WilsonIndependentEvenPassport (power)
variable {X:Type}(V:XSpace.Run)(E r:X → ℕ)(a:ℕ)

def length (x:X):ℕ:=(E x-r x)/a
def remainder (x:X):ℕ:=(E x-r x)%a
def expo (p:Page (length E r a)):ℕ:=
  remainder E r a p.bindW + a*(length E r a p.bindW-p.downW)+(if p.downW=0 then r p.bindW else 0)
def n (p:Page (length E r a)):Side:=
  ⟨V.finalSide.side.val*V.ratio^(expo E r a p),Nat.mul_pos V.finalSide.side.pos (V.den_pos _)⟩
def edge (f:Flap (length E r a)):Side:=power V (if f.offset=0 then a+r f.volW else a)

theorem opening (old:∀x,r x≤E x)(x:X):
    n V E r a (Page.opening _ x)=V.finalSide.side*power V (E x):=by
  apply Subtype.ext
  change V.finalSide.side.val*V.ratio^_=V.finalSide.side.val*V.ratio^(E x)
  congr 2
  change (E x-r x)%a + a*((E x-r x)/a-0)+r x=E x
  rw [Nat.sub_zero,Nat.mod_add_div,Nat.sub_add_cancel (old x)]

theorem terminal (enough:∀x,0<length E r a x)(x:X):
    n V E r a (Page.finallyW _ x)=V.finalSide.side*power V (remainder E r a x):=by
  apply Subtype.ext
  change V.finalSide.side.val*V.ratio^_=V.finalSide.side.val*V.ratio^(remainder E r a x)
  congr 2
  change _ + a*(length E r a x-length E r a x)+(if length E r a x=0 then _ else _)=_
  simp only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,(enough x).ne',if_false]
  rfl

theorem seats (f:Flap (length E r a)):n V E r a f.prev=n V E r a f.next*edge V E r a f:=by
  have gap:length E r a f.volW-f.offset=length E r a f.volW-(f.offset+1)+1:=by
    have:=f.ok;omega
  have step:expo E r a f.prev=expo E r a f.next+(if f.offset=0 then a+r f.volW else a):=by
    simp only [expo,Flap.prev,Flap.next,Nat.add_one_ne_zero,if_false,Nat.add_zero,gap,Nat.mul_succ]
    by_cases z:f.offset=0 <;> simp only [z,if_true,if_false] <;> omega
  apply Subtype.ext
  change V.finalSide.side.val*V.ratio^(expo E r a f.prev)=V.finalSide.side.val*V.ratio^(expo E r a f.next)*V.ratio^_
  rw [step,pow_add,mul_assoc]

def physical (j:X → ℕ)(w:X → ℕ → ℕ)(x:X):ℕ:=WilsonPositionProgramCommonWindow.elapsed (w x) (j x)

theorem common (j:X → ℕ)(w:X → ℕ → ℕ)(old:∀x,r x≤physical j w x)(x:X):
    n V (physical j w) r a (Page.opening _ x)=WilsonPositionProgramInfraredCircuit.count V j w (Page.opening _ x):=by
  rw [opening V _ r a old]
  rfl

end YM.Integration.WilsonOriginalPublicNodalHelperShape
end
