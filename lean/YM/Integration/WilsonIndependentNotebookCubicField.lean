import YM.Integration.WilsonIndependentNotebookOrdinaryBirth
import YM.Integration.WilsonIndependentMatchedTotalTop
import YM.WilsonCoeffUV.Product.Connected.FirstJoin

/-! Ordinary and connected cubic entries of one normalized conditional
Wilson step. Each pair is the native connected contraction on the entire
inherited vacuum, including the pair of the two unchanged fields. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookCubicField
open Lattice RG XSpace Precision WilsonCoeffUV WilsonCoeffUV.Mer
open scoped Classical
variable {G:Gauge}
structure Faces (G:Gauge) where
  proper:Era G ℝ
  ab:Era G ℝ
  ac:Era G ℝ
  bc:Era G ℝ
  connected:Era G ℝ

def Faces.birth (Z:Faces G):Era G ℝ:=Z.ab+Z.ac+Z.bc+Z.connected

/-- The centered third field uses the full conditional of the deposited
AB field against the changed C, then subtracts the two other pairings. -/
def issue (A:Levels G)(Ñ:ChartRatio G)(m N i j k:ℕ)(X Y D:Era G ℝ):Faces G:=
  let U:=verseI (V:=ℝ) A Ñ m N
  let gap:=JoinGap A Ñ m N
  let ab:=agateV (gap i j X Y) (U k D)
  let ac:=agateV (gap i k X D) (U j Y)
  let bc:=agateV (U i X) (gap j k Y D)
  ⟨agateV (agateV (U i X) (U j Y)) (U k D),ab,ac,bc,
   gap (i+j) k (agateV X Y) D-ac-bc⟩

theorem parts (A:Levels G)(Ñ:ChartRatio G)(m N i j k:ℕ)(X Y D:Era G ℝ):
    let Z:=issue A Ñ m N i j k X Y D
    verseI A Ñ m N (i+j+k) (agateV (agateV X Y) D)=Z.proper+Z.birth:=by
  intro Z
  let U:=verseI (V:=ℝ) A Ñ m N
  let xy:=agateV (U i X) (U j Y)
  let ab:=JoinGap A Ñ m N i j X Y
  have split:ab+xy=U (i+j) (agateV X Y):=by
    dsimp only [ab,JoinGap,xy,U]
    exact sub_add_cancel _ _
  have both:agateV (U (i+j) (agateV X Y)) (U k D)=agateV ab (U k D)+agateV xy (U k D):=by
    rw [←split]
    exact (WilsonIndependentMatchedTotalTop.binary ab xy (U k D)).1
  dsimp only [Z,issue,Faces.birth]
  change U (i+j+k) (agateV (agateV X Y) D)=agateV xy (U k D)+
    (agateV ab (U k D)+_+_+(U (i+j+k) (agateV (agateV X Y) D)-
    agateV (U (i+j) (agateV X Y)) (U k D)-_-_))
  rw [both]
  abel

/-- Every one of the five lower registers has the same true degree. -/
theorem admitted (A:Levels G){Ñ:ChartRatio G}{m N i j k:ℕ}{X Y D:Era G ℝ}
    (simple:G.Simple)(ratio:LocalRatio Ñ)(live:m<N)(x:Auth i X)(y:Auth j Y)(d:Auth k D):
    let Z:=issue A Ñ m N i j k X Y D;let h:=i+j+k
    Auth h Z.proper ∧ Auth h Z.ab ∧ Auth h Z.ac ∧ Auth h Z.bc ∧ Auth h Z.connected:=by
  intro Z h
  have moved {n:ℕ}{T:Era G ℝ}(t:Auth n T):Auth n (verseI A Ñ m N n T):=
    Auth.verse A live simple ratio t
  have joined {a b:ℕ}{T S:Era G ℝ}(ht:Auth a T)(hs:Auth b S):
      Auth (a+b) (JoinGap A Ñ m N a b T S):=
    (moved (ht.manor hs)).sub ((moved ht).manor (moved hs))
  have ac:Auth h Z.ac:=by
    change Auth (i+j+k) (agateV (JoinGap A Ñ m N i k X D) (verseI A Ñ m N j Y))
    rw [show i+j+k=i+k+j by omega]
    exact (joined x d).manor (moved y)
  have bc:Auth h Z.bc:=by
    change Auth (i+j+k) (agateV (verseI A Ñ m N i X) (JoinGap A Ñ m N j k Y D))
    rw [Nat.add_assoc]
    exact (moved x).manor (joined y d)
  exact ⟨((moved x).manor (moved y)).manor (moved d),(joined x y).manor (moved d),
    ac,bc,((joined (x.manor y) d).sub ac).sub bc⟩

end YM.Integration.WilsonIndependentNotebookCubicField
