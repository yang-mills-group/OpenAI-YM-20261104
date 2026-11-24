import YM.PertExtension.OrbExpansion
import YM.Integration.WilsonMaxwellThermometerWardConditional

/-! The two copies of a bulk change in the even inversion regulator carry one
ordinary Wilson weight. Use the four actual bonds of every plaquette. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardReflection
open Function Set Filter MeasureTheory Lattice Wilson PertExtension.Orb
open WilsonMaxwellThermometerWardConditional
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side}

def mirror (U:Config G n) : Config G n :=fun e=>(U (reflect e))⁻¹

private theorem mirrored (U:Config G n) : energy (mirror U)=energy U := by
  let s:Signed:=⟨Equiv.refl _,fun _=>true⟩
  have aff (x:Site n) : affine s 0 x = -x := by
    rw [affine,add_zero]
    ext1 i
    simp [s,Signed.act]
  have same:mirror U=pull s 0 U:=by
    funext e
    rw [pull,aff]
    rfl
  rw [same,energy_pull]

def rim (p:Face (Per n)) : Finset (Edge (Site n)) :=
  {(p.1,p.2.val.1),(p.1+step p.2.val.1,p.2.val.2),
   (p.1+step p.2.val.2,p.2.val.1),(p.1,p.2.val.2)}

private theorem square_value (U:Config G n) (p:Face (Per n)) :
    faceValue U p=U (p.1,p.2.val.1)*U (p.1+step p.2.val.1,p.2.val.2)*
      (U (p.1+step p.2.val.2,p.2.val.1))⁻¹*(U (p.1,p.2.val.2))⁻¹:=by
  rcases p with ⟨x,⟨⟨i,j⟩,h⟩⟩
  simp [faceValue,square,travel,mul_assoc]
  congr 4 <;> abel

theorem same_face {U V:Config G n} (p:Face (Per n))
    (h:∀ e∈rim p,U e=V e): faceValue U p=faceValue V p:=by
  rw [square_value,square_value,h _ (by simp [rim]),h _ (by simp [rim]),
    h _ (by simp [rim]),h _ (by simp [rim])]

/-- No physical plaquette crosses from the source collar to its
inversion image. This is tested before taking a tree or changing beta. -/
def Clear (r:ℕ) (o:Site n):Prop:=∀p:Face (Per n),
  (∀ e∈rim p,far r o e) ∨ (∀e∈rim p,far r o (reflect e))

def single (r:ℕ) (o:Site n) (U:Config G n) (v:Free G r o):Config G n :=
  (chamber r o).symm (((chamber r o) U).1,v)

def twins (r:ℕ) (o:Site n) (U:Config G n) (v:Free G r o):Config G n :=
  fun e=>if far r o e then mirror (single r o U v) e else single r o U v e

theorem held (r:ℕ) (o:Site n) (U:Config G n) (v:Free G r o)
    (e:Edge (Site n)) (h:far r o e):single r o U v e=U e:=by
  change (if h:far r o e then U e else v ⟨e,h⟩)=U e
  rw [dif_pos h]

theorem energy_bill (r:ℕ) (o:Site n) (legal:Clear r o) (U:Config G n)
    (fixed:mirror U=U) (v:Free G r o) :
    energy (twins r o U v)+energy U=2*energy (single r o U v) := by
  let A:=single r o U v
  let T:=twins r o U v
  have both (p:Face (Per n)):
      G.price (faceValue T p)+G.price (faceValue U p)=
      G.price (faceValue A p)+G.price (faceValue (mirror A) p):=by
    rcases legal p with left|right
    · have a:faceValue A p=faceValue U p:=same_face p (fun e he=>held r o U v e (left e he))
      have t:faceValue T p=faceValue (mirror A) p:=same_face p fun e he=>if_pos (left e he)
      rw [t,a,add_comm]
    · have back (e:Edge (Site n)) (he:e∈rim p):mirror A e=U e:=by
        have h:=held r o U v (reflect e) (right e he)
        exact (congrArg Inv.inv h).trans (congrFun fixed e)
      have a:faceValue (mirror A) p=faceValue U p:=same_face p back
      have t:faceValue T p=faceValue A p:=same_face p fun e he=>by
        by_cases h:far r o e
        · exact (if_pos h).trans ((back e he).trans (held r o U v e h).symm)
        · exact if_neg h
      rw [t,a]
  calc
    _ = energy A+energy (mirror A) := by
      unfold energy
      rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _=>both p)
    _= _ := by rw [mirrored,two_mul]

theorem weight (r:ℕ) (o:Site n) (legal:Clear r o) (U:Config G n)
    (fixed:mirror U=U) (v:Free G r o) (β:ℝ) :
    bare (β/2) (twins r o U v) = Real.exp (β/2*energy U)*bare β (single r o U v) := by
  have h:=energy_bill r o legal U fixed v
  unfold bare
  rw [←Real.exp_add]
  congr 1
  linear_combination -(β/2)*h

end YM.Integration.WilsonMaxwellThermometerWardReflection
