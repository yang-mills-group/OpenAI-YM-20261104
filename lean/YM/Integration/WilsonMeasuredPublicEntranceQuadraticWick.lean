import YM.Next.MAXWELL.Triangle

/-! Complete connected contractions for three genuinely distinct, independently marked
Wick quadratics. All eight cross-pairings are retained with their actual signs. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticWick
open Maxwell Maxwell.Free Maxwell.Wick
open scoped Classical BigOperators
variable {G:Gauge}

def cycle {ι K:Type*}[CommRing K](xy xz yz:ι→ι→K)(a a' b b' c c':ι):K:=
    xy a b * xz a' c * yz b' c' +
    xy a b * xz a' c' * yz b' c +
    xy a b' * xz a' c * yz b c' +
    xy a b' * xz a' c' * yz b c +
    xy a' b * xz a c * yz b' c' +
    xy a' b * xz a c' * yz b' c +
    xy a' b' * xz a c * yz b c' +
    xy a' b' * xz a c' * yz b c

theorem original {x y z:E4}(xy:x≠y)(xz:x≠z)(yz:y≠z)
    (a a' b b' c c':Factor G):
    triangle G x y z (letter a*letter a') (letter b*letter b') (letter c*letter c')=
      cycle (fun p q=>linkEntry (x,p) (y,q)) (fun p q=>linkEntry (x,p) (z,q))
        (fun p q=>linkEntry (y,p) (z,q)) a a' b b' c c':=by
  let tags:Fin 4→Fin 2:=![0,0,1,1]
  let factors:Fin 4→Factor G:=![b,b',c,c']
  let listed:List (Fin 4):=[0,1,2,3]
  let lower:Fin 2→WickPol G:=Fin.cons (letter b*letter b') (fun _=>letter c*letter c')
  have law:lower=bag tags factors listed:=by
    ext1 i
    fin_cases i <;> simp [lower,bag,tags,factors,listed]
  rw [tri_eval]
  change moment G (Points.cons x (pairPoints y z)) (Fin.cons _ lower)=_
  rw [law,show letter a*letter a'=([a,a'].map letter).prod by simp,
    planted _ _ _ _ _ (tri_ok xy xz yz)]
  change pairCost linkEntry [(x,a),(x,a'),(y,b),(y,b'),(z,c),(z,c')]=_
  simp only [pair_step,pulls_cons,pulls_nil,zero_mul,mul_zero,add_zero,zero_add,link_zero]
  rw [pairCost]
  unfold cycle
  ring
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticWick

