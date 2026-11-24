import YM.Integration.WilsonMaxwellThermometerPositionCurrency
import YM.Integration.WilsonMaxwellThermometerPublicHeads
/-! The literal graded reannouncement on the authentic registered frame, at
the voted finite signed position detector. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerVotedCurrency
open Function Finset Labels MvPolynomial Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open WilsonMaxwellThermometerChargedHeads WilsonMaxwellThermometerPositionCurrency
open WilsonMaxwellThermometerPublicEvenSlope WilsonMaxwellThermometerPublicGalop
open scoped Classical BigOperators
variable {G:Gauge}{d n:ℕ}(F:Labels.Frame G d)

theorem projection (i:F.Index):
    en (F.bound i) (Normalize.part d (F.grades i).1 (arm F i))=arm F i:=by
  apply Subtype.ext
  change _ = reduceEq (F.basis i).val
  apply IsWeightedHomogeneous.weightedHomogeneousComponent_same
  let v:=(F.basis i).val
  change IsWeightedHomogeneous scaleW (reduceEq v) (F.grades i).1
  nth_rw 1 [v.as_sum]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro l hl
  have wag:Finsupp.weight bidegree l=F.grades i:=(pure_grade _ _).mp (F.pure i) (MvPolynomial.mem_support_iff.mp hl)
  rw [weight_slot] at wag
  have grade:Finsupp.weight Labels.generation l=(F.grades i).1:=congrArg Prod.fst wag
  rw [←grade]
  exact bounded_grade generation scaleW reduceEq (reduce_grade (fun j=>j+2)) l _

def form (X:Sample n)(a:ℝ):Sec G d→ₗ[ℂ] Sec G d:=
  ∑j:Fin (d+1),((X.F.spacing:ℂ)^j.val/(a:ℂ)^d) •
    (en (Nat.le_of_lt_succ j.isLt)).comp (Normalize.part d j.val)

theorem applied (X:Sample n)(a:ℝ)(p:Sec G d):form X a p=received X a p:=by
  simp [form,received,LinearMap.sum_apply]

def pay (X:Sample n)(a:ℝ)(v:F.Coeff):F.Coeff:=
  fun i=>((X.F.spacing:ℂ)^(F.grades i).1/(a:ℂ)^d)*v i

theorem actual (X:Sample n)(a:ℝ)(v:F.Coeff):received X a (sector F v)=sector F (pay F X a v):=by
  have pure (i:F.Index):form X a (arm F i)=((X.F.spacing:ℂ)^(F.grades i).1/(a:ℂ)^d) • arm F i:=by
    rw [applied,←projection F i,received]
    let k:Fin (d+1):=⟨(F.grades i).1,Nat.lt_succ_of_le (F.bound i)⟩
    rw [Finset.sum_eq_single k]
    · rw [part_same]
    · intro j _ ne
      rw [part_other _ (mt Fin.ext ne),map_zero,smul_zero]
    · simp
  rw [←applied,summed,summed,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,pure,smul_smul,mul_comm]
  rfl

theorem maximal (X:Sample n)(a:ℝ)(v:F.Coeff):head F (pay F X a v)=
    head F (((X.F.spacing:ℂ)^d/(a:ℂ)^d) • v):=by
  funext i
  by_cases h:F.grades i=(d,d/2) <;> simp [head,pay,h,Pi.smul_apply]

theorem original (W:Initialize G){V:Normalize.Store G}(X:Sample 3)(a:ℝ)
    (simple:G.Simple)(stage:V.Meets W X.F 6)
    (H:Labels.Frame G 6)(L:Labels.Frame G 4)(b:H.Coeff)(u v:L.Coeff):
    node W (V:=V) X (entered (received X a (sector H b)) (received X a (sector L u))
      (received X a (sector L v)))=
    node W (V:=V) X (entered (sector H (head H (((X.F.spacing:ℂ)^6/(a:ℂ)^6) • b)))
      (sector L (head L (((X.F.spacing:ℂ)^4/(a:ℂ)^4) • u)))
      (sector L (head L (((X.F.spacing:ℂ)^4/(a:ℂ)^4) • v)))):=by
  rw [actual,actual,actual,WilsonMaxwellThermometerPublicHeads.original W X simple stage]
  simp only [maximal]

end YM.Integration.WilsonMaxwellThermometerVotedCurrency
end
