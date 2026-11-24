import YM.Integration.WilsonOriginalTwoFlatIRFlatPartitions
import YM.QCDContinuum.Sources.Dial

/-! Ordinary finite marked evaluation and the total-degree truncation of the
same genuine scalar series. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatPolynomial
open Finset Marker
open WilsonOriginalTwoFlatIRFlatPartitions (exponent row term crop)
open scoped Classical BigOperators
variable {V I:Type}[DecidableEq V][Fintype I]{J:Census V}{q:ℕ}

def lift (J:Census V):Poly J →+* Cargo J (PowerSeries ℂ) where
  toFun a:=Cargo.inject fun s=>PowerSeries.C (a.part s)
  map_one':=by
    apply Cargo.ext; intro s
    change PowerSeries.C ((1:Poly J).part s)=(1:Cargo J (PowerSeries ℂ)).part s
    rw [Poly.one_part,Cargo.one_part]; split <;> simp
  map_mul' a b:=by
    apply Cargo.ext; intro s
    change PowerSeries.C ((a*b).part s)=_
    rw [Poly.part_mul,Cargo.part_mul,map_sum]
    apply sum_congr rfl
    intro j _
    rw [map_sum]; apply sum_congr rfl
    intro k _; split <;> simp [Cargo.part,Cargo.inject]
  map_zero':=by
    apply Cargo.ext; intro s; change PowerSeries.C ((0:Poly J).part s)=0; simp
  map_add' a b:=by apply Cargo.ext; intro s; change PowerSeries.C ((a+b).part s)=_; rw [Poly.part_plus,map_add]; rfl

variable (m:I→J.Mode)(cash:I→Fin (q+1)→ℂ)
def degree : Option (Fin (q+1))→ℕ
  | none=>0
  | some j=>j.val
def deposit (j:I):PowerSeries ℂ:=∑h:Fin (q+1),
  (PowerSeries.X:PowerSeries ℂ)^h.val * PowerSeries.C (cash j h)
def declared : Cargo J (PowerSeries ℂ):=∏j,(1+Cargo.send (m j) (deposit cash j))

omit [Fintype I] in
private theorem factor (j:I):
    (1+Cargo.send (m j) (deposit cash j))=
      ∑u:Option (Fin (q+1)),(PowerSeries.X^(degree u):PowerSeries ℂ) • lift J (row m cash j u):=by
  rw [Fintype.sum_option]
  simp only [degree,row,pow_zero,one_smul,map_one]
  apply congrArg (1+·)
  apply Cargo.ext; intro s
  rw [Cargo.part_sum]
  simp only [Cargo.part_smul,smul_eq_mul,Cargo.part_send]
  change _=∑i:Fin (q+1),PowerSeries.X^i.val*PowerSeries.C ((Poly.send (m j) (cash j i)).part s)
  by_cases h:s=m j <;> simp [Poly.part_send,h,deposit]

theorem table (s:J.Mode):
    (declared m cash).part s=
      ∑w:I→Option (Fin (q+1)),(PowerSeries.X:PowerSeries ℂ)^(exponent w)*PowerSeries.C ((term m cash w).part s):=by
  unfold declared
  simp_rw [factor m cash,Fintype.prod_sum]
  rw [Cargo.part_sum]
  apply sum_congr rfl
  intro w _
  rw [Finset.prod_smul,Finset.prod_pow_eq_pow_sum,←map_prod,Cargo.part_smul]
  rfl

theorem coefficient (s:J.Mode)(h:ℕ):
    PowerSeries.coeff h ((declared m cash).part s)=
      ∑w:I→Option (Fin (q+1)),if exponent w=h then (term m cash w).part s else 0:=by
  rw [table,map_sum]
  apply sum_congr rfl
  intro w _
  rw [PowerSeries.coeff_mul_C,PowerSeries.coeff_X_pow]
  by_cases eq:exponent w=h
  · subst h; simp
  · simp [eq,Ne.symm eq]

theorem original (g:ℂ)(p:ℕ)(s:J.Mode):
    (crop m cash g p).part s=
      ∑h∈range (p+1),g^h*PowerSeries.coeff h ((declared m cash).part s):=by
  rw [crop,Poly.part_sum]
  simp_rw [coefficient,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro w _
  by_cases keep:exponent w≤p
  · rw [if_pos keep,Poly.part_smul,sum_eq_single (exponent w)]
    · simp
    · intro e _ miss; simp [Ne.symm miss]
    · simp [keep]
  · rw [if_neg keep,Poly.part_nil]
    symm; apply sum_eq_zero
    intro e he; have miss:exponent w≠e:=by intro h; apply keep; rw [h]; exact Nat.le_of_lt_succ (mem_range.mp he)
    simp [miss]

end YM.Integration.WilsonOriginalTwoFlatIRFlatPolynomial
end
