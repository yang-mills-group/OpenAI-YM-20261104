import YM.Integration.WilsonOriginalJointGaussianIncome

/-! Component readings of a jointly deposited roster before the conditional Wilson integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalJointGaussianAdmission
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonVacuumPreResetFiniteRegister WilsonOriginalSingleMarkedRegister WilsonOriginalMixedGaussianTable
open WilsonOriginalJointGaussianIncome
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V](J:Census V)(r:ℕ)
variable {I Y A B:Type}[Fintype I][DecidableEq I][Fintype Y][Fintype A][Fintype B]

theorem income_value {S:Type}(v:S→ℝ)(i:J.Mode)(a:A→ℂ)(U:A→Ink S)(s:J.Mode)(k:Index r):
    (income J r v i a U).part (Join.pair s k)=
      if s=i then (k.val.card.factorial:ℂ)*(∑e,a e*(MvPolynomial.eval v (coeff k.val.card (U e)):ℝ)) else 0:=by
  let Z:=∑e,a e • register J r (observed v (U e))
  have vacant:bottom J r Z=Z:=by simp only [Z,map_sum,map_smul,clean]
  change (token J r i*Z).part _=_
  rw [token_read J r i s k Z vacant]
  split
  · simp only [Z,Poly.part_sum,Poly.part_smul,WilsonVacuumPreResetFiniteRegister.read,Finset.mul_sum]
    apply sum_congr rfl
    intro e _
    change a e*((k.val.card.factorial:ℂ)*(MvPolynomial.eval v (coeff k.val.card (U e)):ℝ))=
      k.val.card.factorial*(a e*(MvPolynomial.eval v (coeff k.val.card (U e)):ℝ))
    ring
  · rfl

variable (h:Y→ℝ)(i j:Hot J)(P:Ink (I⊕Y))(a:A→ℂ)(b:B→ℂ)(U:A→Ink (I⊕Y))(W:B→Ink (I⊕Y))
def source (z:I→ℝ):Grade J r :=
  register J r (observed (Sum.elim z h) P)+income J r (Sum.elim z h) i.val a U+
    income J r (Sum.elim z h) j.val b W

omit [Fintype I] [DecidableEq I] [Fintype Y] in
theorem evaluated (z:I→ℝ)(t:J.Mode)(k:Index r):
    (source J r h i j P a b U W z).part (Join.pair t k)=
      (k.val.card.factorial:ℂ)*(
        (if t=J.quiet then ((MvPolynomial.eval (Sum.elim z h) (coeff k.val.card P):ℝ):ℂ) else 0)+
        (if t=i.val then ∑e,a e*(MvPolynomial.eval (Sum.elim z h) (coeff k.val.card (U e)):ℝ) else 0)+
        (if t=j.val then ∑e,b e*(MvPolynomial.eval (Sum.elim z h) (coeff k.val.card (W e)):ℝ) else 0)):=by
  simp only [source,Poly.part_plus,WilsonVacuumPreResetFiniteRegister.read,income_value,mul_add]
  split_ifs <;> simp [OriginalRadialSeries.observed]

theorem admitted (zero:constantCoeff P=0)(q:Matrix I I ℝ)(sym:q.IsSymm)(f:Hot (Board J r)→Normal.poly I)
    (written:∀(s:Hot (Board J r))(z:I→ℝ),Cloud.paint z (f s)=(source J r h i j P a b U W z).part s.val):
    Cloud.prescription q sym 0 f =
      stock J r h (fun x:Option A×Option B=>charge J i.val a x.1*charge J j.val b x.2)
        (fun x=>Wick Y q (raiseE P*option U x.1*option W x.2)):=by
  apply WilsonOriginalMixedGaussianTable.integrated
  intro z
  have log:lit (Board J r) (fun s=>Cloud.paint z (f s))=source J r h i j P a b U W z:=by
    ext1 s
    by_cases nonempty:s.val.Nonempty
    · exact (part_lit _ ⟨s,nonempty⟩).trans (written ⟨s,nonempty⟩ z)
    · have empty:s=(Board J r).quiet:=of_not_not (mt (hot_iff_ne s).2 nonempty)
      have oi:J.quiet≠i.val:=fun e=>i.property.ne_empty (congrArg Subtype.val e.symm)
      have oj:J.quiet≠j.val:=fun e=>j.property.ne_empty (congrArg Subtype.val e.symm)
      rw [empty,part_lit_quiet,←Join.pair_quiet,evaluated]
      have ord:((indices r).quiet.val.card:ℕ)=0:=rfl
      rw [ord,if_pos rfl,if_neg oi,if_neg oj,coeff_zero_eq_constantCoeff_apply,zero,map_zero];simp
  rw [log]
  exact passed J r (Sum.elim z h) P zero i.val j.val i.property j.property a b U W

end YM.Integration.WilsonOriginalJointGaussianAdmission
