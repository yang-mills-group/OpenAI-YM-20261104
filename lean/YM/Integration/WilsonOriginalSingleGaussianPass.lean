import YM.Integration.WilsonOriginalSingleGaussianTable

/-! The real tilted Gaussian and its actual finite occupied payer at each retained heat grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSingleGaussianPass
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonOriginalSingleMarkedRegister WilsonVacuumPreResetFiniteRegister
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {I Y V A:Type}[Fintype I][DecidableEq I][Fintype Y][Fintype V][DecidableEq V]
  [Fintype A]{J:Census V}(r:ℕ)(B:Y→ℝ)

def deposit (P:Ink (I⊕Y))(M:A→Ink (I⊕Y))(c:A→ℂ)(z:I→ℝ)(i:J.Mode) :=
  register J r (observed (Sum.elim z B) P) +
    token J r i*(∑a,c a • register J r (observed (Sum.elim z B) (M a)))

omit [Fintype I] [DecidableEq I] [Fintype Y] in
theorem read_deposit (P:Ink (I⊕Y))(M:A→Ink (I⊕Y))(c:A→ℂ)(z:I→ℝ)
    (i t:J.Mode)(u:Index r) :
    (deposit r B P M c z i).part (Join.pair t u) =
      (if t=J.quiet then (u.val.card.factorial:ℂ)*(MvPolynomial.eval (Sum.elim z B)
        (coeff u.val.card P):ℝ) else 0) +
      (if t=i then ∑a,(u.val.card.factorial*c a)*(MvPolynomial.eval (Sum.elim z B)
        (coeff u.val.card (M a)):ℝ) else 0) :=by
  let Z:=∑a,c a • register J r (observed (Sum.elim z B) (M a))
  have hp:bottom J r Z=Z:=by simp only [Z,map_sum,map_smul,WilsonOriginalSingleMarkedRegister.clean]
  rw [deposit,Poly.part_plus,token_read J r i t u Z hp,WilsonVacuumPreResetFiniteRegister.read]
  congr 1
  · by_cases h:t=J.quiet
    · simp only [if_pos h];rfl
    · simp only [if_neg h,mul_zero]
  · split
    · simp only [Z,Poly.part_sum,Poly.part_smul,WilsonVacuumPreResetFiniteRegister.read]
      apply sum_congr rfl
      intro a _
      change c a*((u.val.card.factorial:ℂ)*(MvPolynomial.eval (Sum.elim z B) (coeff u.val.card (M a)):ℝ))=_
      ring
    · rfl

omit [Fintype I] [DecidableEq I] [Fintype Y] in
private theorem observed_zero (P:Ink (I⊕Y))(hP:constantCoeff P=0)(z:I→ℝ):
    constantCoeff (observed (Sum.elim z B) P)=0:=by
  change MvPolynomial.eval (Sum.elim z B) (constantCoeff P)=0
  rw [hP,map_zero]

omit [Fintype I] [DecidableEq I] [Fintype Y] in
private theorem passed (P:Ink (I⊕Y))(hP:constantCoeff P=0)(M:A→Ink (I⊕Y))(c:A→ℂ)
    (z:I→ℝ)(i:J.Mode)(hi:i.val.Nonempty) :
    Poly.pass (deposit r B P M c z i) =
      deposit r B (raiseE P) (fun a=>raiseE P*M a) c z i :=by
  let v:=Sum.elim z B
  have hx:constantCoeff (observed v PowerSeries.X)=0:=by
    simp [OriginalRadialSeries.observed]
  have hp:=raise_map (observed v) hx hP
  change Poly.pass (register J r (observed v P)+token J r i*_)=_
  rw [WilsonOriginalSingleMarkedRegister.exponential J r i hi _ _ (observed_zero B P hP z)]
  unfold deposit
  change _=register J r (observed v (raiseE P))+token J r i*(∑a,c a • register J r (observed v (raiseE P*M a)))
  rw [hp,mul_add,mul_one,mul_left_comm _ (token J r i),Finset.mul_sum]
  congr 2
  apply sum_congr rfl
  intro a _
  rw [mul_smul_comm,map_mul,map_mul,hp]

omit [Fintype I] [DecidableEq I] [Fintype Y] in
theorem hot (P:Ink (I⊕Y))(hP:constantCoeff P=0)(M:A→Ink (I⊕Y))(c:A→ℂ)(i:J.Mode)
    (hi:i.val.Nonempty)(f:Hot (Board J r)→Normal.poly I)
    (h:∀(s:Hot (Board J r))(z:I→ℝ),Cloud.paint z (f s)=(deposit r B P M c z i).part s.val)
    (z:I→ℝ):lit (Board J r) (fun s=>Cloud.paint z (f s))=deposit r B P M c z i:=by
  have hn:J.quiet≠i:=fun e=>hi.ne_empty (congrArg Subtype.val e.symm)
  ext1 s
  by_cases hs:s.val.Nonempty
  · rw [part_lit _ ⟨s,hs⟩]
    exact h ⟨s,hs⟩ z
  · have eq:s=(Board J r).quiet:=of_not_not (mt (hot_iff_ne s).2 hs)
    rw [eq,part_lit_quiet,←Join.pair_quiet,read_deposit]
    have hm: ((indices r).quiet.val.card:ℕ)=0:=rfl
    rw [hm,if_pos rfl,if_neg hn,coeff_zero_eq_constantCoeff_apply,hP,map_zero];simp

theorem original (q:Matrix I I ℝ)(h:q.IsSymm)
    (i:J.Mode)(hi:i.val.Nonempty)(P:Ink (I⊕Y))(hP:constantCoeff P=0)
    (M:A→Ink (I⊕Y))(c:A→ℂ)(f:Hot (Board J r)→Normal.poly I)
    (law:∀z,lit (Board J r) (fun h=>Cloud.paint z (f h))=deposit r B P M c z i) :
    Cloud.prescription q h 0 f = register J r (observed B (Wick Y q (raiseE P))) +
      token J r i*(∑a,c a • register J r (observed B (Wick Y q (raiseE P*M a)))) :=by
  apply WilsonOriginalSingleGaussianTable.registered r B q h i hi (raiseE P)
    (fun a=>raiseE P*M a) c f
  intro t u z
  rw [Cloud.before_log,law,passed r B P hP M c z i hi]
  exact read_deposit r B (raiseE P) (fun a=>raiseE P*M a) c z i t u

end YM.Integration.WilsonOriginalSingleGaussianPass
