import YM.Integration.WilsonOriginalSingleMarkedRegister

/-! The signed original Gaussian table, retaining a marked numerator and the entire quiet row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSingleGaussianTable
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonOriginalSingleMarkedRegister WilsonVacuumPreResetFiniteRegister
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {I Y V A:Type}[Fintype I][DecidableEq I][Fintype Y][Fintype V][DecidableEq V]
  [Fintype A]{J:Census V}(r:ℕ)(B:Y→ℝ)(q:Matrix I I ℝ)(h:q.IsSymm)

def field (p:MvPolynomial (I⊕Y) ℝ): Normal.poly I :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Complex.ofRealHom)
    (Sum.elim MvPolynomial.X (fun y=>MvPolynomial.C ((B y:ℝ):ℂ))) p

omit [Fintype I] [DecidableEq I] [Fintype Y] in
theorem reading (p:MvPolynomial (I⊕Y) ℝ)(z:I→ℝ):
    Cloud.paint z (field B p)=(MvPolynomial.eval (Sum.elim z B) p:ℝ):=by
  let L:=MvPolynomial.eval₂Hom (MvPolynomial.C.comp Complex.ofRealHom)
    (Sum.elim (MvPolynomial.X : I→MvPolynomial I ℂ) (fun y=>MvPolynomial.C ((B y:ℝ):ℂ)))
  have he:((Cloud.paint z).toRingHom.comp L)=
      Complex.ofRealHom.comp (MvPolynomial.eval (Sum.elim z B)):=by
    apply MvPolynomial.ringHom_ext
    · intro x;simp [L,Cloud.paint]
    · intro x;cases x <;> simp [L,Cloud.paint]
  exact DFunLike.congr_fun he p

theorem integrated (d:ℕ)(p:A→Ink (I⊕Y))(c:A→ℂ)(u:Normal.poly I)
    (hu:∀z,Cloud.paint z u=∑a,c a*(MvPolynomial.eval (Sum.elim z B) (coeff d (p a)):ℝ)):
    Cloud.wick q h 0 u=∑a,c a*(MvPolynomial.eval B (coeff d (Wick Y q (p a))):ℝ):=by
  have he:u=∑a,c a • field B (coeff d (p a)):=by
    apply Valence.Enlist.paint_inj
    intro z;rw [hu,map_sum];simp_rw [map_smul,reading,smul_eq_mul]
  rw [he,map_sum];simp_rw [map_smul,smul_eq_mul]
  apply sum_congr rfl
  intro a _
  rw [OriginalFiniteWickReadout.painted B q h (p a) d _ (fun z=>reading B _ z)]

private theorem quiet_case (d:ℕ)(P:Ink (I⊕Y))(c:ℂ)(v:Normal.poly I)
    (hv:∀z,Cloud.paint z v=c*(MvPolynomial.eval (Sum.elim z B) (coeff d P):ℝ)):
    Cloud.wick q h 0 v=c*(MvPolynomial.eval B (coeff d (Wick Y q P)):ℝ):=by
  have hl (z:I→ℝ):Cloud.paint z v=∑_a:Unit,c*(MvPolynomial.eval (Sum.elim z B) (coeff d P):ℝ):=by simpa using hv z
  simpa using integrated B q h d (fun _a:Unit=>P) (fun _=>c) v hl

/-- The unnormalized physical Wick result combines the complete quiet table with precisely
the original weighted one-source numerators at the retained order. -/
theorem registered (i:J.Mode)(hi:i.val.Nonempty)(P:Ink (I⊕Y))(M:A→Ink (I⊕Y))(c:A→ℂ)
    (f:Hot (Board J r)→Normal.poly I)
    (law:∀(t:J.Mode)(u:Index r)(z:I→ℝ),
      Cloud.paint z (Cloud.integrand f (Join.pair t u)) =
      (if t=J.quiet then (u.val.card.factorial:ℂ)*(MvPolynomial.eval (Sum.elim z B)
        (coeff u.val.card P):ℝ) else 0) +
      (if t=i then ∑a,(u.val.card.factorial*c a)*(MvPolynomial.eval (Sum.elim z B)
        (coeff u.val.card (M a)):ℝ) else 0)):
    Cloud.prescription q h 0 f = register J r (observed B (Wick Y q P)) +
      token J r i*(∑a,c a • register J r (observed B (Wick Y q (M a)))) :=by
  have hn:J.quiet≠i:=fun e=>hi.ne_empty (congrArg Subtype.val e.symm)
  let Z:=∑a,c a • register J r (observed B (Wick Y q (M a)))
  have pure:bottom J r Z=Z:=by
    simp only [Z,map_sum,map_smul,WilsonOriginalSingleMarkedRegister.clean]
  apply Join.both_parts
  intro t u
  change Cloud.wick q h 0 (Cloud.integrand f (Join.pair t u))=_
  change _=(register J r (observed B (Wick Y q P))).part (Join.pair t u) +
    (token J r i*Z).part (Join.pair t u)
  rw [token_read J r i t u Z pure,WilsonVacuumPreResetFiniteRegister.read]
  by_cases ht:t=J.quiet
  · subst t;rw [if_pos rfl,if_neg hn,add_zero]
    exact quiet_case B q h u.val.card P _ _ (fun z=>by simpa [hn] using law J.quiet u z)
  · rw [if_neg ht,mul_zero,zero_add]
    by_cases hi':t=i
    · subst t;rw [if_pos rfl]
      have w:=integrated B q h u.val.card M (fun a=>(u.val.card.factorial:ℂ)*c a) _
        (fun z=>by simpa [ht] using law i u z)
      rw [w]
      simp only [Z,Poly.part_sum,Poly.part_smul,WilsonVacuumPreResetFiniteRegister.read]
      apply sum_congr rfl
      intro a _
      change _=c a*((u.val.card.factorial:ℂ)*(MvPolynomial.eval B (coeff u.val.card (Wick Y q (M a))):ℝ))
      ring
    · rw [if_neg hi']
      have hz:Cloud.integrand f (Join.pair t u)=0:=by
        apply Valence.Enlist.paint_inj
        intro z;simpa [ht,hi'] using law t u z
      rw [hz,map_zero]

end YM.Integration.WilsonOriginalSingleGaussianTable
