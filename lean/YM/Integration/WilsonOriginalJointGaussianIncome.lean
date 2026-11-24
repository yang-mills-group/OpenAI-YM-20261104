import YM.Integration.WilsonOriginalMixedGaussianTable

/-! Two enrolled source families on one original conditional integration. Each deposited
row and each joint product is integrated once against the same tilted Gaussian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalJointGaussianIncome
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open Extra.Trajectories (pass_add pass_zero)
open WilsonVacuumPreResetFiniteRegister WilsonOriginalSingleMarkedRegister WilsonOriginalMixedGaussianTable
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V](J:Census V)(r:ℕ)
variable {X Y S A B:Type}[Fintype A][Fintype B]

def option {D E:Type} [One E] (c:D→E):Option D→E
  | none => 1
  | some a => c a

def charge (i:J.Mode)(a:A→ℂ)(u:Option A):Poly J :=
  option (fun e=>a e • Poly.send i 1) u

def income (v:S→ℝ)(i:J.Mode)(a:A→ℂ)(P:A→Ink S):Grade J r :=
  token J r i*(∑e,a e • register J r (observed v (P e)))

private theorem absent (i:J.Mode)(hi:i.val.Nonempty)(w:Grade J r):
    (token J r i*w).part (Board J r).quiet=0:=by
  have hn:J.quiet≠i:=fun e=>hi.ne_empty (congrArg Subtype.val e.symm)
  rw [Poly.quiet_mul,token,Join.inject_left_quiet,Poly.part_send,if_neg hn,zero_mul]

private theorem multiplied (v:S→ℝ)(a b:Poly J)(P Q:Ink S):
    term J r v a P*term J r v b Q=term J r v (a*b) (P*Q):=by
  simp only [term,map_mul]
  ring

private theorem optional (v:S→ℝ)(i:J.Mode)(a:A→ℂ)(P:A→Ink S):
    (∑u:Option A,term J r v (charge J i a u) (option P u))=1+income J r v i a P:=by
  rw [Fintype.sum_option]
  change term J r v 1 1+(∑u:A,term J r v ((a u) • Poly.send i 1) (P u))=_
  simp only [term,map_one,one_mul,income,token,map_smul,smul_mul_assoc,mul_smul_comm,Finset.mul_sum]

theorem passed (v:S→ℝ)(P:Ink S)(hP:constantCoeff P=0)
    (i j:J.Mode)(hi:i.val.Nonempty)(hj:j.val.Nonempty)(a:A→ℂ)(b:B→ℂ)(U:A→Ink S)(W:B→Ink S):
    Poly.pass (register J r (observed v P)+income J r v i a U+income J r v j b W)=
      stock J r v (fun x:Option A×Option B=>charge J i a x.1*charge J j b x.2)
        (fun x=>raiseE P*option U x.1*option W x.2):=by
  have h0:constantCoeff (observed v P)=0:=by
    change MvPolynomial.eval v (constantCoeff P)=0
    rw [hP,map_zero]
  have empty:(register J r (observed v P)).part (Board J r).quiet=0:=by
    rw [←Join.pair_quiet,WilsonVacuumPreResetFiniteRegister.read,if_pos rfl]
    change (0:ℕ).factorial * ((coeff 0 (observed v P):ℝ):ℂ)=0
    rw [coeff_zero_eq_constantCoeff_apply,h0];simp
  have hz:constantCoeff (observed v PowerSeries.X)=0:=by simp [OriginalRadialSeries.observed]
  have lift:=raise_map (observed v) hz hP
  have old:(income J r v i a U).part (Board J r).quiet=0:=absent J r i hi _
  have fresh:(income J r v j b W).part (Board J r).quiet=0:=absent J r j hj _
  have one:register J r (raiseE (0:PowerSeries ℝ))=1:=by
    rw [WilsonVacuumPreResetFiniteRegister.exponential J r 0 (by simp),map_zero,pass_zero]
  have atom:Poly.pass (income J r v j b W)=1+income J r v j b W:=by
    have once:=WilsonOriginalSingleMarkedRegister.exponential J r j hj
      (∑e,b e • register J r (observed v (W e))) 0 (by simp)
    simpa only [map_zero,zero_add,one,one_mul,income] using once
  have first:Poly.pass (register J r (observed v P)+income J r v i a U)=
      register J r (raiseE (observed v P))*(1+income J r v i a U):=
    WilsonOriginalSingleMarkedRegister.exponential J r i hi _ _ h0
  rw [pass_add (by rw [Poly.part_plus,empty,old,add_zero]) fresh,first,atom,←lift]
  have vacuum:term J r v 1 (raiseE P)=register J r (observed v (raiseE P)):=by simp [term]
  rw [←vacuum]
  rw [←optional J r v i a U,←optional J r v j b W]
  simp only [stock,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,multiplied,one_mul]
  exact Finset.sum_comm

end YM.Integration.WilsonOriginalJointGaussianIncome
