import YM.Integration.WilsonOriginalSingleGaussianReceipt

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSingleGaussianDivision
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue Extra.Trajectories
open WilsonOriginalSingleMarkedRegister WilsonVacuumPreResetFiniteRegister
open WilsonOriginalSingleGaussianReceipt
open OriginalRadialSeries (observed)
open Primitives.GCC.Anchor
open scoped Classical BigOperators
variable {I Y V A:Type}[Fintype I][DecidableEq I][Fintype Y][Fintype V][DecidableEq V]
  [Fintype A]{J:Census V}{r:ℕ}(W:Page I Y A J r)(q:Matrix I I ℝ)(h:q.IsSymm)

def prior := register J r (observed W.B (mass W q))
def signed := ∑a,W.amplitude a • register J r (observed W.B (numerator W q a))
def row := signed W q * inverseMass (prior W q)

private theorem first (i:J.Mode)(hi:i.val.Nonempty):
    bottom J r (token J r i)=0:=by
  have hn:J.quiet≠i:=fun e=>hi.ne_empty (congrArg Subtype.val e.symm)
  apply Join.both_parts
  intro t u
  rw [bottom_value,token,Join.left_part,Poly.part_send,if_neg hn]
  by_cases ht:t=J.quiet <;> by_cases hu:u=(indices r).quiet <;> simp [ht,hu]

theorem vacuum : denominator (realTable W q h)=prior W q:=by
  rw [integral]
  change bottom J r (prior W q+token J r W.source*signed W q)=prior W q
  rw [map_add,map_mul,first W.source W.live,zero_mul,add_zero]
  exact WilsonOriginalSingleMarkedRegister.clean J r _

omit [Fintype Y] in
theorem leading : UnitLeading (realTable W q h):=by
  change (Cloud.prescription q h 0 W.driver).part (Board J r).quiet=1
  rw [Cloud.prescribed,driven_quiet,Cloud.wick_one]

theorem normalized :
    ratio (realTable W q h)=1+token J r W.source*row W q:=by
  have hd:(prior W q).part (Board J r).quiet=1:=
    (congrArg (fun x:Grade J r=>x.part (Board J r).quiet) (vacuum W q h).symm).trans
      ((bottom_quiet (realTable W q h)).trans (leading W q h))
  rw [ratio,vacuum,integral]
  change (prior W q+token J r W.source*signed W q)*inverseMass (prior W q)=_
  rw [add_mul,right_inverse hd,mul_assoc]
  rfl

theorem logarithm :
    logMarked (realTable W q h)=token J r W.source*row W q:=by
  let T:=token J r W.source*row W q
  have hT:T.part (Board J r).quiet=0:=
    (bottom_quiet T).symm.trans (by
      change (bottom J r (token J r W.source*row W q)).part (Board J r).quiet=0
      rw [map_mul,first W.source W.live,zero_mul];rfl)
  have e:T.pass=1+T:=by
    simpa [raise_still] using WilsonOriginalSingleMarkedRegister.exponential J r W.source W.live (row W q)
      0 (by simp)
  change connected (ratio (realTable W q h))=T
  rw [normalized,←e,connected_pass hT]

include h in
theorem identified (S:A→PowerSeries ℝ)
    (hS:∀a,observed W.B (numerator W q a)=observed W.B (mass W q)*S a):
    row W q=∑a,W.amplitude a • register J r (S a):=by
  let Z:=∑a,W.amplitude a • register J r (S a)
  have hn:signed W q=prior W q*Z:=by
    unfold signed Z
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro a _
    rw [hS,map_mul,mul_smul_comm]
    rfl
  have h0:(prior W q).part (Board J r).quiet=1:=
    (congrArg (fun x:Grade J r=>x.part (Board J r).quiet) (vacuum W q h).symm).trans
      ((bottom_quiet (realTable W q h)).trans (leading W q h))
  change signed W q*inverseMass (prior W q)=Z
  rw [hn,mul_right_comm,right_inverse h0,one_mul]

end YM.Integration.WilsonOriginalSingleGaussianDivision
