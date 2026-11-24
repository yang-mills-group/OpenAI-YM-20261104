import YM.Integration.WilsonAddressedFiniteGuardTrial
import YM.Integration.WilsonPositionProgramTrialGroundCylinder
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteThermalInput
open Finset MeasureTheory Lattice Wilson RG Source Labels Marker QuadraticLocal.Affinity MergeProof.Accent
open PhysicalNext.Repeat.Legato PertExtension Pert.Asymptotics RG16 RG16.Literal
open WilsonAddressedFiniteGuardTrial (printed submitted)
open WilsonOriginalPublicTrialFigure (measured amount)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I](d:I → ℕ)(N per K:ℕ)
  (o:I → Site (R.family.side K per))(v:∀a:I,R.family.label (d a))(z:I → ℂ)
  (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=I)))(s:(Stock.census I).Mode)

def vector (a:↥s.val):(R.family.labels.level (d a.val)).Coeff:=
  WilsonPositionProgramReportedField.entire R (d a.val) K (N,per) (submitted R d v z x a.val)

variable (locations:I → Cover)(lift:∀a,wrap (R.family.side K per) (locations a)=o a)
local notation "g" => regulatorRun R.family N per K

include lift in
theorem original (U:Config G (R.family.side K per)):
    printed R d (N:=N) o v z x s U=measured R (fun a:↥s.val=>d a.val) g
      (vector R d N per K v z x s) (fun a=>locations a.val) U:=by
  let row (a:I):ℂ:=∑l,WilsonPositionProgramReportedField.entire R (d a) K (N,per) (submitted R d v z x a) l*
    WilsonPositionProgramBlockedTrialFiling.atomAt R (d a) N per K (o a) l U
  calc
    _=∏a:↥s.val,row a.val:=(Finset.prod_coe_sort s.val row).symm
    _=_:=by
      unfold measured
      apply Finset.prod_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro l _
      rw [lift]
      simp only [amount,vector,WilsonPositionProgramBlockedTrialFiling.atomAt,Complex.real_smul,
        Complex.ofReal_inv,mul_assoc]

include lift in
/-- The physical finite film on the restored optical source, with its true
    measured heat and the same relative lifts for all proper subfaces. -/
theorem grounded (live:K ≤ N)(U:Config G (R.family.side K per))(L:ℂ →L[ℝ] ℝ):
    WilsonThermometerInversionFaces.face R (fun a:↥s.val=>d a.val)
      (wrap (R.family.side K per) ∘ (fun a:↥s.val=>locations a.val)) 1 1 (vector R d N per K v z x s)
      (fun (_:↥s.val) (_:Unit)=>1) () L g U=L (printed R d (N:=N) o v z x s U):=by
  have positive:=ActualRunKernelPackets.regulator_pos R N per K live
  rw [original R d N per K o v z x s locations lift U]
  exact WilsonPositionProgramTrialGroundCylinder.original R (fun a:↥s.val=>d a.val)
    (vector R d N per K v z x s) (fun a=>locations a.val) positive.ne' U L

end YM.Integration.WilsonAddressedFiniteThermalInput
end
