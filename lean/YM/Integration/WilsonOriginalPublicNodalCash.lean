import YM.Integration.WilsonOriginalPublicNodalFibre

/-! Reconstruction of the one original physical receipt from its actual public
measuring coordinates, with its charged unit and every true curvature term. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalCash
open Finset Lattice Wilson RG Source Labels Laurent Pert.Asymptotics PowerSeries
open ActualRunPhysicalPages PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialFigure (amount)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonReceivedCanonicalVerseBasis (dose)
open WilsonPositionProgramReportedField (entire)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[DecidableEq I](d:I→ℕ)
variable {N p K:ℕ}(live:K≤N)(w:(j:I)→R.family.label (d j))
local notation "F" j:max => R.family.labels.level (d j)
local notation "g" => regulatorRun R.family N p K
local notation "τ" => (R.family.path.rep N p K).p.threshold
local notation "V" => (fun i=>entire R (d i) K (N,p) (w i))

def axis (j:I)(b:(F j).Index):Columns R d:=Pi.single j b

include live in
omit [DecidableEq I] in
theorem return_at (j:I)(b:(F j).Index):amount R d g V j b*(τ:ℂ)^((F j).grades b).2=w j b:=by
  have hg:=ActualRunKernelPackets.regulator_pos R N p K live
  have nz:(g:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hg.ne'
  have hit:=congrFun (WilsonPositionProgramReportedField.recovered R (d j) K (N,p) live (w j)) b
  rw [←hit]
  change (_*_)*(τ:ℂ)^((F j).grades b).2=(((τ/g)^((F j).grades b).2:ℝ):ℂ)*_
  simp only [Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_div,div_pow]
  ring

include live in
theorem salary (j:I):∑b:(F j).Index,amount R d g V j b •
      request R d (axis R d j b) (N:=N) (p:=p) (K:=K) j=w j:=by
  classical
  funext l
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,request,axis,Pi.single_eq_same,Frame.scaled_apply,
    Complex.ofReal_pow]
  rw [Finset.sum_eq_single l]
  · simpa using return_at R d live (p:=p) w j l
  · intro b _ h
    rw [Pi.single_eq_of_ne (Ne.symm h),mul_zero,mul_zero]
  · simp

include live in
theorem original (j:I)(c:Choice R d j):
    ∑b:(F j).Index,amount R d g V j b*dose R d N p K (request R d (axis R d j b) (N:=N) (p:=p) (K:=K)) j c=
      dose R d N p K w j c:=by
  classical
  have sum:=salary R d live (p:=p) w j
  cases c with
  | inl u =>
    cases u
    change (∑b:(F j).Index,amount R d g V j b*request R d (axis R d j b) (N:=N) (p:=p) (K:=K) j 0)=w j 0
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using congrFun sum 0
  | inr x =>
    have apply:=congrArg (fun y=>(F j).core y x.1) sum
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at apply
    change (∑b:(F j).Index,_*(_*((F j).core (request R d (axis R d j b) (N:=N) (p:=p) (K:=K) j)) x.1*_))=
      _*((F j).core (w j)) x.1*_
    rw [←apply,mul_sum,sum_mul]
    apply sum_congr rfl
    intro b _
    ring

end YM.Integration.WilsonOriginalPublicNodalCash
end
