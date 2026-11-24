import YM.Integration.WilsonReflectedPublicCommonSup
import YM.Integration.WilsonMeasuredPublicEntranceCheapOrder

/-! The cheap part of the dosed ordinary swap under the true unconditioned
Wilson law and at every earlier posterior. Each source has its own true dose and grade. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCommonSoftLaw
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Motion
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonThermometerUnitFilingFieldRange WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open OPE.Therm WilsonMeasuredPublicEntranceCheapOrder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p f K:ℕ}
local notation "C₀" => R.family
local notation "P_" => R.family.path.rep N p f
local notation "H_" => R.family.path.levels.clock.hatBeta f
local notation "wage_" => WilsonReflectedPublicMountedInvoice.wage R f

def gross (R:Run G)(d f:ℕ):ℝ:=3*orbitCost (R.family.labels.level d)*(6+basisCost G d)*R.family.path.levels.clock.hatBeta f^(d+1)

def net (R:Run G)(d f q:ℕ):ℝ:=(6+basisCost G d)*(2+orbitCost (R.family.labels.level d))*(R.family.path.levels.clock.hatBeta f^q)⁻¹

theorem original {I:Type}(d q:I → ℕ)(A:∀i,Arm R (d i) N p f K)(h:f ≤ K)(top:K ≤ N)
    (c:I → ℂ)(row:I → Three G ((C₀).side f p))(X E:∀i,Coefficient ((C₀).labels.level (d i)) ((C₀).side f p))
    (filed:∀i,let Ω:=orbitCost ((C₀).labels.level (d i));
      Joined R (A i) h top (c i) (row i) wage_ (Ω*(1+wage_)) ((2+Ω)*((H_)^(q i+d i))⁻¹) (X i) (E i))
    (vs:List I){u:ℕ}(old:u ≤ f):
    let x:=fun U i=>(X i).exponentialEntry (A i).o ((C₀).localSection (d i)) (P_) U
    let e:=fun U i=>(E i).exponentialEntry (A i).o ((C₀).localSection (d i)) (P_) U
    let signed:=fun U=>(vs.map (x U)).prod-(vs.map (fun i=>x U i-e U i)).prod
    let invoice:=route (fun i=>gross R (d i) f) (fun i=>gross R (d i) f+net R (d i) f (q i))
      (fun i=>net R (d i) f (q i)) vs
    (∀U,‖actualTransport (C₀) (N:=N) signed old U‖ ≤ invoice) ∧
      ‖∫U,actualTransport (C₀) (N:=N) signed old U ∂scene (C₀).path N p u‖ ≤ invoice:=by
  intro x e signed invoice
  have fees (i:I):=WilsonReflectedPublicCommonSup.original R (A i) h top (c i) (row i) (q i)
    (X i) (E i) (filed i)
  have paid (U):‖signed U‖ ≤ invoice:=by
    have split:=crossed (1:ℂ) (x U) (fun i=>x U i-e U i) (e U) (fun i=>by ring) vs
    rw [one_mul] at split
    change ‖(vs.map (x U)).prod-(vs.map (fun i=>x U i-e U i)).prod‖ ≤ _
    rw [split]
    exact price (x U) (e U) (fun i=>gross R (d i) f) (fun i=>net R (d i) f (q i))
      (fun i=>(fees i U).1) (fun i=>(fees i U).2) vs
  have every:=actualTransport_norm_le (C₀) R.makes (h.trans top) paid old
  letI : IsProbabilityMeasure (scene (C₀).path N p u):=probability R.makes.wilson (old.trans (h.trans top))
  refine ⟨every,?_⟩
  simpa using norm_integral_le_of_norm_le_const (μ:=scene (C₀).path N p u) (ae_of_all _ every)

end YM.Integration.WilsonReflectedPublicCommonSoftLaw
end
