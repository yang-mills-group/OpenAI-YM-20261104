import YM.Integration.WilsonInvariantActionConditionalMarginal
import YM.Integration.WilsonMatrixTicketLanesConnectedRegistered

/-! Exact connected components of the two actual grade-four regular fields,
with both complete conditional means on their common unmarked Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionConditionalRegistered
open Function Filter Finset MeasureTheory Lattice RG Wilson OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Legato Source MergeProof LocalComparison RG3.Script.Picnic Push.SectorMeasure
open WilsonInvariantActionRegisteredReturn WilsonInvariantActionMixedMaterial
open WilsonInvariantActionConditionalMarginal WilsonInheritedRegisteredField
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesConnectedRegistered
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) p)
local notation "coarse" => Config G (R.family.side m p)
local notation "upperLaw" => scene R.family.path N p (m+1)
local notation "lowerLaw" => scene R.family.path N p m

def nonlinear (v:R.family.label 4) (o:Site (R.family.side (m+1) p)):fine→ℂ:=
  R.family.O (m+1) p (center R (m+1) N p v) o

def old (live:m<N) (v:R.family.label 4) (o:Site (R.family.side (m+1) p)) (U:fine):ℂ:=
  maskError R live v o U+earlier (C:=R.family) R.makes live v o Set.univ U

set_option backward.isDefEq.respectTransparency false in
private theorem fields (live:m<N) (birth:R.family.ref 4 ≤ m + 1) (v:R.family.label 4)
    (o:Site (R.family.side (m+1) p)):
    let F:=regular (C:=R.family) R.makes live v o
    let A:=nonlinear R (N:=N) v o
    let Z:=old R live v o
    F=(fun U=>A U+Z U) ∧ Envelope F ∧ Envelope A ∧ Envelope Z:=by
  intro F A Z
  have split(U:fine):F U=A U+Z U:=by
    simpa only [F,A,Z,nonlinear,old,add_assoc] using four (k:=m+1) (N:=N) (per:=p) R live v o U
  have eF:Envelope F:=(source R live birth v o).1
  have eA:Envelope A:=Env.compact (R.family.continuousO (m+1) p 4 (center R (m+1) N p v) o)
  have dif:Z=fun U=>F U-A U:=funext (fun U=>by rw [split];ring)
  refine ⟨funext split,eF,eA,?_⟩
  rw [dif]
  exact ⟨eF.meas.sub eA.meas,⟨eF.cost.choose+eA.cost.choose,
    fun U=>(norm_sub_le _ _).trans (add_le_add (eF.cost.choose_spec U) (eA.cost.choose_spec U))⟩⟩

open private fineSum from YM.Integration.WilsonInvariantActionConditionalMarginal

private theorem integral {β:Type*} [MeasurableSpace β] {P:Measure β} [IsFiniteMeasure P]
    {f:β→ℂ} (ef:Envelope f):Integrable f P:=
  (integrable_const ef.cost.choose).mono' ef.meas.aestronglyMeasurable (ae_of_all _ ef.cost.choose_spec)

private theorem addLeft (P:Measure fine) [IsFiniteMeasure P] (f h t:fine→ℂ)
    (ef:Envelope f) (eh:Envelope h) (et:Envelope t):
    pair (fun x=>∫U,x U ∂P) (fun U=>f U+h U) t=
      pair (fun x=>∫U,x U ∂P) f t+pair (fun x=>∫U,x U ∂P) h t:=by
  simp only [pair,add_mul]
  rw [integral_add (integral (fineSum R f t ef et)) (integral (fineSum R h t eh et)), integral_add (integral ef) (integral eh)]
  ring

private theorem exchange {β:Type} (E:(β→ℂ)→ℂ) (f h:β→ℂ):pair E f h=pair E h f:=by
  simp only [pair,mul_comm]

theorem held (live:m<N) (birth:R.family.ref 4 ≤ m + 1) (v w:R.family.label 4)
    (x y:Site (R.family.side (m+1) p)) (V:coarse):
    let F:=regular (C:=R.family) R.makes live v x
    let H:=regular (C:=R.family) R.makes live w y
    let A:=nonlinear R (N:=N) v x
    let B:=nonlinear R (N:=N) w y
    let D:=old R live v x
    let L:=old R live w y
    connected R (N:=N) F H V=connected R (N:=N) A B V+
      connected R (N:=N) D B V+connected R (N:=N) F L V:=by
  intro F H A B D L
  obtain ⟨sf,ef,ea,ed⟩:=fields R live birth v x
  obtain ⟨sh,_,eb,el⟩:=fields R live birth w y
  let P:=ActualWilsonConditionalRoots.fibre R.family (N:=N) V
  letI:IsProbabilityMeasure P:=ActualWilsonConditionalRoots.probability R.family R.makes live V
  let E: (fine→ℂ)→ℂ:=fun f=>∫U,f U ∂P
  change pair E F H=pair E A B+pair E D B+pair E F L
  have first:pair E F B=pair E A B+pair E D B:=by
    rw [show F=fun U=>A U+D U from sf]
    exact addLeft R P A D B ea ed eb
  have second:pair E H F=pair E B F+pair E L F:=by
    rw [show H=fun U=>B U+L U from sh]
    exact addLeft R P B L F eb el ef
  rw [exchange E F H,second,exchange E B F,exchange E L F,first]

theorem original (live:m<N) (birth:R.family.ref 4 ≤ m + 1) (v w:R.family.label 4)
    (x y:Site (R.family.side (m+1) p)):
    let F:=regular (C:=R.family) R.makes live v x
    let H:=regular (C:=R.family) R.makes live w y
    let A:=nonlinear R (N:=N) v x
    let B:=nonlinear R (N:=N) w y
    pair (fun M=>∫U,M U ∂upperLaw) F H=
      (∫V,connected R (N:=N) A B V+connected R (N:=N) (old R live v x) B V+
        connected R (N:=N) F (old R live w y) V ∂lowerLaw)+
      pair (fun M=>∫V,M V ∂lowerLaw) (mean R (N:=N) F) (mean R (N:=N) H):=by
  intro F H A B
  rw [WilsonInvariantActionConditionalMarginal.original R live F H (source R live birth v x).1 (source R live birth w y).1]
  congr 1
  exact integral_congr_ae (ae_of_all _ (held R live birth v w x y))

end YM.Integration.WilsonInvariantActionConditionalRegistered
