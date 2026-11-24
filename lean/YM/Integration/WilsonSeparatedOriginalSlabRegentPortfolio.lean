import YM.Integration.WilsonSeparatedOriginalSlabYoungEnrollment
import YM.Integration.WilsonSeparatedOriginalSlabFourierCylinder

/-! One finite submitted full-cell catalogue carries the original smooth signed three-field experiment, with every child offset kept through all independent field readings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabRegentPortfolio
open Function Finset Lattice Wilson Labels RG Source RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabFolioAddress WilsonSeparatedOriginalSlabFolioEnrollment WilsonSeparatedOriginalSlabDriven
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){n N per:ℕ}{s:Fin 3 → ℕ}{T:Type*}
set_option quotPrecheck false
local notation "C"=>R.family
local notation "Parents"=>Fin 3 → Site ((C).side n per)
local notation "Fields"=>Fin 3 → Config G ((C).side N per)

abbrev leaves (r η:ℝ)(o:Parents)(book:(Fin 3 → Body) → (T → ℂ) → Prop):=
  List (Entry s (legal (Pulse.buy C n per o (r*η/2)) s) book)

def arm (v:(i:Fin 3) → Palette C (s i))(o:Parents)(f:Fin 3 → Body)(U:Fields):ℂ:=
  ∏i:Fin 3,Records.clinic C per N (s i) (v i) n (o i) (1,false) (f i) (U i)

theorem original (book:Parents → (Fin 3 → Body) → (T → ℂ) → Prop)(top:n≤N){r η X cap:ℝ}(rp:0<r)(room:(C).S.a n≤r)
    (ep:0<η)(small:η≤1)(Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(sizeX:Tall Ψ (rank+1) 1 X)(seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤ cap)
    (earn:∀o∈Pulse.area («C»:=R.family) (WilsonSeparatedOriginalSlabActiveWeights.range C n r cap),
      ∀f,legal (Pulse.buy C n per o (r*η/2)) s f → ∃a,book o f a):
    let A:=Pulse.area («C»:=R.family) (b:=n) (p:=per) (WilsonSeparatedOriginalSlabActiveWeights.range C n r cap)
    ∃L:(o:Parents) → leaves (s:=s) R r η o (book o),
      (∀o∈A,((L o).map price).sum≤tariff*(WilsonSeparatedOriginalSlabYoungBouquet.fee s rank η*X) ∧
        ∀e∈L o,∀H:ℕ,Priced H (stamp e) 1) ∧
      ∀(v:(i:Fin 3) → Palette C (s i))(g:Body)(m:ℕ)(U:Fields),
        WilsonSeparatedOriginalReplicaExperiments.assembled R s v top Ψ r g m U=
          premiums C s m n r*∑o∈A,((L o).map (fun e=>((price e:ℂ)*stamp e g)*arm R v o e.test U)).sum:=by
  intro A
  let tender:=fun (o:Parents)(L:leaves (s:=s) R r η o (book o))=>
    ((L.map price).sum≤tariff*(WilsonSeparatedOriginalSlabYoungBouquet.fee s rank η*X)) ∧
    (∀e∈L,∀H:ℕ,Priced H (stamp e) 1) ∧ ∀(v:(i:Fin 3) → Palette C (s i))(g:Body)(U:Fields),
       WilsonSeparatedOriginalReplicaRegularity.meeting s v o top Ψ r g U=(L.map (fun e=>((price e:ℂ)*stamp e g)*arm R v o e.test U)).sum
  have sold(o:Parents):∃L:leaves (s:=s) R r η o (book o), o∈A → tender o L:=by
    by_cases hp:o∈A
    · obtain ⟨L,hL⟩:=WilsonSeparatedOriginalSlabYoungEnrollment.original (book o) o top rp room ep small Ψ rank grade scatter xp sizeX (earn o hp)
      exact ⟨L,fun _=>hL⟩
    · exact ⟨[],fun ha=>(hp ha).elim⟩
  choose L priced using sold
  refine ⟨L,fun o ho=>⟨(priced o ho).1,(priced o ho).2.1⟩,?_⟩
  intro v g m U
  rw [← WilsonSeparatedOriginalSlabFourierCylinder.selected R s v top rp Ψ seen g m]
  simp only [WilsonSeparatedOriginalSlabFourierCylinder.restricted,ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
  exact congrArg (premiums C s m n r * ·) (Finset.sum_congr rfl (fun o ho=>(priced o ho).2.2 v g U))

end YM.Integration.WilsonSeparatedOriginalSlabRegentPortfolio
