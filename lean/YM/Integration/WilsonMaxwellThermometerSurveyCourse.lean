import YM.Integration.WilsonMaxwellThermometerSurveyIncome
/-! All mixed masks share one purchased before-period normalized receipt, with the original lower quiet and elected clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMaxwellThermometerSurveyCourse
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open XSpace
open WilsonMaxwellThermometerSurveyIncome (chapter master prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}(R:Run G)

variable (W:Initialize G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)

abbrev shelf (posted:Fin (a+1)→Bool)(i:Fin (a+1)):SealR G:=
  ⟨l i,(primes G).F (l i),d i,if posted i then chapter W (l i) else (primes G).T (l i),fit i⟩

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (survey:prices W R.kit)(p:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) l d fit)≤k):
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∀ᶠ j:ℕ in atTop, ∃(C:ChorusLine (hol G) S p e Credit.leanC Credit.leanC Credit.leanC)
      (Y:Torch (hol G) S p rails Credit.leanC Credit.leanC Credit.leanC),
      Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧ Y.L.V.y=zz R.family.path.levels ∧
      Y.L.V.anchor=j ∧ C.arch=Y.L ∧ Dormitory Y.L.V (capP (deck (G:=G) l d fit)) u Credit.leanC ∧
      SpringD Y.L.V (capP (deck (G:=G) l d fit)) u (capP (deck (G:=G) l d fit)+2) Credit.leanC ∧
      ∀posted:Fin (a+1)→Bool,let Q:=shelf W l d fit posted
        FramesR (hol G) Y.L.V Credit.leanC Credit.leanC Q Credit.leanC ∧
        HorizonP (hol G) Y.L.V Credit.leanC Credit.leanC Q:=by
  intro S
  let P(i:Fin (a+1)):=BayV (master W) (l i) (d i) (fit i)
  have granted:=reported (hol G) (master W) survey.1 survey.2
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d fit cap,
    ambassadors simple (chart_ok G) R.alloy.B.valid granted tendsto_id e P (fun _=>rfl)] with j enrolled purchased
  obtain ⟨C,Y,levels,paid,clock,age,realm,quiet,spring,old,_⟩:=enrolled
  have pub:=purchased Y.L.V levels (paid.trans funded.1) clock age
  refine ⟨C,Y,levels,paid,clock,age,realm,quiet,spring,?_⟩
  intro tag Q
  have both:FramesR (hol G) Y.L.V Credit.leanC Credit.leanC Q Credit.leanC:=by
    intro i
    cases hi:tag i with
    | true =>
      rw [show Q i=P i from by simp [Q,shelf,hi,P,BayV,master]]
      exact pub i
    | false =>
      rw [show Q i=deck (G:=G) l d fit i from by simp [Q,shelf,hi,deck,BayV]]
      exact old i
  exact ⟨both,fun i=>(both i).map fun t=>t.p⟩

end YM.Integration.WilsonMaxwellThermometerSurveyCourse
end
