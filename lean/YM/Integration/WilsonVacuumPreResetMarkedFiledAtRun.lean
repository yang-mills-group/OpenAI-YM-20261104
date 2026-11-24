import YM.Integration.WilsonVacuumPreResetMarkedFiniteSourcePrice
import YM.Integration.WilsonVacuumPreResetFiniteHeatHistory

/-! Same-date physical-side transfer between the true finite log and the
official folded Gazette on the selected Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedFiledAtRun
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonVacuumPreResetFiniteHeatWindow WilsonVacuumPreResetFiniteHeatScale
open WilsonVacuumPreResetFiniteHeatTable WilsonVacuumPreResetMarkedOrdinaryBound
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open scoped Classical BigOperators
variable {ι:Type}[DecidableEq ι]

theorem original (G:Gauge)(D:ι→ℕ)(I:Finset ι)(k:ι→ℕ)(e i r:ℕ)(hi:i≤e):
    ∃v:Gear G→ℝ,∃M:ℝ,0≤M ∧ ∃d:ℕ,∀(R:Run G)(Q:Realm G (e+1) Credit.leanC),
    let L:=R.family.path.levels
    let O:=R.metals.O
    ∀m (hm:Q.anchor ≤ m),Q.draws=L→Q.paid=O→Q.y=zz L→v (Q.mint m hm).gear≤Q.cash Credit.leanC m →
    ∀N p:ℕ,m<N→
    let n:=R.family.side m p
    let f:=R.family.side (m+1) p
    let cap:=horizon e (r+2*mass k I)
    table L O e N (m+1) f (rate L (m+1) p) →
    ∀η:ℝ,rate L (m+1) p≤η→η≤1→∀K:family G D,Eu k K→∀a:ι→ℝ,(∀j,0<a j)→
    (∀J⊆I,J.Nonempty→∀j≤e,∀s≤cap,∀y,‖(repaint K J).1 f j s y‖≤weights a J ∧
      ‖(K J).1 f j s y-(repaint K J).1 f j s y‖≤η*weights a J)→
    ∀x,‖(logO L O m N K k I).1 n i r x-
        coilH L O m N n K k (ratioHigh L O N m) I i r x‖≤
          M*(gross (zz L m) f)^d*weights a I*η:=by
  obtain ⟨v,M,Mpos,d,paid⟩:=WilsonVacuumPreResetMarkedFiniteSourcePrice.original G D I k e i r hi
  refine ⟨v,M,Mpos,d,?_⟩
  intro R Q L O m hm draws ratio clock fund N z live n f cap quiet η covered unit K legal a hot fees x
  have pos:0<η:=(Real.exp_pos _).trans_le covered
  have natural:f=n*(loose L m).L:=Subtype.ext (R.family.path.levels.clock.op m z).sizes
  have input:=paid Q m hm fund N live n η pos unit
  change (∀j≤e,∀s≤cap,∀y,|(story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) j s y-
    emera (actionW Q.draws Q.paid N (m+1)) (n*(loose Q.draws m).L) j s y|≤η)→_ at input
  have qin: ∀j≤e,∀s≤cap,∀y,|(story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) j s y-
      emera (actionW Q.draws Q.paid N (m+1)) (n*(loose Q.draws m).L) j s y|≤η:=by
    rw [draws,ratio,←natural]
    exact fun j hj s _ y=>(quiet j hj s y).trans covered
  have chosen:=input qin K (repaint K) legal a hot
  change (∀J⊆I,J.Nonempty→∀j≤e,∀s≤cap,∀y,‖(repaint K J).1 (n*(loose Q.draws m).L) j s y‖≤weights a J ∧
      ‖(K J).1 (n*(loose Q.draws m).L) j s y-(repaint K J).1 (n*(loose Q.draws m).L) j s y‖≤η*weights a J)→
    ∀y,‖(logO Q.draws Q.paid m N K k I).1 n i r y-
        coilH Q.draws Q.paid m N n K k (ratioHigh Q.draws Q.paid N m) I i r y‖≤
      M*(gross (Q.y m) (n*(loose Q.draws m).L))^d*weights a I*η at chosen
  rw [draws,ratio,clock,←natural] at chosen
  exact chosen fees x

end YM.Integration.WilsonVacuumPreResetMarkedFiledAtRun
end
