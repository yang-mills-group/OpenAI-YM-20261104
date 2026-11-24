import YM.Integration.WilsonOriginalPublicTrialPhaseWhole

/-! A grant on the actual centered replicated K-born law at the original
Wilson receiver. Its scalar price has no factor for the number of copies. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseGrant
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Push Marker Extra.Histories
open MergeProof Accent Extra.Multi Cells OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open OPE.Therm.ReplicaChessboard WilsonOriginalPublicTrialPhaseTrace WilsonOriginalPublicTrialPhaseTerminal
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {N p K u:ℕ} {I:Type} [Fintype I]
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "H" => (C).path
structure Grant (d:I→ℕ)(z:I→Site ((C).side K p))(v:∀i,(C).label (d i))(uk:u≤K)(fee:ℝ) where
  station : ℕ
  radius : ℕ
  early : station ≤ u
  fits : ∀i,window (z i) (stencilRadius (C) (d i))⊆window 0 radius
  housing : Push.GridApprox.room (A) station K radius
  salary : ℝ
  soft : ℝ
  hard : ℝ
  rent : ℝ
  pos : 0 < salary
  regular : Site ((C).side station p)→ Config G ((C).side u p)→ℂ
  forced : Site ((C).side station p)→Box ((C).side u p)→ Config G ((C).side u p)→ℂ
  homes : Site ((C).side station p)→Site ((C).side u p)
  serves : let M:=word R (N:=N) d z v
           let a:=actualTransport (C) (N:=N) M uk 1
           Served ((H).rep N p u) regular forced
             (arrival R (N:=N) (early.trans uk) uk (fun U=>M U-a))
             homes (fun _=>salary) ((A).budget u).supportExponent rent
  vault : Vault (fun _ : Site ((C).side station p)=>salary) regular forced soft hard
  charge : Real.exp (((C).S.a station/(C).S.a u)^4*Vac.treasury (A) u+soft+hard+2*rent)/salary≤fee

theorem original (d:I→ℕ)(z:I→Site ((C).side K p))(v:∀i,(C).label (d i))(uk:u≤K)(live:K≤N)
    {fee:ℝ}(g:Grant R (N:=N) d z v uk fee):
    let M:=word R (N:=N) d z v
    ‖(∫U,M U ∂scene (H) N p K)-actualTransport (C) (N:=N) M uk 1‖≤fee:=by
  exact (WilsonOriginalPublicTrialPhaseWhole.original R d z v g.early uk live g.radius g.fits g.housing
    g.regular g.forced g.homes g.pos g.serves g.vault).trans g.charge
end YM.Integration.WilsonOriginalPublicTrialPhaseGrant
