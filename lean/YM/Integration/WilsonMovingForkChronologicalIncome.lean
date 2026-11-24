import YM.Integration.WilsonMovingForkChronologicalTable
import YM.Integration.WilsonOriginalOrdinaryBochner

/-! The fitted K stencils and the complete paid chronological prints are
integrable on the actual Wilson prior at their own dates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkChronologicalIncome
open MeasureTheory (Integrable)
open Function Filter Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Affinity QuadraticLocal.Sunrise Push Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalMixedBlockRows WilsonRootedKioskOccupiedSlip WilsonRegisteredPairUnaryWallet
open WilsonMovingForkPrintedFile (Board Program)
open WilsonMovingForkChronologicalTable (ordinary density)
open scoped Classical BigOperators Topology
open private integral from YM.Integration.WilsonOriginalOrdinaryBochner
variable {G:Gauge}{R:Run G}{n K:ℕ}{d:Fin n → ℕ}(prog:Program R d K)
  (N per:ℕ)(w:(a:Fin n) → R.family.label (d a))(pins:Fin n → Site (R.family.side K per))
local notation "C" => R.family
local notation "J" => Stock.census (Fin n)
local notation "X" i:max => Config G ((C).side i per)

theorem upper (live:K ≤ N):
    Integrable (density prog N per w pins K) (prior G _):=by
  let rep:=(C).path.rep N per K
  change Integrable (fun U=>(rep.eval U:ℂ) • ordinary prog N per w pins K U) (prior G _)
  refine integral (prior G _) (rep.envelope (R.makes.wilson.represents N per K live).good) _ ?_
  intro s
  have cont:Continuous (fun U:X K=>(ordinary prog N per w pins K U).part s):=by
    simp only [WilsonMovingForkChronologicalTable.upper]
    exact continuous_finsetProd _ (fun a _=>continuous_const.add (((C).localSection (d a)).continuous_places
      (WilsonPositionProgramBlockedTrialAddBack.names R (d a) N per K (WilsonMovingForkMixedSeed.units R d K w a))
      (pins a)))
  obtain ⟨bound,paid⟩:=isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
  exact ⟨cont.measurable,bound,fun U=>paid U (Set.mem_univ _)⟩

theorem lower {i:ℕ}(ik:i<K)(live:i ≤ N):
    let b:=prog N per w pins i ik
    let rep:=(C).path.rep N per i
    let g:=regulatorRun (C) N per i
    ∀{ord seats shelf ext:ℕ}{stripU slack gross:ℝ},
      0 ≤ b.strip → b.order ≤ ord → 1 ≤ seats → n ≤ seats → (∑a,b.load a) ≤ shelf →
      0 ≤ rep.p.supportExponent+2 →
      Invoice.Supports rep.p stripU (rep.p.supportExponent+2) g b.strip slack →
      Invoice.price rep.p stripU (ord+shelf+1) seats (rep.p.supportExponent+2) slack G ≤
        (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2 →
      (∑a:b.index,Real.exp (b.strip*(b.binder a).length)*WilsonIndependentCollarSlateIntensity.amount
        (b.copies a) (b.binder a).center) ≤ gross*(3*g⁻¹)^ext →
      Integrable (density prog N per w pins i) (prior G _):=by
  intro b rep g ord seats shelf ext stripU slack gross hs dep oc slots fit wide fund fare wage
  obtain ⟨equal,C₀,C₁,_,_,_,_,_,sold⟩:=WilsonOriginalTwoFlatIRMounted.original b.binder b.load b.copies
    hs dep oc (by simpa using slots) fit rep.p fund fare wage
  have good:=WilsonOriginalOrdinaryBochner.unmasked rep (rep.envelope (R.makes.wilson.represents N per i live).good)
    _ (fun _=>zero_lt_one) wide sold b.wallet
  apply good.congr
  filter_upwards [] with U
  rw [equal]
  unfold density ordinary
  rw [dif_pos ik]
  rfl

end YM.Integration.WilsonMovingForkChronologicalIncome
