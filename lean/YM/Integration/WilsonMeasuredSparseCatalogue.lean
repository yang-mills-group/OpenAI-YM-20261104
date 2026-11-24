import YM.Integration.WilsonMeasuredChargedSiteFare
import YM.Integration.WilsonEmittedSparseRows

/-! Return the complete compact and long signed material to the very same
measured Wilson representation at the actual displaced site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredSparseCatalogue
open Filter Function Finset Lattice RG Wilson Source Labels Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise Push.Local Push.AbsoluteSums Next.Foundations
open Comparison.Density.Mirrors WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open WilsonCenteredCaptureSlots WilsonCenteredFailedHalo WilsonCenteredMountedCapture
open ConnectedActivityE6 Trace.Physical PhysicalNext Repeat Legato Roost Org Pert.Asymptotics
open Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "hat" => R.family.path.levels.clock.hatBeta
local notation "divisor" => LocalComparison.forcedDivisor R.family

theorem original (simple:G.Simple) (d n q:ℕ) {wallet ε:ℝ} (hw:0<wallet) (ep:0<ε) :
    ∀ᶠ i:ℕ in atTop, ∀ (m N per k probe:ℕ) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
      (Ψ:(j:ℕ)→Rep G ((C).side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i → i < N → probe ≤ i →
    ∀ (A V:Type) [Fintype A] [DecidableEq V] (I X:A→Type) (J:Census V)
      (P:A→Passport ((C).side i per) V) (M:(a:A)→I a→Row (P a) J G (X a)) (w:A→V→ℝ)
      (grades:A→V→ℕ) (x:(a:A)→X a) (c:A→ℝ) (ν ℓ:A→ℕ) (σ b K θ:A→ℝ)
      (p pieces depth:A→ℕ) (s:J.Mode) (v:V) (y:Site ((C).side i per))
      (cut D pole:ℕ) (scale mass:ℝ), v∈s.val → 0 < mass →
    let B:=(Ψ i).p
    let g:=Coat.gStep (Ψ i).beta
    let short:=words M x c ℓ (fun a=>early (M a) s cut) g
    let box:=neighborhood D y
    let rent:=reservedMass B box (‖(↑((g^pole)⁻¹):ℂ)‖*scale)+
      WilsonEmittedLongInvoice.budget (G:=G) w c ν B s cut g p pieces depth K b θ
    let cash:=reservedMass B box (WilsonEmittedLongInvoice.gross w c ν B s 0 g p pieces depth b θ)+
      WilsonEmittedLongInvoice.gross w c ν B s cut g p pieces depth b θ
    (∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a)) →
    (∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a)) →
    (∀a,(P a).origin v=y) → y∈box → 0 < g →
    (∀a,pole+ν a=ℓ a+(Launch.index J (grades a) s+1)) →
    B.Regular box short → B.supBounds y box short scale → 0 ≤ scale →
    (∀a (U:Config G ((C).side i per)),Summable (fun b=>Spill.raw (M a) g (x a) b U)) →
    cash≤(wallet*(hat i)^n)*mass →
    factor (C).params ((C).localSection d) B.supportExponent ((C).path.levels.params i).columns*rent ≤
      (ε*(regulatorRun (C) N per probe)^q)*mass →
    ∃e:Coefficient ((C).labels.level d) ((C).side i per),
      e.Format y (C).params (Ψ i) ∧ e.remBound y (Ψ i) (divisor i) (3*(ε*(regulatorRun (C) N per probe)^q)*mass) ∧
      ((C).labels.level d).coeffSize e.x≤(ε*(regulatorRun (C) N per probe)^q)*mass ∧
      ∀U,e.density y ((C).localSection d) (Ψ i) U=((Ψ i).eval U:ℂ)*
        (∑a,c a • (g^(ν a) • (Spill.Foundry.uncut (M a) g (x a) U).part s)) :=by
  filter_upwards [WilsonMeasuredChargedSiteFare.original R simple d n q hw ep]
    with i returned m N per k probe π Γ Ψ course before live report A V fm de I X J P M w grades
      x c ν ℓ σ b K θ p pieces depth s v y cut D pole scale mass hv mass_pos
  dsimp only
  intro old scope home fixed g_pos lag good measured scale_pos posted gross cheap
  let B:=(Ψ i).p
  let g:=Coat.gStep (Ψ i).beta
  obtain ⟨rows,soft,hard,reads⟩:=WilsonEmittedSparseRows.original M w grades x c ν ℓ B old scope s v hv
    cut D pole home fixed g_pos lag good measured scale_pos posted
  obtain ⟨e,⟨formatted,paid⟩,primary,heard⟩:=returned m N per k probe π Γ Ψ course before live report
    y (WilsonEmittedSparseRows.Key M s cut) (WilsonEmittedSparseRows.site M B s cut D y)
    (WilsonEmittedSparseRows.value M x c ν ℓ s cut pole g) _ _ _ _ mass mass_pos
    (fun z=>(rows z).1) (fun z=>(rows z).2.1) soft hard (fun z=>(rows z).2.2.1)
    (fun z=>(rows z).2.2.2) gross cheap
  exact ⟨e,formatted,paid,primary,fun U=>(heard U).trans (congrArg (((Ψ i).eval U:ℂ)*·) (reads U))⟩

end YM.Integration.WilsonMeasuredSparseCatalogue
end
