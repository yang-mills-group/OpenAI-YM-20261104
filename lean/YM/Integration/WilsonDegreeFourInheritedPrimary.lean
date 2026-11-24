import YM.Integration.WilsonInheritedRegisteredField
import YM.Integration.WilsonRegisteredDegreeFourCovariance

/-! The inherited degree-four primary and the independently submitted fresh
primary in the original connected experiment, after removing their constant
difference on the full Wilson conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonDegreeFourInheritedPrimary
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension Push.SectorMeasure
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Source
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open private real_test from YM.Integration.WilsonRegisteredDegreeFourCovariance
open scoped Classical Topology
variable {G : Gauge} (R : Run G)
local notation "D" => R.family.path

private theorem core (y : R.family.label 4) {n:Side} (o : Site n) (θ : ℝ) (U : Config G n) :
    let L := R.family.labels.level 4
    let S := R.family.localSection 4
    Push.Local.primary S o θ (L.core y) U = Push.Local.primary S o θ y U-y 0 := by
  intro L S
  have again : L.core (L.core y) = L.core y := by
    funext i;by_cases e:i=0 <;> simp [Labels.Frame.core,Function.update,e]
  change (L.core y) 0+masked θ (S.footprint o) (S.places (L.scaled θ⁻¹ (L.core (L.core y))) o) U =
    y 0+masked θ (S.footprint o) (S.places (L.scaled θ⁻¹ (L.core y)) o) U-y 0
  rw [again]
  have zero : (L.core y) 0=0 := by simp [Labels.Frame.core]
  rw [zero];ring

theorem purchased (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (D).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (q grade:ℕ) (order:q+5≤grade) {ε:ℝ} (he:0<ε) :
    let d:Unit→ℕ:=fun _=>4
    ∀ᶠ m:ℕ in atTop,∀ N (interior:m+1<N) per (v w:R.family.label 4)
      (x:Site (R.family.side N per)) (o:Site (R.family.side (m+1) per))
      (T:Forest ((D).levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
      (η χ:ℂ→L[ℝ]ℝ),
    let roots:Unit→Site (R.family.side (m+1) per):=fun _=>o
    let A:=(D).rep N per (m+1)
    let Z:=WilsonInheritedRegisteredField.packet (C:=R.family) R.makes interior.le w o
    let F:=fun U=>η (actualTransport R.family (N:=N) (R.family.O N per v x) interior.le U)
    let E:=actualAverage R.family (N:=N) (p:=per) (m:=m) (E:=ℝ)
    let H:=fun U=>F U-E F V
    let α:=(((R.family.S.a (m+1):ℂ)^4)⁻¹)
    let s : R.family.label 4 := (Z.x : R.family.label 4)-(R.family.factory 4 (m+1) per).terminal.symm w
    let y:∀i,R.family.label (d i):=fun _=>(R.family.labels.level 4).core s
    let b := fun U=>χ (α*(Z.exponentialEntry o (R.family.localSection 4) A U-∑'i,Z.maskedTerm A i U)
      -R.family.O (m+1) per w o U-α*s 0)
    let B:=incident R T d roots
    let C:=cold R m per d roots
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    let retained:=∫z in panel R m per d roots T r,
      WilsonCoherentRetainedDriver.value R interior grade T B V z*H (state T B z)*
        χ (α*polynomial T B R d A.p.threshold y roots (q+2*reserve R d) z) ∂law P r T B
    |E (C.indicator (fun U=>H U*b U)) V-retained|≤
      δ*E (C.indicator (fun U=>|H U*b U|)) V+
        (2*((‖χ‖*‖α‖)*(δ*originalMass R d y)))*E (C.indicator (fun U=>|H U|)) V := by
  intro d
  filter_upwards [WilsonCoherentRetainedExperiment.measured R simple marks fees slow J clear P hp pr sr d q grade order he,
    WilsonCoherentMeasuredStencil.on_event R d simple] with m paid present N interior per v w x o T V η χ
  intro roots A Z F E H α s y b B C δ retained
  let L:=R.family.labels.level 4
  let S:=R.family.localSection 4
  let t:=A.p.threshold
  let f:= (R.family.factory 4 (m+1) per).terminal.symm w
  let Y:∀i,R.family.label (d i):=fun _=>f
  let file U:=χ (α*∏i,Push.Local.primary (R.family.localSection (d i)) (roots i) t (y i) U)
  have Hdata:=WilsonMeasuredInheritedGauge.occupied R.family R.makes (per:=per) interior.le v x
  have eF:Envelope F:=real_test Hdata.1 η
  have envelope : Envelope H:=by simpa only [H,sub_eq_add_neg] using eF.add (Envelope.const (-E F V))
  have gauge : GaugeInvariant H:=fun g U=>congrArg (fun a=>η a-E F V) (Hdata.2 g U)
  have tested:=paid N interior per y roots T V α χ H envelope gauge
  have shape (U) (cold:U∈C) : b U=file U := by
    have flat := present N per interior.le roots Y U cold
    simp only [Fintype.prod_unique] at flat
    have threshold : t = (D).levels.clock.threshold (m+1) :=
      congrArg (fun a=>a.threshold) (R.makes.wilson.represents N per (m+1) interior.le).vac
    have fresh : R.family.O (m+1) per w o U=α*Push.Local.primary S o t f U := by
      change _ = α*Push.Local.primary (R.family.localSection (d default)) (roots default) t (Y default) U
      rw [←flat]
      change _ = α*Push.Local.presented S o t f U
      rw [threshold];rfl
    have raw : Z.exponentialEntry o S A U = Push.Local.primary S o t Z.x U+∑'i,Z.maskedTerm A i U := rfl
    have linear : Push.Local.primary S o t s U=Push.Local.primary S o t Z.x U-Push.Local.primary S o t f U :=
      congrFun ((Push.Local.primary S o t).map_sub Z.x f) U
    dsimp only [b,file]
    simp only [Fintype.prod_unique]
    change χ (α*(Z.exponentialEntry o S A U-_)-R.family.O (m+1) per w o U-α*s 0)=
      χ (α*Push.Local.primary S o t (L.core s) U)
    rw [raw,fresh,core,linear]
    congr 1;ring
  have changeField (a:ℝ→ℝ) : C.indicator (fun U=>a (H U*file U))=C.indicator (fun U=>a (H U*b U)) := by
    funext U;by_cases cold:U∈C
    · simp only [indicator_of_mem cold,shape U cold]
    · simp only [indicator_of_notMem cold]
  change |E (C.indicator (fun U=>H U*file U)) V-retained|≤
    δ*E (C.indicator (fun U=>|H U*file U|)) V+_*E (C.indicator (fun U=>|H U|)) V at tested
  have eq:=changeField id
  simp only [id_eq] at eq
  rw [eq,changeField abs] at tested
  exact tested

end YM.Integration.WilsonDegreeFourInheritedPrimary
