import YM.Integration.WilsonRetainedClusterRead
import YM.Integration.WilsonReportingMolecularMaskRegion
import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum
import YM.Integration.ManuscriptQLocalObservedComponents

/-! A signed deposited cluster on its own physical coarse scene, with every
one of its original inherited rows inside the same sampled integrals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingRetainedMarkedDiagram
open Filter Function Set Finset MeasureTheory Lattice Wilson Merge RG Tree Pressure ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Lotus Daisy RGLocalTaylor MergeProof Marker Extra.Multi
open LocalLTE Matter OPE.Therm RG16 WilsonPositionSeparatedProfileReportingPrimary
open ManuscriptQLocalIntegratedTicket WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {Y:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ α:ℝ} {o:Target.Order G W}
    (H:Cash W s μ L Q o α T Y) (χ:Chi)
    {V ι:Type} [DecidableEq V] {Γ:Marker.Census V} (M:ι→Menu.Hat Γ Y)
    {j n:ℕ} {C' d v B' A b r B q:ℝ} (K:Captain H j C' d v B' A b r B q n χ)

/-- The original signed Ursell material, sampled against its original bare
store for every factor, evaluated without the individual masks. -/
def field (p:H.fragrances) (D:Captain.Oscars (fun i:ι=>(M i).M) p) (U:Config G c) : ℝ :=
  if ∀i, authorized H (p.2 i).val then Ursell.coefficient H.seam p.2 *
    (∏i,WilsonRetainedBareFactor.sampled H χ (fun i:ι=>(M i).M) (p.2 i) (D i) U) / ↑(p.1+1).factorial else 0

include K in
theorem accepted (ℓ:ℕ) (p:H.fragrances) (low:¬Height.tiredN H ℓ p) (D:Captain.Oscars (fun i:ι=>(M i).M) p)
    (U:Config G c) (good:∀X⊆Captain.reachability p,Healthy (Pressure.temp s) X U) :
    activity H χ M p D U=field H χ M p D U := by
  rw [WilsonRetainedClusterRead.low_activity H χ M K ℓ p low D U]
  unfold WilsonRetainedClusterRead.bare field
  split_ifs with licensed
  · congr 2
    apply Finset.prod_congr rfl
    intro i _
    apply RG.masked_eq
    apply good
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩
  · rfl

/-- On the rejected physical field the paid source is the original activity,
not its continuation outside the local chart. -/
def discrepancy (τ:ℝ) (z:Fan.Stars H (fun i:ι=>(M i).M)) (U:Config G c) : ℝ :=
  activity H χ M z.1 z.2 U -
    (House.chilly (G:=G) (cover (Captain.reachability z.1)) τ).indicator (field H χ M z.1 z.2) U

include K in
private theorem cut (τ:ℝ) (ℓ:ℕ) (z:Fan.Stars H (fun i:ι=>(M i).M))
    (low:¬Height.tiredN H ℓ z.1) (ν:Measure (Config G c)) (finite:IsFiniteMeasure ν)
    (wage:ℝ) (recvd:∀U,|activity H χ M z.1 z.2 U|≤wage) (F:Config G c→ℂ) {C:ℝ} (C0:0≤C)
    (good:∀Y⊆Captain.reachability z.1,∀U∈House.chilly (G:=G) (cover (Captain.reachability z.1)) τ, Healthy (Pressure.temp s) Y U)
    (rough:∀U∉House.chilly (cover (Captain.reachability z.1)) τ,‖F U‖≤C) :
    (∫U,‖F U*(discrepancy H χ M τ z U:ℂ)‖ ∂ν)≤
      (C*wage)*ν.real (House.chilly (G:=G) (cover (Captain.reachability z.1)) τ)ᶜ := by
  letI:=finite
  let D:=House.chilly (G:=G) (cover (Captain.reachability z.1)) τ
  have closed:MeasurableSet Dᶜ:=(House.bath _).compl
  have cap:=((integrable_const (μ:=ν) (C*wage)).indicator closed)
  calc
    _≤∫U,Dᶜ.indicator (fun _=>C*wage) U ∂ν:=by
      apply integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) cap
      apply ae_of_all
      intro U
      change ‖F U*((activity H χ M z.1 z.2 U-D.indicator (field H χ M z.1 z.2) U:ℝ):ℂ)‖≤_
      by_cases fit:U∈D
      · rw [Set.indicator_of_mem fit,accepted H χ M K ℓ z.1 low z.2 U (fun X hX=>good X hX U fit),
          sub_self,Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem (show U∉Dᶜ from fun h=>h fit)]
      · rw [Set.indicator_of_notMem fit,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          Set.indicator_of_mem (show U∈Dᶜ from fit)]
        exact mul_le_mul (rough U fit) (recvd U) (abs_nonneg _) C0
    _=_:=by rw [integral_indicator closed,setIntegral_const,smul_eq_mul];ring

variable (R:Run G)

/-- The market opens before the torus, regulator, term, original complex
spectator and deposited roster. Only the spectator on the actual rejected
field is charged. The conductor retains the adjacent fine state. -/
theorem original (simple:G.Simple) (gate:posted R) (p:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀cutoff,(m+1)<cutoff→∀per,
    let β:=R.family.path.levels.clock.hatBeta (m+1)
    let g:=Pert.Asymptotics.regulatorRun R.family cutoff per (m+1)
    let Z:=R.family.path.levels.budget (m+1)
    let ν:=scene R.family.path cutoff per (m+1)
    ∀{P:Teller G} {Q:ConnectedActivityE6.Target G P} {W μ α:ℝ} {f:Side} {O:Target.Order G W}
    {Y:Rep G (R.family.side (m+2) per)} (J:Cash W β μ f Q O α (Testing.ships R.alloy.B cutoff (m+1) per) Y)
    (χ:Chi) {V ι:Type} [DecidableEq V] {Γ:Marker.Census V} (M:ι→Menu.Hat Γ Y)
    {j n:ℕ} {C' d v B' A b r B q:ℝ} (K:Captain J j C' d v B' A b r B q n χ),
    HostQ J K.conduit A B n → Z.order≤j → ∀(a:ℕ),Z.power≤a→
    ∀(ℓ:ℕ) (z:Fan.Stars J (fun i=>(M i).M)),¬Height.tiredN J ℓ z.1→
    let X:=Captain.reachability z.1
    let D:=House.chilly (G:=G) (cover X) (angularCut β)
    let wage:=if ManuscriptQLocalForcedClusters.alive J χ (fun i=>(M i).M) z then Captain.wife K z.1 (fun i=>(M i).M) z.2 a else 0
    ∀root∈X,∀(F:Config G (R.family.side (m+1) per)→ℂ) {C:ℝ},0≤C→(∀U∉D,‖F U‖≤C)→
    (∫U,‖F U*(discrepancy J χ M (angularCut β) z U:ℂ)‖ ∂ν)≤
      (C*wage)*(coverNumber (radiusB β) X:ℝ)*(ε*g^p) := by
  filter_upwards [WilsonReportingMolecularMaskRegion.purchased R simple gate p ep]
    with m sold cutoff live per β g Z ν P Q W μ α f O Y J χ V ι _ Γ M j n C' d v B' A b r B q K host order a power ℓ z low X D wage root rooted F C C0 rough
  have terms:=sold cutoff (by omega) per X
  have recvd:∀U,|activity J χ M z.1 z.2 U|≤wage:=
    ManuscriptQLocalObservedComponents.value J χ M K host Z rfl order a power z root rooted
  have w0:0≤wage:=(abs_nonneg _).trans (recvd 1)
  letI:IsProbabilityMeasure ν:=probability R.makes.wilson (by omega: m+1≤cutoff)
  calc
    _≤(C*wage)*ν.real Dᶜ:=cut J χ M K (angularCut β) ℓ z low ν (inferInstance : IsFiniteMeasure ν) wage recvd F C0 terms.2 rough
    _≤(C*wage)*((coverNumber (radiusB β) X:ℝ)*(ε*g^p)):=mul_le_mul_of_nonneg_left terms.1 (mul_nonneg C0 w0)
    _=_:=by ring

end YM.Integration.WilsonReportingRetainedMarkedDiagram
