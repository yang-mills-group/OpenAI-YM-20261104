import YM.Integration.WilsonReportingRetainedMarkedDiagram
import YM.Integration.ManuscriptQLocalSmoothSourceTail

/-! The signed low marked material, integrated on its dated original Wilson
marginal and summed at every root on the same enrolled height account. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingRetainedMarkedPortfolio
open Filter Function Set Finset MeasureTheory Lattice Wilson Merge RG Tree Pressure ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Lotus Daisy RGLocalTaylor MergeProof Marker Extra.Multi
open LocalLTE Matter OPE.Therm RG16 FullQLocal WilsonPositionSeparatedProfileReportingPrimary
open ManuscriptQLocalIntegratedTicket WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open WilsonReportingRetainedMarkedDiagram ManuscriptQLocalMarkedHeightTail
open private cut from YM.Integration.WilsonReportingRetainedMarkedDiagram
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {Y:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ α:ℝ} {o:Target.Order G W}
    (H:Cash W s μ L Q o α T Y) (χ:Chi)
    {V ι:Type} [DecidableEq V] [Fintype ι] {Γ:Marker.Census V} (M:ι → Menu.Hat Γ Y)
    {j n:ℕ} {C' d v B' A b r B q:ℝ} (K:Captain H j C' d v B' A b r B q n χ)

/-- Each joint signed scalar retains its own original deposited finite matrix. -/
def signed (τ:ℝ) (ν:Measure (Config G c)) (F:Fan.Stars H (fun i=>(M i).M) → Config G c → ℂ)
    (z:Fan.Stars H (fun i=>(M i).M)): Poly Γ :=
  (∫U,F z U*(discrepancy H χ M τ z U:ℂ) ∂ν) • matrix H M z

private theorem length_paid (γ k:ℝ) : k*Real.exp (γ*k) ≤ Real.exp ((γ+1)*k) := by
  rw [add_mul,one_mul,Real.exp_add,mul_comm k]
  exact mul_le_mul_of_nonneg_left (le_trans (by linarith) (Real.add_one_le_exp k)) (Real.exp_pos _).le

private theorem funded [Fintype V] (host:HostQ H K.conduit A B n) (Z:BudgetPoint) (th:Z.threshold=Pressure.temp s)
    (ord:Z.order ≤ j) (a:ℕ) (power:Z.power ≤ a) (ℓ:ℕ) (w:V → ℝ) (hw:∀v,0<w v) (hβ:1 ≤ betaF G s L)
    (γ:ℝ) (u:ℝ) (before:Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z=>Height.beaconN H ℓ z*Height.rocket H (fun _=>1) z*Height.markU K (fun i=>(M i).M)
        (fun i=>(betaF G s L)^(-(2:ℝ))*Menu.sumFee (M i) w) z a) (γ+1) u)
    (ν:Measure (Config G c)) (finite:IsFiniteMeasure ν) (τ rate:ℝ) (l0:0 ≤ rate)
    (event:∀X:Support c,ν.real (House.chilly (G:=G) (cover X) τ)ᶜ ≤ (coverNumber (radiusB s) X:ℝ)*rate ∧
      ∀Y⊆X,∀U∈House.chilly (G:=G) (cover X) τ,Healthy (Pressure.temp s) Y U)
    (F:Fan.Stars H (fun i=>(M i).M) → Config G c → ℂ) (C:ℝ) (C0:0 ≤ C)
    (rough:∀z,¬Height.tiredN H ℓ z.1 → ∀U∉House.chilly (G:=G) (cover (Captain.reachability z.1)) τ,‖F z U‖ ≤ C) :
    Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB s)
      (fun z=>if ¬Height.tiredN H ℓ z.1 then Poly.price w (signed H χ M τ ν F z) else 0)
      γ ((C*rate)*((((betaF G s L)^2)^Fintype.card V)*u)) := by
  have sale:=ManuscriptQLocalSmoothSourceTail.funded H M K a ℓ w hw hβ before
  have raw (z:Fan.Stars H (fun i=>(M i).M)):0 ≤ Captain.wife K z.1 (fun i=>(M i).M) z.2 a:=
    mul_nonneg (pow_nonneg (by unfold March.shiftG;positivity) _) (Captain.fareV K z.1 _ z.2)
  intro root
  apply budget_mono (budget_scale (mul_nonneg C0 l0) (sale root))
  · intro z
    by_cases seen:root∈Captain.reachability z.1
    · simp only [if_pos seen]
      apply mul_nonneg _ (Real.exp_pos _).le
      split_ifs <;> first | exact le_rfl | exact Poly.nonnegative hw _
    · simp only [if_neg seen,le_refl]
  · intro z
    by_cases seen:root∈Captain.reachability z.1
    · simp only [if_pos seen]
      by_cases low:¬Height.tiredN H ℓ z.1
      · simp only [if_pos low,signed,Poly.adapted]
        let X:=Captain.reachability z.1
        let k:ℝ:=coverNumber (radiusB s) X
        let amount:=Captain.wife K z.1 (fun i=>(M i).M) z.2 a
        let mass:=Poly.price w (matrix H M z)
        let zread:=fun U=>F z U*(discrepancy H χ M τ z U:ℂ)
        have m0:0 ≤ mass:=Poly.nonnegative hw _
        have a0:0 ≤ amount:=raw z
        have quote (U):|activity H χ M z.1 z.2 U| ≤ amount:=by
          apply (ManuscriptQLocalObservedComponents.value H χ M K host Z th ord a power z root seen U).trans
          split_ifs <;> first | exact le_rfl | exact a0
        have picked:=cut H χ M K τ ℓ z low ν finite amount quote (F z) C0 (event X).2 (rough z low)
        have val:‖∫U,zread U ∂ν‖ ≤ (C*amount)*(k*rate):=(norm_integral_le_integral_norm _).trans
          (picked.trans (mul_le_mul_of_nonneg_left (event X).1 (mul_nonneg C0 a0)))
        change ‖∫U,zread U ∂ν‖*mass*Real.exp (γ*k) ≤ (C*rate)*((mass*amount)*Real.exp ((γ+1)*k))
        calc
          _ ≤ ((C*amount)*(k*rate))*mass*Real.exp (γ*k):=by gcongr
          _=((C*rate)*(mass*amount))*(k*Real.exp (γ*k)):=by ring
          _ ≤ ((C*rate)*(mass*amount))*Real.exp ((γ+1)*k):=mul_le_mul_of_nonneg_left (length_paid γ k) (by positivity)
          _=_:=by ring
      · simp only [if_neg low,zero_mul]
        exact mul_nonneg (mul_nonneg C0 l0) (mul_nonneg (mul_nonneg (Poly.nonnegative hw _) (raw z)) (Real.exp_pos _).le)
    · simp only [if_neg seen,mul_zero,le_refl]

/-- A single eventual calendar, before every regulator and period, applies
to the actual original step and the carried fine representation in its
booked `High`. It spends the *first* pre-field purse on the original roster. -/
theorem original {V:Type} [Fintype V] [DecidableEq V] (Γ:Marker.Census V) (req:FullQLocal.RenderedStep.Request V)
    (R:Run G) (simple:G.Simple) (gate:posted R) (p:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N,(m+1)<N → ∀per,
    let β:=R.family.path.levels.clock.hatBeta (m+1)
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    let ν:=scene R.family.path N per (m+1)
    ∀{P:Teller G} {Q:ConnectedActivityE6.Target G P} {W μ α:ℝ} {L:Side} {O:Target.Order G W}
    {Y:Rep G (R.family.side (m+2) per)} (J:Cash W β μ L Q O α (Testing.ships R.alloy.B N (m+1) per) Y)
    (E:Q.Expense) {high:ℝ},ManuscriptQLocalMarkedHeightRun.High E J req Γ high → 
    ∀(ι:Type) [Fintype ι] (M:ι → Menu.Hat Γ Y) (origin:V → Site (R.family.side (m+2) per)) (w:V → ℝ) (offer:ℝ),
    (∀v,0<w v) → Menu.Offer origin M w Y.p.B Y.p.supportExponent offer → (Fintype.card V:ℝ)*offer ≤ betaF G β L → 
    let ℓ:=ManuscriptQLocalMarkedHeightRun.length req
    ∀(F:Fan.Stars J (fun i=>(M i).M) → Config G (R.family.side (m+1) per) → ℂ) {C:ℝ},0 ≤ C → 
    (∀z,¬Height.tiredN J ℓ z.1 → ∀U∉House.chilly (G:=G) (cover (Captain.reachability z.1)) (angularCut β),‖F z U‖ ≤ C) → 
    Ac.Hit (fun z:Fan.Stars J (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB β)
      (fun z=>if ¬Height.tiredN J ℓ z.1 then Poly.price w (signed J Chi.canonical M (angularCut β) ν F z) else 0)
      (E.earn-1) ((C*(ε*g^p))*(((betaF G β L)^2)^Fintype.card V)) := by
  filter_upwards [WilsonReportingMolecularMaskRegion.purchased R simple gate p ep] with
    m solar N live per β g ν P Q W μ α L O Y J E high housed ι _ M origin w offer hw saved cap ℓ F C C0 rough
  obtain ⟨A,b,C',d,v,s,r,B,e,q,k,K,_,host,_,window,market⟩:=housed
  let Z:BudgetPoint:={ R.family.path.levels.budget (m+1) with
    order:=req.outputFieldOrder,order_ge:=req.field_minimum,power:=req.outputDistanceOrder,power_ge:=req.distance_minimum }
  letI:IsProbabilityMeasure ν:=probability R.makes.wilson (by omega:m+1 ≤ N)
  have l0:0 ≤ ε*g^p:=by dsimp [g,Pert.Asymptotics.regulatorRun];positivity
  have fee:=((market ι M origin w offer hw saved cap).1)
  have bought:=funded J Chi.canonical M K host Z rfl le_rfl req.outputDistanceOrder le_rfl ℓ w hw
    window.1 (E.earn-1) 1 (by simpa only [sub_add_cancel] using fee)
    ν (inferInstance:IsFiniteMeasure ν) (angularCut β) (ε*g^p) l0 (solar N (by omega) per) F C C0 rough
  simpa only [mul_one] using bought

end YM.Integration.WilsonReportingRetainedMarkedPortfolio
