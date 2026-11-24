import YM.Integration.FVA1Physical.Sources.Round2.FieldBudget
import YM.Integration.FVA1Physical.Sources.Round2.AdditiveRatio
import YM.Integration.FVA1Physical.Round2.FieldLocalWilson
import YM.MSbar.Mosaic.Pay

/-! Conditional Haar reading of a finite mixed physical stencil on an inherited
Wilson stage. The real action estimate comes from the measured stage and the
physical source estimate from its separately computed FVA2 Taylor rows. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open MSbar.Jade MSbar.Lapaz MSbar.Parma MSbar.Tramp Push.Uniform Next.SectorChange Further.GaussianScalar
open MeasureTheory Matrix Metric YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

def stencilSalary (p k L : ℕ) (part : Bool) (hk : 1 ≤ k) :=
  (field_projection_budget J p k L part hk).choose

theorem stencilSalary_pos (p k L : ℕ) (part : Bool) (hk : 1 ≤ k) :
    1 ≤ stencilSalary J p k L part hk := (field_projection_budget J p k L part hk).choose_spec.1

variable (A : Mosaic.Issue G) (χ : ChartRatio G) (V : Voice G) (P : Palisade) (K : Patch) (H H' : RG.Stage)
variable (p k L : ℕ) (hk : 1 ≤ k) (Z : Positions (Primary A.c G)) (b : Site A.f)
variable (O : Ages) (pay : Salary) (cutoff : ℝ→ℝ) (part : Bool) (o : ι→Site A.f)
variable {u : G.ColorIndex} {x e d D0 B actionBound cost stipend : ℝ}
local notation "F"=>A.F
local notation "g"=>A.fClock
local notation "R"=>A.pre
local notation "A₀"=>postcard G A.c g Z
local notation "ν"=>vest (priced A.F A.v A.pre.clip A.pre.path) (A.fClock•Z)
local notation "y"=>tip G K.L x
local notation "X"=>boxX y b
local notation "Y"=>boxY y b
local notation "Ω"=>hotel A.F X Y V A₀ ν (pillow y) (room y)
local notation "R'"=>woolModel A.F X V R Y A.v A₀ ν (pillow y) (room y)
local notation "θ"=>jointFieldBank J A o part
local notation "σ"=>k*(p+2)
local notation "a"=>αm y
local notation "s₀"=>Ruby.crownP A.F A.M Z

/-- All source and analytic charges use precisely the original Mosaic projection,
including the real conditional vacuum. The stochastic replacement of the physical
source is additive; only the pre-existing action salary is required. -/
theorem projection_field (patch : K=A.S.patch)
    (season : Season V H H' x A.pre A.post A.S (courage G K.L x))
    (clear : Clear G V) (fest : A.Festival χ p u) (charts : LocalRatio χ)
    (suite : Suite V χ A.F X Y A₀ A.v A.pre ν (pillow y) (room y)
      (rot P y) (maxZ G P y) (topP V P y) D0 (linCash A.F (A.fClock•Z)))
    (cal : Mosaic.Issue.Calibrate A V P X Y (A.fClock•Z) y e d) (clock : A.fClock ≤ 1)
    (hat : Lodge.Hat k O.w B cutoff) (high : 1 ≤ hatW y)
    (hd : ∀ i ≤ p, Tokew (address A.F G) a 0 σ 0 (PowerSeries.coeff i (barbed A.F A.v χ A.T)) actionBound ∧
      (PowerSeries.coeff i (barbed A.F A.v χ A.T)).totalDegree ≤ σ)
    (proj : Mosaic.Issue.Projection A χ P V O pay Z p k b y actionBound (stencilSalary J p k L part hk) cost stipend D0)
    (near : ∀ j:Slice J,separation b (legs J o j).1 ≤ L*closeN y)
    (live : ∀ i, slotEdge J A.S A.F o i ∈ board A.F X) (small : 3*shade G*rot P y ≤ fieldRadius J part p)
    (U : Config G A.f) (hU : U∈Ω) :
    |Rota.resample F (board F X) R' Ω (fun B=>look part (tally J o B)) U -
      taste p (innerColumn A χ V y (g•Z) b U θ p) g| ≤
      fieldCost J part p*(3*shade G*rot P y)^(p+1) + Salary.stamp pay p (Fintype.card (Lake A.F X G)) g cost stipend := by
  let port:=proj.funds
  have vows:=proj.epic
  have ha : 0 ≤ a:=zpow_nonneg (zero_le_one.trans high) _
  have source:=(field_projection_budget J p k L part hk).choose_spec.2 y high A o b near
  obtain ⟨F',trend⟩:=fest.preT
  obtain ⟨tail,κ,tailFit,tailPos,hκ,hTail⟩:=port.crew
  obtain ⟨bound,clip,actionCap,sourceCap⟩:=port.beads
  have laws:=season.case_
  rw [←patch] at laws
  have hβ:0<A.pre.beta:=(half_pos (zero_lt_one.trans laws.enough)).trans_le laws.beta
  have hg:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have same : A.pre.beta = g⁻¹^2 := by unfold Mosaic.Issue.fClock cue; rw [inv_inv,Real.sq_sqrt hβ.le]
  let m:=sampleY F R A.v V X Y U (g•Z) ∘ includeX A.F X
  let mask:=clipM A.F X Y Ω χ g m U
  have born0 : (0:SpaceP A.F X G)∈mask:=Lapaz.born F R A.v V χ X Y U g Z suite hg hU
  have geom:=port.receipt U hU
  have center:= (geom 0 born0).1
  have room (v:SpaceP A.F X G) (hv:v∈mask) : ‖v‖ ≤ bound := by
    apply le_of_mul_le_mul_left _ hg
    nth_rw 1 [← Real.norm_of_nonneg hg.le];rw [←norm_smul]
    exact ((suite.exports U hU g hg).2.1 _ hv).trans clip
  let base:= meetVar Z (berth F R A.v V X Y U Z g 0)
  let act:=barbed F A.v χ A.T
  let z:=vene X A.F G
  have both (v:SpaceP A.F X G) :
      Belt p (micro base z (Rewind act base) v) ≤ pay.payQ*(1+‖v‖)^pay.m ∧
      Belt p (micro base z θ v) ≤ pay.payH*(1+‖v‖)^pay.m := by
    have hp0:=hd p le_rfl|>.1.1
    have hb0:=source p le_rfl|>.1.1
    have hs : 0 ≤ O.outer := (norm_nonneg _).trans center
    have hq : 0 ≤ pay.payQ := le_trans (by unfold loftM; positivity) port.emblem
    have hj : 0 ≤ pay.payH := le_trans (by unfold Bmark barry; positivity) port.limb
    have pw := pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) port.origin
    exact ⟨(Lapaz.portion F R A.v V X Y U g Z v p act hd ha center).trans
      (mul_le_mul port.emblem pw (by positivity) hq),
      (Lapaz.baro F R A.v V X Y U g Z v p θ σ b a source center ha).trans
      (mul_le_mul port.limb pw (by positivity) hj)⟩
  have env : RG.Envelope (fun B : Config G A.f=>look part (tally J o B)) :=
    Lumen.Planet.havenreal ((look part).continuous.comp (Spool.tally_cont J o))
  have funded : 0 ≤ stipend := by
    have birth:=proj.payQ 0 (Nat.zero_le _)
    exact (pow_nonneg hg.le (p+1)).trans (by simpa only [Emark,pow_zero,mul_one] using birth)
  rw [←field_local_inner J A V χ y b U Z p cutoff s₀ o part suite.positivity trend.bond hg.ne']
  refine additive_ratio F R A.v V χ X Y U g Z suite hg hU A.T p _ cutoff s₀ cal.first.extendsX charts clear
    clock trend.bond θ env pay stipend funded cal.fuel port.caps ((Lapaz.muscle F R A.v V χ X Y U g Z suite hg hU tailFit
      tailPos port.caps hκ).trans hTail) port.sealed both
    (Lapaz.rocky F R A.v V X Y U g Z A.T p cutoff s₀ hat (fun x hx=>⟨(vows.sC x hx).1,(vows.sC x hx).2.1⟩)).measurable
    (fun i=>(Lapaz.withinW F R A.v V X Y U g Z i A.T p cutoff s₀ hat (fun x hx=>⟨(vows.sC x hx).1,
      (vows.sC x hx).2.1⟩) vows.posU).trans port.costU) port.ticks ?_ ?_ ?_ port.jam
  · intro i hi
    have hq : 0 ≤ pay.payQ:=by simpa using (Belt_pos p _).trans (both 0).1
    have hj : 0 ≤ pay.payH:=by simpa using (Belt_pos p _).trans (both 0).2
    have pw : (1+‖i‖)^pay.m ≤ (1+bound)^pay.m := by gcongr; exact room i hi
    exact ⟨(both i).1.trans ((mul_le_mul_of_nonneg_left pw hq).trans actionCap),
      (both i).2.trans ((mul_le_mul_of_nonneg_left pw hj).trans sourceCap)⟩
  · intro v hv
    exact (Jade.logVic F R A.v V P χ X Y U g Z A.post.path A.post.clip A.ρ suite hg 0 v hU A.T p same
      hv born0 charts cal.first.extendsX clear trend season.bends.1 fest.critical fest.classical_ s₀ cutoff vows
      cal.first fest.real0 hat port.charge geom).trans port.titan
  exact (field_salary_input J part p).choose_spec.choose_spec.2.2 A V clear χ charts o X Y live U Z g _ _ _ _ _
    hg small cal.first.extendsX suite.seat


end YM.Integration.FVA1Physical.Round2.Curvature
