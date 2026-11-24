import YM.Integration.OriginalMarkedHistoryLog
import YM.Integration.OriginalMarkedBirthStencil
import YM.Integration.OriginalMarkedThermalPower
import YM.Integration.QLocalNormalizedQBirth

/-! All original signed connected Q responses to an independent finite
physical birth at every earlier scale, with a uniform prescaled hot error. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedHistoryBirth
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker FVA1 OPE.Therm
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extra.Trajectories
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V→MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)
local notation "Γ" => Stock.census V
local notation "rq" => ActualOriginalQPointSetup.request R u J

def coefficient (power : ℕ) : ℝ :=
  let b := (Fintype.card V:ℝ)*((2:ℝ)^ActualOriginalQLayout.rankCap R u*1)
  OriginalMarkedHistoryLog.tariff (Fintype.card V) power b*
    (((Fintype.card PlaqAxes*4:ℕ):ℝ)*81*Real.exp (ActualOriginalQPointCover.bound R u:ℝ)*b)

def input {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (z.level+1) z.period))
    (μ : ℝ) (orders : V → ℕ) (x : IndependentTests (ActualOriginalQPointSetup.request R u J).tests) : Config G (R.family.side (z.level+1) z.period) → Poly (Stock.census V) := ((ActualOriginalQInitialPreparation.input R hG u J A z Q o μ orders).leaf
  (testInclusion (ActualOriginalQPointSetup.request R u J).tests x)).density

def cooled {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (z.level+1) z.period))
    (μ : ℝ) (orders : V → ℕ) (x : IndependentTests (ActualOriginalQPointSetup.request R u J).tests)
    (T : Config G (R.family.side (z.level+1) z.period)) : Poly (Stock.census V) :=
  let P := ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
  let F := R.family.path.rep z.cutoff z.period (z.level+1)
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  F.eval T • Poly.pass (ManuscriptQLocalOriginalConditionalTail.source P F.p g x 1 T)

def response {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (z.level+1) z.period))
    (μ : ℝ) (orders : V → ℕ) (x : IndependentTests (ActualOriginalQPointSetup.request R u J).tests)
    {k : ℕ} (hk : k ≤ z.level+1) (U : Config G (R.family.side k z.period)) : Poly (Stock.census V) :=
  connected (actualSignedTransport R.family (N:=z.cutoff) (input R hG u J A z Q o μ orders x) hk U)-
  connected (actualSignedTransport R.family (N:=z.cutoff) (cooled R hG u J A z Q o μ orders x) hk U)

private theorem accounting (T S A d b : ℝ) :
    T*(S*((2:ℝ)*1+1)^4*(A/1)*d*b)=(T*(S*81*A*b))*d := by ring

section Point
variable (z : LocalFormal.Datum R.family Γ) (Q : MS.Land.Prescription B)
  (o : V→Site (R.family.side (z.level+1) z.period)) (μ : ℝ) (orders : V→ℕ)
  (x : IndependentTests (rq).tests)
local notation "P₀" => ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
local notation "F₀" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "g₀" => regulatorRun R.family z.cutoff z.period (z.level+1)

private def fineLoss {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (z.level+1) z.period))
    (μ : ℝ) (orders : V → ℕ) (x : IndependentTests (ActualOriginalQPointSetup.request R u J).tests) : ℝ :=
  let side := R.family.side (z.level+1) z.period
  let P : MarkedPackets (ActualOriginalQPointSetup.request R u J).tests G side (Stock.census V) :=
    ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
  let budget : BudgetPoint := (R.family.path.rep z.cutoff z.period (z.level+1)).p
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  let raw : Config G side → Poly (Stock.census V) := P.read (testInclusion (ActualOriginalQPointSetup.request R u J).tests x) g
  let fine : Config G side → Poly (Stock.census V) := ManuscriptQLocalOriginalConditionalTail.source P budget g x 1
  let measured : Measure (Config G side) := scene R.family.path z.cutoff z.period (z.level+1)
  ∫ T : Config G side, Poly.price (fun _ : V=>(1:ℝ)) (raw T-fine T) ∂measured


end Point

include hG A in
/-- The threshold is selected before all upper cutoffs, periods, prescribed
fields, tests and lower stopping scales. The exact normalized Haar chain can
have any length, including zero. -/
theorem physical (W : Poetry R.family.path.levels) (power a : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, ∀(z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀(Q : MS.Land.Prescription B) (o : V→Site (R.family.side (z.level+1) z.period))
        (μ : ℝ) (orders : V→ℕ) (x : IndependentTests (rq).tests)
        (k : ℕ) (hk : k ≤ z.level+1),
      let measured := fun U=>(Poly.price (fun _ : V=>1) (response R hG u J A z Q o μ orders x hk U))^(power+1)
      Integrable measured (scene R.family.path z.cutoff z.period k) ∧
      ∫ U,measured U ∂scene R.family.path z.cutoff z.period k ≤
        ε*(regulatorRun R.family z.cutoff z.period (z.level+1))^a := by
  obtain ⟨hotLevel,hot⟩ := eventually_atTop.1 (ManuscriptQLocalIncidentMasks.hot W hG R.makes.wilson 1)
  filter_upwards [eventually_ge_atTop hotLevel,eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u),
    OriginalMarkedThermalPower.actual R hG (coefficient R u power) hε a]
    with m enough deep soft z hz Q o μ orders x k hk
  subst m
  have cash := hot (z.level+1) (enough.trans (Nat.le_succ _))
  let P := ActualOriginalQInitialInput.packets R hG u J A z Q o μ orders
  let F := R.family.path.rep z.cutoff z.period (z.level+1)
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  let n := Fintype.card V
  let b := (n:ℝ)*((2:ℝ)^P.rankCap*1)
  let μf := scene R.family.path z.cutoff z.period (z.level+1)
  letI : IsProbabilityMeasure μf := probability (H:=R.family.path) (p:=z.period) R.makes.wilson z.below
  let q := OriginalMarkedBirthStencil.mesh
  have H := OriginalMarkedBirthStencil.paid R hG u J A z Q o μ orders q g
  have cover : Real.exp (q.supportExponent*(ActualOriginalQPackets.packetCover Q
      (ActualOriginalQPointSetup.pointDatum R J z.period (z.level+1) o) u
      (μ-R.family.S.scale z.cutoff) orders z.cutoff q:ℝ)) ≤ Real.exp (ActualOriginalQPointCover.bound R u:ℝ) := by
    apply Real.exp_le_exp.mpr
    simpa only [q,OriginalMarkedBirthStencil.mesh,one_mul] using
      (Nat.cast_le.mpr (OriginalMarkedBirthStencil.covered R u J z Q o μ orders q) :
        (ActualOriginalQPackets.packetCover Q _ u _ orders z.cutoff q:ℝ)≤_)
  let X := P.read (testInclusion (rq).tests x) g
  let Y := ManuscriptQLocalOriginalConditionalTail.source P F.p g x 1
  have hX T := ManuscriptQLocalOriginalFineMaskLoss.original_rows P H x T
  have hY T := ManuscriptQLocalOriginalFineMaskLoss.regular_rows P H x F.p T
  have hq T := ManuscriptQLocalOriginalFineMaskLoss.means_quiet P H x F.p T
  have income := QLocalNormalizedQBirth.source R hG u J A z Q o μ orders (deep.trans (Nat.le_succ _))
    (testInclusion (rq).tests x)
  have joined := OriginalMarkedHistoryLog.received R.family R.makes H.positive z.below hk X Y
    (input R hG u J A z Q o μ orders x) (cooled R hG u J A z Q o μ orders x)
    (ManuscriptQLocalOriginalFineMaskLoss.full_borel P x) (ManuscriptQLocalOriginalFineMaskLoss.mask_borel P x F.p)
    (fun T=>(hX T).2) (fun T=>(hY T).2) (fun T=>(hq T).1) (fun T=>(hq T).2) income (fun _=>rfl) power
  have fine := ManuscriptQLocalOriginalFineMaskLoss.integrated P H x μf F.p
    (pow_nonneg (Real.exp_pos _).le 1) cover (fun _=>cash z.cutoff z.below z.period _)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have drop := mul_le_mul_of_nonneg_left fine (OriginalMarkedHistoryLog.nonnegative n power hb)
  have rank : P.rankCap=ActualOriginalQLayout.rankCap R u := rfl
  have cap : ManuscriptQLocalOriginalFineMaskLoss.bound P (budget:=1) = b := rfl
  let axes : ℝ := ((Fintype.card PlaqAxes*4:ℕ):ℝ)
  let support := Real.exp (ActualOriginalQPointCover.bound R u:ℝ)
  let fee := R.family.path.levels.clock.forcedAllowance (z.level+1)
  have quote := accounting (OriginalMarkedHistoryLog.tariff n power b) axes support fee b
  have stated : (OriginalMarkedHistoryLog.tariff n power b*(axes*81*support*b))*fee ≤ ε*g^a := by
    simpa only [coefficient,b,n,rank,axes,support,fee,g] using soft z.cutoff z.period z.below
  refine ⟨joined.1,(joined.2.trans drop).trans ?_⟩
  calc _ = (OriginalMarkedHistoryLog.tariff n power b*(axes*81*support*b))*fee := by
             simpa only [cap,q,OriginalMarkedBirthStencil.mesh,Nat.cast_one,pow_one,fee,Calendar.forcedAllowance] using quote
       _ ≤ _ := stated

end YM.Integration.OriginalMarkedHistoryBirth
end
