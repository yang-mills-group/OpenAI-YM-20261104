import YM.Integration.RunFormalCoefficients
import YM.Qlocal.Evidence
import YM.Qlocal.Ramp
/-!
# Propagation along a represented Wilson trajectory

`pins` identifies the carrier at a level of a `JourneyK` with the corresponding
run data. Given a `Trip` and an `Agenda`, `continued` identifies the quiet
component with the original density and gives an exact step at the specified
parent addresses. The layouts and the horizon in this comparison belong to the
given journey.

`restore` uses the additional `ShowT`, rank and interval hypotheses to obtain a
`Peak` and a relative budget. Under the positivity and growth assumptions in
`directs`, the run and the program can be chosen together. Their `Appointment`
provides the journey and the eventual stage bounds used in `tickets`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Frigus Time Coat
open Program Program.Camp Program.Certificate
variable {Ω V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge} {m k p N j k' z n l v : ℕ} {δ r θ u E C ℓ: ℝ}

section test
scoped instance independent (D : V→ ComparisonDensity.Address.Orbit): Nonempty (IndependentTests D):= ⟨fun v=>⟨0, ComparisonDensity.Address.Orbit.Bill.zero.more (by norm_num)⟩⟩
end test

section program
variable (X:Run G)
set_option quotPrecheck false
local notation "a"=> X.alloy.B.a
local notation "F"=> X.kit
local notation "C₀"=> X.family
variable (Y : (m:ℕ)→ RG.Rep G (X.alloy.B.a.S.side m p))
    (P:ℕ→Floe.Layout G) (Γ:ℕ→ Floe.Pace.Coin)
    (h : JourneyK X.alloy X.kit X.T P Γ z N p k Y)
local notation "s'"=> (a).clock.J m
local notation "p!"=> (a).budget m
local notation "β"=> X.family.path.β N p
include h
/-- The carrier uses the path, clip, point and view from the given journey. -/
noncomputable def pins (m:ℕ)(hm:z ≤ m)(hN:m ≤ N): Carrier X.family N p m := by
 refine ⟨Y m, ?_,?_,(h.1.walk _ hm hN).truep.point,(h.1.walk _ hm hN).view⟩
 · exact (h.1.walk _ hm hN).truep.path.trans (X.T.sticks N p |>.prices _ (Nat.zero_le _) hN).1.path.symm
 exact (h.1.walk _ hm hN).truep.clip.trans (X.T.sticks N p |>.prices _ (Nat.zero_le _) hN).1.clip.symm
lemma here {m:ℕ}(he:z ≤ m)(hp:m ≤ N): (Y m).beta=(β m)∧ HasSlots (Y m).p (Y m).activities:=⟨(h.1.walk _ he hp).beta, TimeP.allegiance F (h.1.walk _ he hp).truep⟩

variable {η:ℕ→ℝ}{H T:ℕ→ℕ} (Q:Camp X.kit η H T)
variable {o:(m:ℕ)→ V→Site (X.alloy.B.a.S.side m p)}{s:(m:ℕ)→ V→Support (X.alloy.B.a.S.side m p)}
    (j:ℕ) (u:V→ℝ)(c:B.Mode→ℝ)(U:Taste Ω (o j) (Y j) B)
    [Fintype V] [Nonempty V] [Nonempty Ω]
    (hC:Spirit c) (hu:∀ i,0 < u i)
    (Z:(m:ℕ)→Taste Ω (o m) (Y m) B)(M:Protocol X.alloy.B.a p Ω B Y o) (hx: Trip Q o s u c j U M Z z)
    (hS:Agenda (A:=X.alloy) o s z j) (hv:j ≤ N)(hr:z ≤ j)
include hx hv hu hC hS
lemma continued (he:z ≤ m)(h₁:m ≤ j) : HasSlots (Y m).p (Y m).activities ∧
     (β m)∈ band a m ∧ M m (Z m) ∧ (Y m).beta= (β m) ∧
     (∀ x Vw, (((Z m).leaf x).density Vw).part B.quiet=((X.family.path.rep N p m).eval Vw:ℂ)) ∧
     ∀ (hk:m < j), ExactStep (X:=Ω) (pins X Y P Γ h (m+1) (by omega) (by omega)) (pins X Y P Γ h m he (by omega)) (o (m+1)) (o m) (Z (m+1)) (Z m):= by
 obtain ⟨hK,hP⟩:= here X Y P Γ h he (h₁.trans hv); have hy:= h.1.walk _ he (h₁.trans hv); let x:Ω:= Classical.ofNonempty; refine ⟨hP,(X.T.sticks N p|>.prices m (by omega) (h₁.trans hv)).2,hx.intern m he h₁|>.1,hK, ?_,?_⟩
 · intro x U; rw [← show (Y m).eval=(X.family.path.rep N p m).eval from hy.view]; exact Peak.same (hx.intern m he h₁|>.2.2) (rent_spend (shift_pos (zero_lt_one.trans_le (Q.scaled ..)) hu) hC.fresh) x hy.truep.valid U
 intro hk; refine ⟨fun i=>(congr_fun (hS.root m he hk).symm i),fun x=>?_⟩; have hz:=hx.move m he hk |>.2 x; rw [(here X Y P Γ h (show z ≤ m+1 from (by omega)) (hk.trans_le hv)).1] at hz; exact hz.symm

local notation "f'"=> Hull.soft δ (β (m+1))
local notation "v★"=> Hull.divisor (a) m
local notation "θ★"=> Coat.gStep (β (m+1))^v
omit hS
lemma restore (Yφ: ShowT F η H T Q m l v δ) (h1 : m < j)(h2 : z ≤ m)(hr:Certificate.Rank l B)(hp: Hull.Close (a) z j):
     Peak (Y m) (o m) (Z m) (rent u c) (Y m).p.supportExponent (Hull.soft δ (β (m+1))) ((a).clock.forcedAllowance m * θ★)∧
     Nonempty (RelativeBudget (p!) (Z m) u v★ c ((Real.exp 1+1)*Hull.soft δ (β (m+1))) (v★*θ★)) := by
 let i:= (m+1); have he:= Certificate.growing F η H T X.T Q h o s u c j hC hu U M Z hx hv v Yφ h1 h2 hr hp; rw [(here X Y P Γ h (show z ≤ m+1 from (by omega)) (h1.trans_le hv)).1] at he
 exact ⟨ he.1,(h.1.walk _ h2 (by omega)).truep.point ▸ he.2 ⟩
end program
variable (R:Run G)(g:G.Simple)(η:ℕ→ℝ)(H T:ℕ→ℕ)
    (Q:Camp R.kit η H T)
structure Appointment : Prop where
 passports : ∃ (U:Floe.Step.PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (G' : U.Tab R.rolls), TicketP R.alloy R.kit U G' ∧ ∀ (k m N:ℕ),(Burn.horizon k)+2 ≤ R.family.path.levels.clock.J m→ m ≤ N → ∃ (W:ℕ→ Floe.Layout G)(Γ:ℕ→Floe.Pace.Coin), Floe.Step.PlanV.Path U R.alloy G' (Burn.horizon k) N m W Γ ∧∀ p:ℕ,∃ x,JourneyK R.alloy R.kit R.T W Γ m N p k x
 start_all : ∀ k l:ℕ,∀ d:ℝ,0<d→∀ᶠ z in atTop,∀ i≥ z,ShowT R.kit η H T Q i l k d
include g
lemma directs (d:ℝ)(hd:0<d)(hT:Tendsto T atTop atTop)(hη:∀ i,0 < η i) :∃ (R:Run G)(Q:Camp R.kit η H T), R.family.path.levels.clock.kernel.penalty=d ∧ Q.height=(fun i=> H (R.alloy.B.a.clock.J (i+1))) ∧ Appointment R η H T Q:= by
 obtain ⟨B,hB,hT'⟩:= Run.rampK g (Program.sold η H T g hη) d hd
 obtain ⟨Q,hQ⟩:= Program.supplier B.kit η H T hT' (d:=fun m=>H (B.alloy.B.a.clock.J (m+1))) (fun i=>le_refl _)
 exact ⟨B,Q,hB,hQ, Station.journeys _ _ Q.station _ B.tuning.receipts g,fun k l hp hv=> supplied B.kit g η H T Q hT k l hp hv⟩
omit g
lemma tickets (X:Appointment R η H T Q) (k l k':ℕ)(d:ℝ)(hp:0<d) : ∃ (U:Floe.Step.PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (G' : U.Tab R.rolls), TicketP R.alloy R.kit U G' ∧ ∀ᶠ m in atTop,∀ N≥m, (∀ i≥m,ShowT R.kit η H T Q i l k' d)∧∃ (W:ℕ→ Floe.Layout G)(Γ:ℕ→Floe.Pace.Coin), Floe.Step.PlanV.Path U R.alloy G' (Burn.horizon k) N m W Γ ∧∀ p:ℕ,∃ x,JourneyK R.alloy R.kit R.T W Γ m N p k x:= by
 obtain ⟨U,F,h,hp'⟩:=X.passports; refine ⟨U,F,h,?_⟩; filter_upwards [X.start_all k' l d hp,(R.family.path.levels.fits.deep.eventually_ge_atTop (Burn.horizon k +2))] with m hv hl N hN using ⟨hv,hp' k m N hl hN⟩
end YM.Qlocal.Actual
