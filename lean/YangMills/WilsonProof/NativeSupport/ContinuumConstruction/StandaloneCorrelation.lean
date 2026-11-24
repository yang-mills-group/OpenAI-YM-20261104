import YM.SignedWilsonExpansion.Result.Orders

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped BigOperators Classical ContDiff Topology
universe u
variable {G:Gauge}{H:G.Simple}{ε:ℝ}{e:Axis}{O:OrderS G}{E:Construction.{u} H ε e O}
variable {ξ:Extraction.Order} {V:Vision E ξ} {Z:WilsonPrescription G}{dial:Bool} {Q:Perspective H Z dial}
namespace Vision
open Frames Frames.Cortex Dancer Belfry Belfry.Classroom Belfry.ScaleFits Scale Level GroupS
open SeatsW
attribute [local instance] OS.Spread.Resolution.metric OS.Spread.Resolution.compact OS.Spread.Resolution.borel

/-- The physical field, measured real coupling, finite and limiting correlations, and completed phases
    on one elected pupil. The nominated subtraction datum is independent of the arity and reference. -/
structure StandaloneCorrelation (V:Vision E ξ) (Z:WilsonPrescription G)
    (A:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) : Prop where
  meter : Coupling G (Meter V)
  leading : PhysMS.Leading V.pupil.last (Pre Z V)
  measured (r:ℝ) : cT Z * V.T Z r = (Signal V Z r).re
  negative : cT Z < 0
  oriented (d:ℕ) : oriented V (V.Pre Z) d ∧ oriented V (V.Post Z) d
  finiteAndSmeared (b:ℕ){ι:Type}(l:Filter ι) (r:ι→ℝ) (h:Tendsto r l trail){n d:ℕ} (U:Set (Points n))(B:Roi U){α:Type}(t:Taster α)(u:α→ι→Tags G d n)(p:∀i:α,∀k:Fin n,SeatsW.Salary ℂ l 1 (fun j=> u i j k))(a:Bool) : LinePrices V Z l r t U u a b
  mixedCompact {n d:ℕ}(b:ℕ){ι:Type}(l:Filter ι)(r:ι→ℝ)(q:Tendsto r l trail)(U:Set (Points n))(B:Roi U)(ν:ℝ)(w:Caps n)(m:∀i,w i≤d)(u:ι→∀j:Fin n, Sec G (w j) )(p:∀j:Fin n,SeatsW.Salary ℂ l 1 (fun i=>u i j)) : (∀ a:Bool,∃ C:ℝ,0<C∧ ∀ᶠ i in l,∀ (F:Peers V)(x:Scale.Stage n),x.val∈U→ ‖ Life Z V a (r i) w (u i) x.val F- mote ( Lamplight Z a d ) b x.val ( (V.T Z) (r i) ) (toView w d m G (u i))‖ ≤ C*|(V.T Z) (r i)|^(b+1)) ∧ ∃ C:ℝ,0<C∧ ∀ᶠ i in l,∀ ( F:Peers V )(x:Scale.Stage n),x.val∈U→ ‖ Life Z V true (r i) w (u i) x.val F- polynomial Z A ν d x ( toView w d m G (u i) ) b ( (V.T Z) (r i) )‖≤ C*|(V.T Z) (r i)|^(b+1)
  phases : EveryPhase.Completed V.pupil.last V.pupil.L
  decomposition : (V.pupil.last.α.space).Out
  unity (χ:(V.pupil.last.α.unselected).algebra →⋆ₐ[ℂ] ℂ): ∃! z:(V.pupil.last.α.space).X, (V.pupil.last.α.space).character z=χ
  integrates (r:ℝ)(q:0<r){n:ℕ}(w:Caps n)(u:∀ i:Fin n,Sec G (w i))(a:Bool)(x:Scale.Stage n): Continuous (fun z:(V.pupil.last.α.space).X=> Life Z V a r w u x.val (some z)) ∧ (∫ z:(V.pupil.last.α.space).X, Life Z V a r w u x.val (some z) ∂( (V.pupil.last.α.space).μ ))= Life Z V a r w u x.val none

theorem standaloneFromActualField (V:Vision E ξ) (Q:Perspective H Z dial) :
    StandaloneCorrelation V Z Q.MS := by
  let c := certificate V Q
  let a := pricedLines V Q
  exact ⟨c.meter, c.leading, c.c_paid, c.c_neg, c.spin, a.linearizations, a.trueLetters,
    a.phases, a.decomposition, a.unity, a.integrates⟩
end Vision

theorem standaloneOnNominatedMS (H:G.Simple) (ε:ℝ) (hp:0<ε) (e:Axis) (O:OrderS G) :
    ∃ E:Construction.{u} H ε e O, ∀ ξ:Extraction.Order, ∃ V:Vision E ξ,
      ∀ (Z:WilsonPrescription G) (A:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (dial:Bool),
        ∃ Q:Perspective H Z dial, Q.MS=A ∧ Vision.StandaloneCorrelation V Z A := by
  obtain ⟨E⟩ := Construct.{u} H ε e O hp
  refine ⟨E, ?_⟩
  intro ξ
  obtain ⟨V⟩ := afterElection E ξ
  refine ⟨V, ?_⟩
  intro Z A dial
  obtain ⟨Q, hQ⟩ := compared H Z dial A
  exact ⟨Q, hQ, hQ ▸ Vision.standaloneFromActualField V Q⟩

theorem standaloneOnAppointedRun (H:G.Simple) (ε:ℝ) (hp:0<ε) (e:Axis) (O:OrderS G) (R:XSpace.Run) :
    ∃ Z:WilsonPrescription G, Z.run=R ∧ ∃ E:Construction.{u} H ε e O, ∀ ξ:Extraction.Order,
      ∃ V:Vision E ξ, ∀ (A:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (dial:Bool),
        ∃ Q:Perspective H Z dial, Q.MS=A ∧ Vision.StandaloneCorrelation V Z A := by
  obtain ⟨Z, hZ, _⟩ := perspective H false R
  obtain ⟨E, hE⟩ := standaloneOnNominatedMS.{u} H ε hp e O
  refine ⟨Z, hZ, E, ?_⟩
  intro ξ
  obtain ⟨V, hV⟩ := hE ξ
  exact ⟨V, hV Z⟩

/-- A correlation-only conclusion on the one elected field for every independently nominated datum. -/
theorem standaloneCorrelationOnly (H:G.Simple) (ε:ℝ) (hp:0<ε) (e:Axis) (O:OrderS G) :
    ∃ E:Construction.{u} H ε e O, ∀ ξ:Extraction.Order, ∃ V:Vision E ξ,
      ∀ (Z:WilsonPrescription G) (A:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))),
        Vision.StandaloneCorrelation V Z A := by
  obtain ⟨E, hE⟩ := standaloneOnNominatedMS.{u} H ε hp e O
  refine ⟨E, ?_⟩
  intro ξ
  obtain ⟨V, hV⟩ := hE ξ
  refine ⟨V, ?_⟩
  intro Z A
  obtain ⟨_, _, h⟩ := hV Z A false
  exact h
end YM.Answer.ContinuumLimit
