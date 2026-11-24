import YM.Integration.WilsonFundedWindowCompany
import YM.Integration.WilsonWindowPhysicalCompanyArchive

/-! The physical source menu is chosen before a window's required delay.
This follows the original company's actual sequence of choices. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonFundedWindowMenu
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace


open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
variable {G : Gauge}

/-- A length threshold after the real treasury has been fixed; a later delay
on the actual register, scouts and already selected source menu. -/
def Prepared (goal : Prediction G) (s : Sheet G) (price : MapPrices) : Prop :=
  ∀ (R : Targets s price) (E : Expenses R)
    (flags : ∀ i j, (R i j).table = chart G ∧ (R i j).halo = 500 ∧
      (E i j).earn = rays s i j ∧ (E i j).wanting = -(7/16:ℝ) ∧ (E i j).degrees = 0)
    (C : Programs s) (z : Return.Wages) (bt : Baton G),
    ∃ u : ℕ → ℕ, ∀ l : ℕ → ℕ, u ≤ l → ∀ (D : Rolls (ThroughLaunch.raise s l))
      (w : Return.Wages) (U : ℕ → ℝ) (Z : PhysicalNext.Repeat.Register D E w U)
      (φ : ℕ → ℕ → Postage) (S : Time.Scouts (F := φ)), Pocket Z S →
      ∀ (θ : Protection D) (p : ℕ → ℕ → JointLoad.Heir.Record) (P : PostCost D)
        (menu : ℕ → ℕ → JointLoad.Clockwork.Menu) (V : Delays θ),
        (∀ j i, StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) →
        ∃ W : Delays θ, DelayLe V W ∧ ∀ W', DelayLe W W' →
          ∀ (K : Bar W') (I : Wait K) (hp : Stock.Priced W') (B0 : Directed G I (chart G) price P),
          Extension.UV.Archive B0 → Use.Origins B0 → (∃ f, RankCovariance.ShapePort B0.a B0.M f) →
          let A := (Alloy.mk P θ W' K I hp B0 : Alloy (⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩ : Metals G) D)
          ∀ η q E' J K' b,
            ∀ hZ : Roof.Sheltered (C := C) (B := K') A bt z (rays s) mile b menu p J Z S
                (1/16) (1/16) (1/8) E' q η,
            ∀ hY : WorksIn (D := D) (X := (⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩ : Metals G)) Z P W' S,
            ∀ hm : AsDivisors B0.a.S,
              goal (⟨E',φ,S,η,q,w,K',R,E,U,Z,bt,z,rays s,mile,b,C,menu,p,J,hZ,
                fun i j => (flags i j).1,hY,hm⟩ : Roost.Factor A)

/-- The previous physical-factor purchase is a special case. -/
theorem from_guard {p : Prediction G} {s : Sheet G} {price : MapPrices}
    (paid : Prepaid (@WilsonFundedWindowCompany.Guard G (@p)) s price) :
    Prepared (@p) s price := by
  intro R E flags C z bt
  obtain ⟨floor, buy⟩ := paid R E (fun i j => (flags i j).1) C z bt
    (fun i j => (flags i j).2.2.2.1)
  refine ⟨floor, ?_⟩
  intro l hl D w u Z F S pocket θ stages P menu V quarter
  obtain ⟨W, hVW, issue⟩ := buy l hl D w u Z F S θ stages P V quarter
  refine ⟨W, hVW, ?_⟩
  intro Y hY bar wait hp B _ _ _
  dsimp only
  intro η q exchange aux rider booth hZ works hm
  exact issue Y hY bar wait hp B η q exchange menu aux rider booth hZ works hm ⟨flags,pocket⟩

abbrev AllPrices (p : Prediction G) := ∀ s T, Prepared (@p) s (ThroughLaunch.raging s T)

variable (hG : G.Simple) {s:Sheet G} {O K:MapPrices} {u g k:ℕ→ℝ} {r:Bid.Worth} {T': Further.StrongStartup.Tariffs} {Θ: Extra.Multi.Scope} {v:ℕ→ℕ} (h : ThroughLaunch.Perceived s O K u g k r T' Θ v)

include hG h

/-- Pay at the chosen menu before the original ordered delay is issued. All
the original budgets, measurements and conditional physical outputs are retained. -/
theorem company {pred : Prediction G}
    (paid : Prepared (@pred) s (ThroughLaunch.raging s K)) {τ : ℝ} (ht' : 0 < τ) : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.raging s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) ∧ ∀ l : ℕ → ℕ,j≤l → Nonempty (Rolls (ThroughLaunch.raise s l)) ∧ ∀ D : Rolls (ThroughLaunch.raise s l),
      ∃ y : Return.Wages, ∀ w : Return.Wages,y≤w → ∃ (u' : ℕ→ℝ) (R' : PhysicalNext.Repeat.Register D E w u') (B:ℕ→ℕ→Cafe), ∀ K' : ℕ→ℕ→Postage,
        ∃ (F : ℕ→ℕ→Postage) (S : Time.Scouts (F:=F)), (∀ i j, (F i j).rate ≤ (K' i j).rate) ∧ Pocket R' S ∧ ∀ (E₀ : ℕ→ℕ→Next.Scheduling.Exchange) (ξ : Extra.Multi.Tariff),
          ∃ (q : UVNext.CouplingReset.ResetPrices) (η : ℕ→ℝ) (P : PostCost D), ∀ θ₀ : ℕ → ℝ, (∀ j, 0 < θ₀ j) → ∃ θ : Protection D, θ.theta ≤ θ₀ ∧
           ∃ p : ℕ→ℕ→JointLoad.Heir.Record, (∀ j i,StepStages j i → s.first ≤ i → (p j i).ε ≤ 1/4) ∧
             ∀ (Q : ℕ → ℕ → JointLoad.Clockwork.Menu) (U : Delays θ), ∃ b : ℕ→ℕ→Booth, ∀ J : ℕ→ℕ→JointLoad.Folio.Aux,
               ∃ W : Delays θ, OrderedDelays W ∧ DelayLe U W ∧
               ∀ V, DelayLe W V → ∀ (Z : Bar V) (I : Wait Z) (a : Levels G) (_ : Paid I a),
                 Doors.Budget a k r ∧ Extra.Multi.Prepared Θ ξ (Next.Foundations.localSection G) a ∧ ∃ (hp : Stock.Priced V) (B' : Directed G I (chart G) (ThroughLaunch.raging s K) P),
                   let Y := (Alloy.mk P θ V Z I hp B' : Alloy (ThroughLaunch.bountyV s K l) D)
                   B'.a = a ∧ Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S (1/16) (1/16) (1/8) E₀ q η ∧ Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S τ τ (1/8) E₀ q η ∧ Planned.Port.AtTop B'.kin ∧ Stationary.Artes.Cadre P B'.kin ∧ Next.Free.Amplify B'.M ∧ WorksIn (D:=D) (X:=ThroughLaunch.bountyV s K l) R' P V S ∧
                   Use.Origins B' ∧ (AsDivisors a.S → Use.Offering B' S w (radiusW B)) ∧
                   (∃ f, RankCovariance.ShapePort B'.a B'.M f) ∧
                   ∀ (hc : ∀ i j, (R i j).table = chart G)
                     (hZ : Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S (1/16) (1/16) (1/8) E₀ q η)
                     (hY : WorksIn (D:=D) (X:=ThroughLaunch.bountyV s K l) R' P V S)
                     (hm : AsDivisors B'.a.S),
                     pred (⟨E₀,F,S,η,q,w,B,R,E,u',R',bt,z,rays s,mile,b,C,Q,p,J,hZ,hc,hY,hm⟩ : Roost.Factor Y) := by
  obtain ⟨j, C, z, R, E, bt, hv, hE, purchase⟩ :=
    YM.PhysicalNext.Repeat.Roost.companyWithWindowArchive hG h ht'
  obtain ⟨u, fund⟩ := paid R E hE C z bt
  refine ⟨j ⊔ u, C, z, R, E, bt, hv.trans le_sup_left, hE, ?_⟩
  intro l hl
  obtain ⟨original, extra⟩ := sup_le_iff.mp hl
  obtain ⟨lengths, next⟩ := purchase l original
  refine ⟨lengths, ?_⟩
  intro D
  obtain ⟨y, wages⟩ := next D
  refine ⟨y, ?_⟩
  intro w hw
  obtain ⟨duration, reg, rider, register⟩ := wages w hw
  refine ⟨duration, reg, rider, ?_⟩
  intro initialPost
  obtain ⟨post, scouts, rates, pocket, postage⟩ := register initialPost
  refine ⟨post, scouts, rates, pocket, ?_⟩
  intro exchange tariff
  obtain ⟨q, η, P, protect⟩ := postage exchange tariff
  refine ⟨q, η, P, ?_⟩
  intro θ₀ hθ₀
  obtain ⟨θ, hθ, stages, quarter, delays⟩ := protect θ₀ hθ₀
  refine ⟨θ, hθ, stages, quarter, ?_⟩
  intro menu V
  obtain ⟨W, hVW, predicts⟩ :=
    fund l extra D w duration reg post scouts pocket θ stages P menu V quarter
  obtain ⟨b, booth⟩ := delays menu W
  refine ⟨b, ?_⟩
  intro aux
  obtain ⟨W', ordered, hWW', output⟩ := booth aux
  refine ⟨W', ordered, hVW.trans hWW', ?_⟩
  intro V' hV' bar wait a ha
  obtain ⟨budget, prep, hp, B, hA, shelter, shelterτ, port, cadre,
      amplify, works, origins, offering, archive, rank⟩ := output V' hV' bar wait a ha
  refine ⟨budget, prep, hp, B, hA, shelter, shelterτ, port, cadre, amplify,
    works, origins, offering, rank, ?_⟩
  intro _ hZ hY hm
  exact predicts V' (hWW'.trans hV') bar wait hp B archive origins rank η q exchange aux rider b hZ hY hm

end YM.Integration.WilsonFundedWindowMenu
end

