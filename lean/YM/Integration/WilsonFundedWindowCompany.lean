import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply

/-! Buy the marked window at the original company's actual inputs. A guarded
purchase can ask for the five physical treasury equalities and the joint
register/scouts certificate. This theorem discharges both at the emitted factor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonFundedWindowCompany
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

/-- The five physical choices used in the source estimates, and the actual
joint register/scout certificate, all on this one factor. -/
def PhysicalInputs : Prediction G := fun {M} {_} {_} F =>
  (∀ j i, (F.target j i).table = chart G ∧ (F.target j i).halo = 500 ∧
    (F.expense j i).earn = rays M.p j i ∧ (F.expense j i).wanting = -(7/16:ℝ) ∧
    (F.expense j i).degrees = 0) ∧ Pocket F.shape F.scout

def Guard (p : Prediction G) : Prediction G := fun {_} {_} {_} F => PhysicalInputs F → p F

/-- An ordinary funded prediction can ignore the extra physical facts. -/
theorem of_prepaid {p : Prediction G} {s : Sheet G} {K : MapPrices}
    (paid : Prepaid (@p) s K) : Prepaid (@Guard G (@p)) s K := by
  intro R E hc C z bt target
  obtain ⟨floor, buy⟩ := paid R E hc C z bt target
  refine ⟨floor, ?_⟩
  intro l hl D w u Z Q S θ stages post V quarter
  obtain ⟨W, hVW, issue⟩ := buy l hl D w u Z Q S θ stages post V quarter
  refine ⟨W, hVW, ?_⟩
  intro V' hV' bar wait priced directed
  dsimp only
  intro η q exchange menu aux quotes booth hZ hY hm _
  exact issue V' hV' bar wait priced directed η q exchange menu aux quotes booth hZ hY hm

variable (hG : G.Simple) {s:Sheet G} {O K:MapPrices} {u g k:ℕ→ℝ} {r:Bid.Worth} {T': Further.StrongStartup.Tariffs} {Θ: Extra.Multi.Scope} {v:ℕ→ℕ} (h : ThroughLaunch.Perceived s O K u g k r T' Θ v)

include hG h

/-- The original floors, salaries, register, scouts, protection, later
delays and physical outputs, with the guarded bill discharged on their factor. -/
theorem company {pred : Prediction G}
    (paid : Prepaid (@Guard G (@pred)) s (ThroughLaunch.raging s K)) {τ : ℝ} (ht' : 0 < τ) : ∃ (j : ℕ→ℕ) (C : Programs s) (z : Return.Wages) (R:Targets s (ThroughLaunch.raging s K)) (E : Expenses R) (bt : Baton G), v ≤ j ∧
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
  obtain ⟨j,C,z,R,E,bt,hj,hF,stock⟩ := FundedCompanySelection.company hG h paid ht'
  refine ⟨j,C,z,R,E,bt,hj,hF,?_⟩
  intro l hl
  obtain ⟨rolls, roll⟩ := stock l hl
  refine ⟨rolls, ?_⟩
  intro D
  obtain ⟨y, wage⟩ := roll D
  refine ⟨y, ?_⟩
  intro w hw
  obtain ⟨u,reg,rider,posts⟩ := wage w hw
  refine ⟨u,reg,rider,?_⟩
  intro quote
  obtain ⟨F,S,rates,pocket,book⟩ := posts quote
  refine ⟨F,S,rates,pocket,?_⟩
  intro exchange tariff
  obtain ⟨q,η,P,protect⟩ := book exchange tariff
  refine ⟨q,η,P,?_⟩
  intro θ₀ hθ₀
  obtain ⟨θ,hθ,stages,quarter,delay⟩ := protect θ₀ hθ₀
  refine ⟨θ,hθ,stages,quarter,?_⟩
  intro menu V
  obtain ⟨booth,issue⟩ := delay menu V
  refine ⟨booth,?_⟩
  intro aux
  obtain ⟨W,ordered,later,release⟩ := issue aux
  refine ⟨W,ordered,later,?_⟩
  intro V' hV' bar wait a ha
  obtain ⟨budget,prep,hp,B,hB,shelter,shelterτ,port,cadre,amplify,works,
    origins,offer,rank,predict⟩ := release V' hV' bar wait a ha
  refine ⟨budget,prep,hp,B,hB,shelter,shelterτ,port,cadre,amplify,works,origins,offer,rank,?_⟩
  intro hc hZ hY hm
  exact predict hc hZ hY hm ⟨hF,pocket⟩

end YM.Integration.WilsonFundedWindowCompany
end

