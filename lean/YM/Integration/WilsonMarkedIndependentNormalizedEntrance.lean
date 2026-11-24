import YM.Integration.WilsonMarkedIndependentNormalizedElection
import YM.Integration.WilsonConditionalTaylorSeparatedPurchase

/-! Ultraviolet moving births in the separated interval. The actual original
sections undergo their prescribed reporting-coordinate change before the
ultraviolet cutoff. Its rent is uniform over all later cutoffs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedEntrance
open Function Filter Lattice RG RG.Supply Wilson Precision Next.Foundations PowerSeries
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open WilsonLimitConstruction
open scoped Classical BigOperators Topology
open WilsonMarkedIndependentNormalizedElection (deck normalized)
variable {G:Gauge}{a e:ℕ}

def Rent (Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(y:ℕ→ℝ)(e m:ℕ)
    (C:Credit)(X:Herit Q)(A:Fin (a+1)→ℝ):Prop:=
  Shipment L.S m Q (fun i=>C.buy (y m)*A i) e (normalized L O Q X m)

theorem purchase (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ):
    let Q:=deck (G:=G) l d h
    let L:=R.family.path.levels
    ∃C:Credit,∀X:Herit Q,∃A:Fin (a+1)→ℝ,∀ᶠ m:ℕ in atTop,Rent Q L R.metals.O (zz L) e m C X A:=by
  intro Q L
  obtain ⟨C,form⟩:=steering (hol G) Q e Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  obtain ⟨u,_,rails⟩:=rail_noun 0 (capP Q) e (Nat.zero_le _) 0
  refine ⟨C,?_⟩
  intro X
  obtain ⟨A,stock⟩:=shipments_one X e
  refine ⟨A,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded (by decide:0<1)
    rails l d h le_rfl] with m purchased
  obtain ⟨W,Y,level,ratio,clock,date,_,_,_,frames,_⟩:=purchased
  have val:Rent Q Y.L.V.draws Y.L.V.paid Y.L.V.y e m C X A :=
    form Y.L.V frames m date.le A (fun _=>X) (stock _ _)
  rwa [level,ratio,clock] at val

/-- The full mixed component of the independently normalized microscopic
stocks. All mark locations and angular ranks survive the first-join estimate. -/
def Separated {e:ℕ}(F:Fin (a+1)→SealR G)(Q:Realm G (e+1) Credit.leanC)(m:ℕ)(A:Fin (a+1)→ℝ)
    (X:Herit F)(t:Q.anchor ≤ m):Prop:=
  ∀N:ℕ,m ≤ N → ∀z ρ:ℝ,Q.y m ≤ z →
    hgate (hol G) F Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e z ≤ ρ →
    ∀b:ℕ,∀lo:m ≤ b,b ≤ N → ∀Y:Fin (a+1) → Cover,∀S:Finset (Fin (a+1)),1<S.card →
    cleared Q.draws.S m b ρ Y S → ∀i≤e,∀r:ℕ,
      Wig Bank.terrain Y (Q.mint b (t.trans lo)).σ
        ((∏ v∈S,(1+A v))*Real.exp (-penaltyB Credit.leanC z ρ (snowP Q.draws.S m b))) S
        ((Gears Q.draws Q.paid (fun v=>(F v).h) (fun v=>(F v).h) N N b
          (coatA Q.draws Q.paid N m F (normalized Q.draws Q.paid F X m N)) Y S).2 i r)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ):
    let F:=deck (G:=G) l d h
    let L:=R.family.path.levels
    ∃C:Credit,∀X:Herit F,∃A:Fin (a+1)→ℝ,∀ᶠ m:ℕ in atTop,
      ∃(Q:Realm G (e+1) Credit.leanC)(t:Q.anchor ≤ m),
      Q.draws=L ∧ Q.paid=R.metals.O ∧ Q.y=zz L ∧ Q.anchor=m ∧
      (∀j,m ≤ j → ∀hj:Q.anchor ≤ j,∃z:5 ≤ L.clock.J (j+1),
        (Q.mint j hj).σ=crestM L j z ∧
        v (L.clock.J (j+1)) (Q.mint j hj).gear ≤ Q.cash Credit.leanC j) ∧
      Separated F Q m (fun i=>C.buy (zz L m)*A i) X t:=by
  intro F L
  obtain ⟨C,ticket⟩:=purchase R simple v funded l d h e
  refine ⟨C,?_⟩
  intro X
  obtain ⟨A,active⟩:=ticket X
  refine ⟨A,?_⟩
  filter_upwards [active,FundedMarkedCoverRows.realm R simple v funded (a+1) l d h e 0 0] with m rent official
  obtain ⟨Q,level,ratio,clock,date,cl,_,⟨tribe⟩,crest⟩:=official
  have t:Q.anchor ≤ m:=date.le
  refine ⟨Q,t,level,ratio,clock,date,crest,?_⟩
  have old:Rent F Q.draws Q.paid Q.y e m C X A:=by rwa [level,ratio,clock]
  intro N top z ρ warm large b mb bn Y S mixed clear i ei r
  have cap:=old N N m le_rfl top top
  let salary:=fun i=>C.buy (Q.y m)*A i
  have input(v:Fin (a+1)):sprouted (F v) (normalized Q.draws Q.paid F X m N v) e
      ((1+salary v)*Credit.leanC.buy z):=by
    intro j je f
    have row:‖coeff j (normalized Q.draws Q.paid F X m N v f)‖ ≤ salary v:=(cap.track v j je f).main
    have one:1 ≤ Credit.leanC.buy z:=by simpa only [Credit.lean_cost] using (Q.depth m t).trans warm
    exact row.trans ((by linarith:salary v ≤ 1+salary v).trans
      (le_mul_of_one_le_right (by dsimp only [salary]; linarith [cap.stock v]:0≤1+salary v) one))
  have out:=ScaleS.crossing (normalized Q.draws Q.paid F X m N) (fun v=>1+salary v)
    tribe Credit.leanC (fun i=>by linarith [cap.stock i]) t top warm large input
    cl Y S mixed mb bn clear ei r
  simpa only [salary,clock] using out

end YM.Integration.WilsonMarkedIndependentNormalizedEntrance
end
