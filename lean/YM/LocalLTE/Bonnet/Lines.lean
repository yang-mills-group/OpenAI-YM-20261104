import YM.LocalLTE.Bonnet.Clockers
/-! Literal EQs of extended representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable (P : Match.Alliance H I 1 0) (hz:P.units=Equiv.refl _)
variable (hp:R.path=R'.path) (he:R.activities.reg=R'.activities.reg) (hk:R.activities.forced=R'.activities.forced)
include hp he hk P hz
variable (χ)
lemma writtenN (γ:ℝ) (d ℓ:ℕ): Meadow.timbresN P (χ:=χ) γ ℓ d=Meadow.timbresN (Meadow.intern I) (χ:=χ) γ ℓ d:=by
  have h₁:= upwardN (I':=I) χ P hz hp he hk γ
  have h₂:(timbresN P (χ:=χ) γ ℓ d).logRead=(timbresN (intern I) (χ:=χ) γ ℓ d).logRead:=by
    ext1 i; rw [compassN, h₁, compassN]
    rw [flyerN P hz hp he hk]
    exact if_congr (migrateN P hz hp he hk d ℓ _|>.2) rfl rfl
  unfold Meadow.timbresN; rw [Collection.Source.mk.injEq]; exact ⟨h₂, congr_arg Collection.Source.hardRead h₁⟩
lemma abounds (d ℓ:ℕ)(γ:ℝ): Meadow.sortable I χ ℓ d γ= fun i=> if Meadow.debrisN H ℓ d i then (plusone H P χ γ).logRead i else 0:= by
  unfold Meadow.sortable; ext1 i; rw [upwardN (I':=I) _ _ hz hp he hk γ]; exact if_congr (stampedN hp he hk d ℓ i|>.symm) rfl rfl
lemma standings (d ℓ:ℕ): Meadow.panelN H ℓ d=Meadow.panelN I ℓ d:= by
  ext i; rw [petaledN,petaledN, flyerN P hz hp he hk i]; exact (migrateN P hz hp he hk d ℓ _).2
omit P hz in
lemma harbor (p':BudgetPoint) (x : Site c): Meadow.garnerAt H p' x= Meadow.garnerAt I p' x:= by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R; obtain ⟨U,C,⟨S,V,e2,k2⟩,P,B,T₁⟩:=R'; cases hp; cases he; cases hk; rfl
lemma watts (p':BudgetPoint) (d ℓ:ℕ)(γ:ℝ): Trio.earnedN p' P γ d ℓ= Trio.earnedN p' (intern I) γ d ℓ:= by
  ext i j; unfold Trio.earnedN; rw [standings P hz hp he hk,harbor hp he hk _ _, signageN hp he hk _,upwardN _ _ hz hp he hk γ (I':=I)]; rfl
end YM.PhysicalNext.Repeat.Meadow
