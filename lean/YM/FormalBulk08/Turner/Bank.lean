import YM.FormalBulk08.Turner.Scarf
import YM.FormalBulk08.Taft.Spire
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Turner
open Series Wick Jets Orb Matrix Filter Function PowerSeries
open Lattice RG Laurent Precision Stationary Reef Flat Bank Mesa Lava City Wine Aster Dove Elm Quire Lotus Kemp Pose Roof Next.Free Bloch Source Source.Drops Labels
open scoped Topology ENNReal BigOperators ContDiff Classical
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{c f:Side}{i j:ℕ}
variable (A:Levels G) (u:∀ i,(A.clock.op i 0).patch.Branches K G) (R S:∀ i,Lodge ((A.clock.op i 0).patch)) (a:hue G)(hs:G.Simple)(h:LocalRatio ρ)
include hs h
lemma survey (N i:ℕ)(hp:i≤N): Dove.model A R u ρ a N i=Dove.model A S u ρ a N i := by
    induction hp using Nat.decreasingInduction with
    | self=> rw [Dove.leaves,Dove.leaves]
    | of_succ i hp ih=>
       rw [through _ _ _ _ _ _ _ hp, through A S _ _ _ N i hp]; rw [←ih]; unfold taxi; rw [paths_out (destination A N i) _ ((genu A R u ρ a h hs hp).toStory) (u i) h (A.clock.adm _) (R i) (S i)]
variable {X:Type}{W:Lab G K X}{o:Loc G 1}{k d D r:ℕ}{B: Frame G d}{H:Hol G}{T:SectionData B}(p:Quota B H W o D k r)(ht:T.Sound H)(hr: Bid.pop T)
omit hs h
include a h hs p ht hr
lemma walking (x:X)(R:∀ i,Lodge (((W.V x).clock.op i 0).patch))(N i:ℕ)(hp:W.neck x ≤ i)(hx:i≤N): Elm.bornY ρ W a B T p.horizon x N i= Elm.terrace ρ (W.V x) R (W.toEmpire.bill x) a B T p.horizon N i := by
   induction hx using Nat.decreasingInduction with
   | self=> rw [went_top a p,terrace_zero]
   | of_succ i hv ih=>
       rw [born_walk a p _ _ _ hv, thickets _ _ _ _ _ _ _ _ _ _ hv]; rw [← ih (hp.trans (Nat.le_succ _)), ←survey _ (W.toEmpire.bill x) (W.wood x) R a hs h N (i+1) hv]; exact (release_larch (destination (W.V x) N i) _ (genu (W.V x) (W.wood x) _ _ a h hs hv|>.toStory) (W.toEmpire.bill _ _) h ((W.V x).clock.adm _) (W.wood x i) (R i) _ a (birth a h p hs ht hr x _ N (hp.trans (Nat.le_succ _)) hv)).2
end YM.FormalBulk08.Turner
