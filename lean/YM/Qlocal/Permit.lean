import YM.Extension.UV.Canon.Expound

/-!
Stagewise *offer* from the client. Parameterises the construction in
`Passenger` so that we can pay once for all comparisons on the moving tail.
Nothing about convergence or norms assumed here, only bookkeeping for
combining (proved) stage leases without rechoosing Run. Can conjoin.
Scope: pre-L after targets, extra post-L Entrance delays (can include volumes) on
 every purchased Register and passes. Later will also have arbitrary Wait and
wages available before running the campaign.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Schedule
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo

open PhysicalNext PhysicalNext.Repeat
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Roost Cub Circlet Graces
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
-- store cap as `∀M D...`; explicit to survive notation
abbrev Goal (G:Gauge):= ∀ (M:Metals G) (D:Rolls M.p) (A:Alloy M D), Factor A →Prop
variable (H : Goal G)
section after
-- invoice at time of purchasing Delays. Requires NO p before L except settler C z t
variable (s:Sheet G) (T:MapPrices)(C:Programs s) (l:ℕ→ℕ)
     {R:Targets s (ThroughLaunch.bearing s T)} (z:Return.Wages)(E:Expenses R)
     (D:Rolls (ThroughLaunch.raise s l)) (w:Return.Wages) (u:ℕ→ℝ) (Z:PhysicalNext.Repeat.Register D E w u) (F:ℕ→ℕ→Postage)(S:Time.Scouts (F:=F))
     (p₁:ℕ→ℕ→JointLoad.Heir.Record) {P:Protection D}(V:Delays P)
local notation "M" =>ThroughLaunch.currency s T l
-- regression must check eq casts.
def Welcomed (Q:ℕ→ℕ→JointLoad.Clockwork.Menu): Prop:= ∀ (C0:PostCost D) (K0:Bar V)(I : Wait K0) (hp:Stock.Priced V) (B0: Directed G I (chart G) (ThroughLaunch.bearing s T) C0),
  Extension.UV.Archive B0 → (∃ f,RankCovariance.ShapePort B0.a B0.M f) →
  let A : Alloy M D:= Alloy.mk C0 P V K0 I hp B0
  ∀ E' η q B bt b J hf hF hW ha,H M D A ⟨E',F,S,η,q,w,B,R,E,u,Z,bt,z,rays s,mile,b,C,Q,p₁,J,hf,hF,hW,ha⟩

end after

def Obtainable : Prop:=
  ∀ (s:Sheet G) (T:MapPrices)(C:Programs s)(z:Return.Wages) (R:Targets s (ThroughLaunch.bearing s T)) (E:Expenses R),
    (∀ i k,(R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0) →
    ∃ f:ℕ→ℕ,∀ l:ℕ→ℕ,f ≤ l →∀ (D:Rolls (ThroughLaunch.raise s l)) (w:Return.Wages) (u:ℕ→ℝ) (Z:PhysicalNext.Repeat.Register D E w u) (F:ℕ→ℕ→Postage)(S:Time.Scouts (F:=F)), Pocket Z S →
       ∀ (p₁:ℕ→ℕ→JointLoad.Heir.Record), (∀ j i,StepStages j i → s.first ≤ i → (p₁ j i).ε ≤ 1 / 4) →
       ∀ (P:Protection D)(Q:ℕ→ℕ→JointLoad.Clockwork.Menu)(V:Delays P), ∃ W:Delays P,DelayLe V W ∧ ∀ Y, DelayLe W Y → Welcomed H s T C l z E D w u Z F S p₁ Y Q
abbrev accompanying (L:Goal G) : Goal G:=fun M D A F=> H M D A F ∧ L M D A F
variable {H} {L:Goal G}
theorem Obtainable.also (hp:Obtainable H) (hl: Obtainable L) : Obtainable (accompanying H L):= by
 intro s T C z R E h; obtain ⟨f,hf⟩:= hp s T C z R E h; obtain ⟨g,hg⟩:= hl s T C z R E h; refine ⟨f⊔g, fun l hl D w u Z F S h p H₁ P Q V=>?_⟩; obtain ⟨y,hy,H⟩:= hf l (le_sup_left.trans hl) D w u Z F S h p H₁ P Q V; obtain ⟨x,hx,hv⟩:= hg l (le_sup_right.trans hl) D w u Z F S h p H₁ P Q y; exact ⟨x,hy.trans hx, fun W hW K0 T I p b hA hv0 t u a v w l i he hv' hL hp=>⟨ H W (hx.trans hW) K0 T I p b hA hv0 t u a v w l i he hv' hL hp,hv W hW K0 T I p b hA hv0 t u a v w l i he hv' hL hp⟩⟩ -- let binder A not explicit Lean in lambda? maybe yes
end YM.Qlocal.Schedule
