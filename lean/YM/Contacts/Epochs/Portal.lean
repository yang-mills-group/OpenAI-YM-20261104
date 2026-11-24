import YM.MergeProof.North.Expound

/-! # Arbitrary-law scheduling with post-programming access.
 Quantifiers deliberately mirror Trading & Ruese. Supports compound asks on a proof‐relevant Factor,
 allowing time-purchases and Mark/Phase registers fixed without choosing exploration flows;
 `prep` is *method of charging*, not presumed finally. -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
structure EpochSeal (s:Sheet G)(O:MapPrices)(R:Targets s O)(E:Expenses R) :Prop where
    hForm i k : (R i k).table=chart G ∧ (R i k).halo=500 ∧ (E i k).earn=Roof.rays s i k ∧ (E i k).wanting=-(7/16:ℝ) ∧ (E i k).degrees=0
abbrev Decision (G:Gauge): Type := ⦃M : Metals G⦄ → ⦃D:Rolls M.p⦄→ ⦃A: Alloy M D⦄→ Factor A→Prop
-- Granted pre-calendar witness.E: expression accepts law established at any T.Calendar.Level, reusable after mark. Tracks P.Weights widths. No Mark oracle in final.
abbrev Chassis (Ψ:Decision G) {s:Sheet G}{K:MapPrices}{R:Targets s (ThroughLaunch.bearing s K)}{E:Expenses R}
     (z:Return.Wages)(C: Programs s)(bt: Baton G)(u:ℕ→ℕ){D:Rolls (ThroughLaunch.raise s u)}
     {w:Return.Wages} {X:ℕ→ℝ} (R': Register D E w X) (B:ℕ→ℕ→Cafe) {F:ℕ→ℕ→Postage} (S:Time.Scouts (F:=F)) (E₀:ℕ→ℕ→Exchange)
     (q:UVNext.CouplingReset.ResetPrices) (η:ℕ→ℝ) (P : PostCost D)
     {θ:Protection D} (p:ℕ→ℕ→JointLoad.Heir.Record)(Q:ℕ→ℕ→JointLoad.Clockwork.Menu)(b:ℕ→ℕ→Booth)(J:ℕ→ℕ→JointLoad.Folio.Aux) (W: Delays θ) : Prop := ∀ V:Delays θ,DelayLe W V→ ∀ (Z:Bar V) (I: Wait Z) (h : Stock.Priced V)(B' : Directed G I (chart G) (ThroughLaunch.bearing s K) P), let Y: Alloy (ThroughLaunch.currency s K u) D:= ⟨P,θ,V,Z,I,h,B'⟩; ∀ hf : Sheltered (C:=C) (B:=B) Y bt z (rays s) mile b Q p J R' S (1/16) (1/16) (1/8) E₀ q η,
          ∀ hQ:(∀ i j,(R i j).table=chart G), ∀ hV:WorksIn (D:=D) (X:=ThroughLaunch.currency s K u) R' P V S, ∀ hS:AsDivisors B'.a.S, Ψ (⟨E₀,F,S,η,q,w,B,R,E,X,R',bt,z,rays s,mile,b,C,Q,p,J,hf,hQ,hV,hS⟩ : Factor Y)

def EpochPlan (s:Sheet G)(K:MapPrices)(R:Targets s (ThroughLaunch.bearing s K))(E:Expenses R) (z:Return.Wages)(C:Programs s)(bt:Baton G) (Ψ:Decision G) (l:ℕ→ℕ): Prop:= ∀ u: ℕ→ℕ,l≤u → ∀ (D: Rolls (ThroughLaunch.raise s u)) (w:Return.Wages) (X:ℕ→ℝ)(R': Register D E w X) (B:ℕ→ℕ→ Cafe) (F:ℕ→ℕ→Postage)(S:Time.Scouts (F:=F)) (E₀:ℕ→ℕ→Exchange) (q:UVNext.CouplingReset.ResetPrices)(η:ℕ→ℝ)(P:PostCost D)(θ:Protection D) (p:ℕ→ℕ→JointLoad.Heir.Record), (∀ j i,StepStages j i→s.first≤ i→(p j i).ε≤1/4)→∀ (Q : ℕ→ℕ→ JointLoad.Clockwork.Menu)(b:ℕ→ℕ→Booth)(J:ℕ→ℕ→JointLoad.Folio.Aux)(V₀:Delays θ),∃ W : Delays θ, DelayLe V₀ W ∧ Chassis (G:=G) Ψ z C bt u R' B S E₀ q η P p Q b J W
structure Overlay (G:Gauge) where
    mark : Decision G
    passage : ∀ (s: Sheet G) (K:MapPrices)(R:Targets s (ThroughLaunch.bearing s K))(E:Expenses R)(z:Return.Wages)(C: Programs s)(bt:Baton G), G.Simple → EpochSeal s _ R E → ∃ l: ℕ→ℕ, EpochPlan s K R E z C bt mark l
-- composition charges before + successively later
namespace Overlay
def cross (O Y: Overlay G): Overlay G where
    mark _ _ _ X:= O.mark X ∧ Y.mark X -- implicit args?
    passage s K R E z C bt hg hh:= by
      obtain ⟨l,hV⟩:= O.passage s K R E z C bt hg hh; obtain ⟨w,hh⟩:=Y.passage s K R E z C bt hg hh; refine ⟨l⊔w,fun v hv D wX μ Z B F S q a e P θ p hp K₁ b W T=>?_⟩
      obtain ⟨V,h,hV⟩:=hV v (le_sup_left.trans hv) D wX μ Z B F S q a e P θ p hp K₁ b W T; obtain ⟨I,hi,he⟩:=hh v (le_sup_right.trans hv) D wX μ Z B F S q a e P θ p hp K₁ b W V; exact ⟨I,h.trans hi,fun Y hy c d z χ h ht hM h₁=> ⟨hV Y (hi.trans hy) c d z χ h ht hM h₁,he Y hy c d z χ h ht hM h₁⟩⟩ -- Y shadow, let binder proof
end Overlay
end YM.PhysicalNext.Repeat.Legato
