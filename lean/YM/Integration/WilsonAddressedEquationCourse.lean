import YM.Integration.WilsonAddressedEquationShelf
import YM.FullVolume.Cross
import YM.FullVolume.Hearth

/-! The elected Wilson run itself supplies the delayed Haar-equation templates.
Keep the exact outgoing label, full cutoff density and compensated transfer
from that election for all subsequent physical and independent comparisons. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedEquationCourse
open MergeProof WilsonAddressedEquationShelf
open Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D)(hF:Fridge C u ζ){f:Extraction.Order} {N p d:ℕ} (V:∀ d:ℕ,SectionData (C.labels.level d))(R:Mark.Weave G)(hV:∀ d, Mark.Portfolio C.params (V d) (R d))(hG:G.Simple)
set_option quotPrecheck false
include h hV H hG hF B
private theorem project (hb:∀ d:ℕ,∃ a: ℕ→ℝ,Braze (C:=C) (V d) a): ∃ P b, Hearthside C V R P b ζ ∧ ∀ d, ∃ E U,
    Hearth (C:=C) (V d) ζ E (fun i j => P d (i,j)) U ∧
    ∀ᶠ N:ℕ in atTop, ∀ p j, Issued C (V d) N p W u ψ ζ D j (E N) (U N p j) := by
    choose P hp using hb; choose E Y U hY paid using fun d=> elected H B h hF (V d) (hV d).valid hG (hp d)
    choose M hm hM using fun d:ℕ=> Mark.potage (C.labels.level d); choose F hK hQ hs using fun d:ℕ=> fun i:Cutoffs => hM d (catalog C R d i.1 i.2 (Y d i.1 i.2)); let b:Presentation C:=⟨F,fun d i=> (hK d i).stable⟩
    refine ⟨fun d i=> Y d i.1 i.2,b,⟨⟨fun f=> ?_,fun d=>?_,fun d N p=>hK d (N,p), fun f d=>?_⟩,fun d=> ⟨E d,U d,hY d⟩,fun d=> ⟨_,hQ d⟩⟩,fun d=>⟨E d,U d,hY d,paid d⟩⟩
    · exact ⟨fun d p=>⟨_,(hm d).le,Eventually.of_forall fun j=> hQ d (f.mesh j,p)⟩, fun d=>⟨_,(hm d).le, Eventually.of_forall fun p=> Eventually.of_forall fun j=> hQ d (f.mesh j,f.per p)⟩⟩
    · filter_upwards [catalog_symm H (V d) R (hV d) _ (hY d)] with i hi p; obtain ⟨hv,hh⟩:=hi p; refine ⟨hv,hh,hs d (i,p) ?_⟩; let L:= bindP C R d i p (Y d i p); constructor
      · intro s x h; obtain ⟨w,hw,hW⟩:=h; subst x; exact ⟨_,Mark.turn_ideal s hw,hh w s⟩
      intro x hx; obtain ⟨w,hw,hW⟩:=hx; subst x; exact ⟨_,Mark.conjugate_ideal hw,hv w⟩
    refine ⟨fun x hx hv=> marshal H B (V d) R (hV _) _ (hY d) _ hv (fun j=> ((hK d j).ker) ▸ (show x j∈LinearMap.ker (F d j).toLinearMap from LinearMap.mem_ker.mpr (hx j))),fun w hw x=> thyme H B h hG hF x d hw,fun x a=> lofty H B h hG hF x a⟩

section
open PhysicalNext.Repeat.Legato Next.Scheduling FullVolume Push.PriceCompiler
variable (run: Run G)
local notation "C!"=> run.family
local notation "a!"=> run.alloy.B.a
omit H B h hF hV hG in
theorem original (simple:G.Simple) :
    ∃ (V:∀ d,SectionData ((C!).labels.level d)) (W:Mark.Weave G), ∃ P b,
      (∀ d,Mark.Portfolio (C!).params (V d) (W d)) ∧ Hearthside (C!) V W P b (fly (a!)) ∧
      ∀ d, ∃ E U, Hearth (C:=C!) (V d) (fly (a!)) E (fun N p=>P d (N,p)) U ∧
        ∀ᶠ N:ℕ in atTop, ∀ p j, Issued (C!) (V d) N p run.w (far (a!)) (waybill (a!)) (fly (a!))
          run.doors j (E N) (U N p j) := by
  obtain ⟨_,_,_,_,_,_,⟨cost,L,V,W,hc,portfolio,invoice,floor⟩,_⟩ :=
    run.bought run.T run.tuning.receipts run.t run.accepts run.stories run.doors run.makes run.carries run.books
  have ties := (run.again simple).1
  have paid : ∀ d, ∃ b:ℕ→ℝ,Braze (C:=C!) (V d) b := by
    let J:=(a!).clock.J
    have hu (i d:ℕ)(he:d≤J (i+1)) := invoice d (J (i+1)) he _ ((floor _).trans (run.rolls.large (J (i+1))).need)
    have hw (i:ℕ) := hc _ _ (Push.PriceCompiler.step_paid _ i) _ (run.alloy.B.valid.pays i)
    intro d
    let b:=fun i=>cost d (J i)
    have h₀ : ∀ᶠ i:ℕ in atTop, ∃ j,i=j+1 ∧ d≤J (j+1) := by
      filter_upwards [eventually_gt_atTop (run.t d)] with i tail
      obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact ⟨j,rfl,(Nat.le_add_right d 3).trans ((run.accepts d).trans ((a!).fits.mono tail.le))⟩
    refine ⟨b,⟨?_,?_,?_⟩⟩
    · filter_upwards [h₀] with i hi
      obtain ⟨j,rfl,he⟩:= hi
      change Bid.Credit _ ((a!).params (j+1)).order ((a!).params (j+1)).power _
      rw [params_eq run.alloy.B.valid]
      exact (hu j d he).2.1
    · filter_upwards [h₀] with i hi
      obtain ⟨j,rfl,he⟩:= hi
      exact ⟨(hu j d he).2.2.1,(hw (j+1)).2 d he|>.1⟩
    · filter_upwards [h₀] with i hi
      obtain ⟨j,rfl,he⟩:= hi
      change 2*(1+((a!).params _).columns)*sphere ((a!).params _) ((V d).stencil∪(localSection G d).stencil).card (b _) ≤
        Bid.puffs ((a!).S.block _)*sliver ((Labels.frames G).level d)
      rw [params_eq run.alloy.B.valid,show j+1-1=j from rfl,Extra.Iteration.block_eq run.alloy.B.valid]
      exact (hu j d he).1
  obtain ⟨P,b,hearth,rows⟩ := project run.makes ties.tabs ties.scrim ties.fridge V W portfolio simple paid
  exact ⟨V,W,P,b,portfolio,hearth,rows⟩
end
end YM.Integration.WilsonAddressedEquationCourse
