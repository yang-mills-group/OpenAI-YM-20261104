import YM.OPE.Compatible.Eyrie.Return
import YM.MergeProof.Noel
import YM.MergeProof.Emanate

/-!
# Strong mixed-source bin and `Base`/`Seed` on a *common* production

Extra floor, then after-block delays, then window requirements BEFORE extracting the B and
its histories. No additional choice of cutoff law after that; the physical tables and primary
cylinders are exactly those of the Family in the same grant, although we run the bin
selection on that Family with strong witnesses. This doesn't show full-cutoff convergence!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
variable {G:Gauge}{M:Metals G}{P:Rolls M.p}{A:Alloy M P} (Y:Bolt A)(t:ℕ→ℕ)
    (Xf:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p)
    (hx:∀ d,d+3 ≤ A.B.a.clock.J (t d)){cost:ℕ→ℕ→ℝ}{d':ℕ→ℕ}{T:∀ d:ℕ,SectionData ((Labels.frames G).level d)}
    (hc:dusk A.delay cost)(hN:paper M.p cost T d') (hF: d' ≤ M.p.floorL)
set_option quotPrecheck false
local notation "F'" => Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t Xf
include t Xf hx hc hN hF
lemma new_duty :
    (∀ d:ℕ, ∃ a:ℕ→ℝ,Braze (C:=F') (T d) a) ∧ ∀ i,Push.RelayDifference.jump (A.B.a.budget i)≤ A.B.a.clock.hatBeta i:= by
    let S:= A.B.a; let J:=S.clock.J
    have hW(i:ℕ)(d:ℕ)(he:t d ≤ i):d+3  ≤  J i:= (hx d).trans (A.B.a.fits.mono he)
    have hu (i:ℕ)(d:ℕ)(he:d  ≤  J (i+1)):= hN d (J (i+1)) he _ ((hF _).trans (P.large (J (i+1))).need)
    have hw(i):= hc _ _ (step_paid _ i) _ (A.B.valid.pays i)
    constructor
    · intro d; let b:= fun i=> cost d (J i)
      have h₀ : ∀ᶠ i:ℕ in atTop, ∃ j,i=j+1∧ d ≤ J (j+1) := by
         filter_upwards [eventually_gt_atTop (t d)] with i hi; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0); exact ⟨j,rfl,(Nat.le_add_right d 3).trans (hW (j+1) d hi.le)⟩
      refine ⟨b,⟨?_, ?_,?_⟩⟩
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; change Bid.Credit _ (A.B.a.params (j+1)|>.order) (A.B.a.params (j+1)|>.power) _; rw [params_eq A.B.valid]; exact (hu j d h).2.1
      · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; exact ⟨(hu j d h).2.2.1,(hw (j+1)).2 d h|>.1⟩
      filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi
      change 2*(1+(A.B.a|>.params _|>.columns))*sphere (A.B.a|>.params _) ((T _).stencil∪(localSection G _).stencil).card (b _) ≤ Bid.puffs (A.B.a.S.block _)*sliver (Labels.frames G|>.level d)
      rw [params_eq A.B.valid,show j+1-1=j from rfl,Extra.Iteration.block_eq A.B.valid]; exact (hu j d h).1
    intro i; change step_cost (A.B.a.params i) ≤ A.B.a.clock.hatBeta i; rw [params_eq A.B.valid]; exact (hw i).1
end YM.PhysicalNext.Repeat.Legato
