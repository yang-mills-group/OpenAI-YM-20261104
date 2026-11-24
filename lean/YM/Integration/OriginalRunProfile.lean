import YM.FullVolume.Cross

/-!
The original Forge/Cross construction with its existing stage-profile receipt
retained. This strengthens the existential construction; it does not assert a
new property of an arbitrary Run or replace a previously selected Run.

The purchases, full campaign, fields, extraction endpoints, and scalar
normalization are exactly those of the original construction below. The only
new returned datum is WithStage, already supplied by the original trident call.
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
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

namespace OriginalRunConstruction

/-- The exact orders already chosen by the original `dagger` proof. -/
def originalOrders : Orders := ⟨4, fun i => 6+i, fun i => 2+i, fun i => 100+i⟩

/-- Retain the original pre-L order/power/support receipt through every
purchase in `dagger`. All the original unlatched endpoint data remain. -/
theorem dagger_with_profile (hG : G.Simple) {β : ℝ} (h : 0 < β) :
    ∃ (M : Metals G) (P : Rolls M.p) (A : Alloy M P) (X : Factor A)
      (Y : ℕ → ℝ) (K : Bid.Worth) (b : Bandage X Y K),
      A.B.a.clock.kernel.penalty = β ∧
      Unlatched b (fun _ => 1) (fun T t S _ =>
        let Z := Family.mk (Issue.trail T) (hol G) (Labels.frames G)
          (localSection G) t S
        ∀ f : Extraction.Order, MergeProof.East.CompleteWeak Z f) ∧
      WithStage M.p originalOrders := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v : Orders := originalOrders
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,hStage,l,hL,hK⟩:= trident hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  refine ⟨_,_,_,_,_,_,c,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hU,?_⟩
  exact ⟨hStage.first,hStage.jets,hStage.powers,hStage.prices⟩

/-- Construct the very same campaign and family while retaining its profile.
There is a single rod/squad selection, followed by a single returned Run. -/
theorem ramp_with_profile (hG : G.Simple) (b : ℝ) (hp : 0 < b) :
    ∃ R : Run G, R.family.path.levels.clock.kernel.penalty = b ∧
      WithStage R.metals.p originalOrders := by
  obtain ⟨M,P,A,X,Y,K,bC,hK,hAhead,hProfile⟩ := dagger_with_profile hG hp
  obtain ⟨T,⟨Z⟩⟩ := FullVolume.rod hG X
  choose t ht using fun d : ℕ => (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
  obtain ⟨D,S,hm,hc,hH,hF⟩ := squad hG bC T Z.receipts t ht
  exact ⟨⟨M,P,A,X,Y,K,bC,_,hAhead,T,Z,t,ht,D,S,hm,hH,hF⟩,hK,hProfile⟩

/-- The exact receipt discharges the finite field/distance-order inlet. -/
theorem profile_orders (R : Run G) (h : WithStage R.metals.p originalOrders) :
    ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power := by
  intro j
  rw [h.jets, h.powers]
  change j ≤ 6+j ∧ j ≤ 2+j
  omega

/-- The support exponent was also fixed by the same original pre-L profile. -/
theorem profile_support (R : Run G) (h : WithStage R.metals.p originalOrders) :
    ∀ j, 100 ≤ (R.metals.p.profile j).supportExponent := by
  intro j
  rw [h.prices]
  change (100 : ℝ) ≤ 100+j
  exact le_add_of_nonneg_right (Nat.cast_nonneg j)

/-- Transport that support receipt to the actual budget of this same Run. -/
theorem budget_support (R : Run G) (h : WithStage R.metals.p originalOrders) :
    ∀ m, 100 ≤ (R.alloy.B.a.budget m).supportExponent := by
  intro m
  change 100 ≤ (R.alloy.B.a.clock.stage (R.alloy.B.a.clock.J m)).supportExponent
  rw [R.alloy.B.valid.stage]
  exact profile_support R h _

open FullVolume

/-- Every endpoint of the original `realized` theorem, for one original Run,
with the construction's order/power/support receipt still available. -/
theorem realized_with_profile (hG : G.Simple) (w : ℝ) (hw : 0 < w) :
    ∃ R : Run G, R.family.path.levels.clock.kernel.penalty = w ∧
      WithStage R.metals.p originalOrders ∧ R.Ties ∧
      (∀ f : Extraction.Order, ∃ (g : Extraction.Order) (S : Table R.family.book),
        Nonempty (Spec.Final R.family (f.refine g) S)) ∧
      (∀ b ∈ nearby R.alloy.B.a, ∀ N p : ℕ, let U := R.tuning.arc p N
        ∃ β ∈ Icc U.left U.right,
          Competes (still R.kit) p N 0 (U.replay β) ∧
          (U.replay β 0).beta = b ∧ (U.replay β N).beta = β) ∧
      (∀ N p : ℕ, let U := R.tuning.arc p N
        R.family.path.rep N p = U.replay (R.tuning.beta p N)) ∧
      ∀ m p : ℕ,
        (∃ c : ℝ, 0 < c ∧ ∀ N ≥ m, c ≤ stripped R.family.path N p m) ∧
        Tendsto (fun N => (R.family.path.rep N p m).v) atTop atBot := by
  obtain ⟨R,hW,hProfile⟩ := ramp_with_profile hG w hw
  obtain ⟨H,hFinal⟩ := Run.again R hG
  refine ⟨R,hW,hProfile,H,hFinal,fun b hb N p => ?_,
    fun N p => (R.tuning.central p N).symm,fun m p => ⟨?_,?_⟩⟩
  · intro U
    obtain ⟨β,hv,ht⟩ := U.covers hb
    exact ⟨β,hv,U.trials β hv,ht,U.top β hv⟩
  · exact FullVolume.saved (A := R.family.path) R.makes.wilson m p
  · exact FullVolume.field_independent R.makes.wilson hG m p

end OriginalRunConstruction
end YM.PhysicalNext.Repeat.Legato
