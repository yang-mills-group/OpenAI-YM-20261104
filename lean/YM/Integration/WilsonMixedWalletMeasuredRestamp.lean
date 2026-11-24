import YM.Integration.WilsonOriginalBornRestamp
import YM.Integration.WilsonMixedReceivedLamp

/-! Change the coupling only of the deposited student, keeping the separately
addressed birth and the hard array actually produced by the joint second tap. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedWalletMeasuredRestamp
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Comparison.RG02 Comparison.RG02.Adjacent Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling Next.Foundations PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Rebirth QuadraticLocal.Sunrise QuadraticLocal.Rebirth.Chart
open WilsonMixedTestTableau WilsonMixedPassportRows
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V I J:Type} [DecidableEq V] [Fintype V] [Countable J]
  (P Z:Passport n V) (W:Rep G n) (R:Census V) {F F₁:V → Type}
  [∀ v,AddCommGroup (F v)] [∀ v,Module ℝ (F v)] [∀ v,AddCommGroup (F₁ v)] [∀ v,Module ℝ (F₁ v)]
  (A:∀v,Set (F v)) (B:∀v,Set (F₁ v)) (K:∀v,Submodule ℝ (F v)) (L₁:∀v,Submodule ℝ (F₁ v))
  (old:Finset V) (blank:∀v,0∈ A v)
  (born:Lamps (Wallet (actors A B)) I G W.p (passport (owner P Z old)).origin R)
  (X:J → Row P R G (Wallet A)) (Q:Pace.Coin) (h:Q 0=0) (L j:ℕ) (g d : ℝ) (w u split:V → ℝ) (t:V → ℕ)
  {k v:ℕ} {a c σ ν z x τ regular hard:ℝ}
  (H:Recharged Q h g d L j v a ν z) (stock:Scene.Armada X w t x c j k v)
local notation "joined" => passport (owner P Z old)
local notation "project" => WilsonMixedReceivedLamp.regular (P:=P) (Q:=Z) (W:=W) A B old blank
local notation "width" => (W.p.supportExponent+1+1)
local notation "f₀" => rendered X W.p g
local notation "stamp" => Mutation.stamp X Q h L j
local notation "f₁" => rendered (stamp) W.p d
local notation "refill" => Mutation.mend X W.p Q h L j g d
local notation "fee" => Invoice.price W.p σ (j+v+1) k (width) τ G

include H stock in
theorem measured (upperFee:Invoice.Supports W.p σ (width) g x τ) (atDate:Invoice.Supports W.p σ (width) d x τ)
    (rate:0 ≤ ν) (table:Tableau K A X) (hu:∀v,0<u v) (fit:∀v∈old,u v ≤ w v)
    (nativeHard:Hard (Wallet A) W.p W.activities.forced W.activities.K P.origin R) (eligible:Crown P.support A K nativeHard)
    {freshFee:ℝ} (active:born.Paid u W.p.B (width) freshFee)
    (Y:Wallet (actors A B) → Config G n → Poly R)
    (admitted:WilsonOriginalBornLedger.priced W joined R (actors A B) (pieces K L₁) born (project f₀) u split regular hard Y) :
    WilsonOriginalBornLedger.priced W joined R (actors A B) (pieces K L₁) born (project f₁) u split (ν*(fee)*c+regular) hard Y ∧
    Tableau K A (stamp) := by
  obtain ⟨C,counted,next,rent,forced,hits,crown,physical,quiet⟩:=admitted
  letI : Countable C:=counted
  have room:0 ≤ (width):=by linarith [W.p.exponent_pos]
  have stamped:=Mutation.fidelity Q h L j A K X table
  have first:=Scene.Armada.paid X w t stock W.p upperFee
  have last:=Scene.Armada.paid (stamp) w t (Mutation.allocate X Q h L j w t H stock) W.p atDate
  have change:=Mutation.wage X W.p Q h L j g d w t H stock upperFee rate
  have good:Taut P.support A K (refill):=by
    let paid:=table.line W.p g
    exact ⟨paid.house,fun i U => (paid.adv i U).cs _⟩
  have firstJoint:=WilsonMixedReceivedLamp.paid (Q:=Z) A B old blank (f₀) hu fit first
  have lastJoint:=WilsonMixedReceivedLamp.paid (Q:=Z) A B old blank (f₁) hu fit last
  have changeJoint:=WilsonMixedReceivedLamp.paid (Q:=Z) A B old blank (refill) hu fit change
  have firstRead:=WilsonMixedReceivedLamp.heard (Q:=Z) A B K L₁ old blank (f₀) nativeHard eligible
    (table.line W.p g) stock.positive room first
  have lastRead:=WilsonMixedReceivedLamp.heard (Q:=Z) A B K L₁ old blank (f₁) nativeHard eligible
    (stamped.line W.p d) stock.positive room last
  have changeRead:=WilsonMixedReceivedLamp.heard (Q:=Z) A B K L₁ old blank (refill) nativeHard eligible
    good stock.positive room change
  let fixed : Tint.Incoming joined W (Wallet (actors A B)) (_⊕C) R := ⟨(project refill).join next.old,next.hard⟩
  have added:=Lamps.joinPaid changeJoint rent
  have prior:=Lamps.joinPaid firstJoint rent
  have after:=Lamps.joinPaid lastJoint added
  have same (s:Wallet (actors A B)) (U:Config G n) :
      (born.join ((project f₀).join next.old)).log s U=(born.join ((project f₁).join fixed.old)).log s U := by
    rw [Lamps.joinLog s U (active.sums room hu s U) (prior.sums room hu s U),
      Lamps.joinLog s U (active.sums room hu s U) (after.sums room hu s U),
      Lamps.joinLog s U (firstJoint.sums room hu s U) (rent.sums room hu s U),
      Lamps.joinLog s U (lastJoint.sums room hu s U) (added.sums room hu s U)]
    rw [Lamps.joinLog s U (changeJoint.sums room hu s U) (rent.sums room hu s U),firstRead.2,lastRead.2,changeRead.2,
      Mutation.biology X W.p Q h L j g d w t H stock upperFee atDate rate room]; abel
  have field (s:Wallet (actors A B)) (U:Config G n) :
      (⟨born.join ((project f₀).join next.old),next.hard⟩:Gallery (Wallet (actors A B)) _ (joined).origin W R).density s U=
      (⟨born.join ((project f₁).join fixed.old),fixed.hard⟩:Gallery (Wallet (actors A B)) _ (joined).origin W R).density s U := by
    unfold Gallery.density
    change _ • (Poly.pass ((born.join ((project f₀).join next.old)).log s U)*_) =
      _ • (Poly.pass ((born.join ((project f₁).join fixed.old)).log s U)*_)
    rw [same s U]
    rfl
  refine ⟨⟨_,inferInstance,fixed,added,forced,Polish.Static.spawn changeRead.1 hits,crown,?_,?_⟩,stamped⟩
  · exact fun s U=>(field s U).symm.trans (physical s U)
  · exact fun s U=>(congrArg (fun e:Poly R=>e.part R.quiet) (field s U).symm).trans (quiet s U)
end YM.Integration.WilsonMixedWalletMeasuredRestamp
