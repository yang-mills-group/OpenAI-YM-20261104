import YM.QuadraticLocal.Rebirth.Team
import YM.Integration.WilsonOriginalBornLedger

/-! Restamp the received analytic bank in the outgoing coupling on the very same
signed born density, with the discrepancy paid once on its original incoming. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalBornRestamp
open Function Filter Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn
open Comparison.RG02 Comparison.RG02.Adjacent Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling Next.Foundations PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Sunrise
open QuadraticLocal.Rebirth.Chart
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V I J:Type} [DecidableEq V] [Fintype V] [Countable J]
  (P:Passport n V) (W:Rep G n) (R:Census V)
  {F:V → Type} [∀ v,AddCommGroup (F v)] [∀ v,Module ℝ (F v)]
  (A:∀v,Set (F v)) (K:∀v,Submodule ℝ (F v))
  (born:Lamps (Wallet A) I G W.p P.origin R) (X:J → Row P R G (Wallet A))
  (Q:Pace.Coin) (h:Q 0=0) (L j:ℕ) (g d : ℝ) (w u:V → ℝ) (t:V → ℕ)
  {k v:ℕ} {a c σ ν z x τ regular hard:ℝ}
  (H:Recharged Q h g d L j v a ν z) (stock:Scene.Armada X w t x c j k v)

local notation "width" => (W.p.supportExponent+1+1)
local notation "f₀" => rendered X W.p g
local notation "stamp" => Mutation.stamp X Q h L j
local notation "f₁" => rendered (stamp) W.p d
local notation "fee" => Invoice.price W.p σ (j+v+1) k (width) τ G

include H stock in
theorem measured (upperFee:Invoice.Supports W.p σ (width) g x τ) (atDate:Invoice.Supports W.p σ (width) d x τ)
    (rate:0 ≤ ν) (table:Tableau K A X) {freshFee:ℝ} (active:born.Paid w W.p.B (width) freshFee)
    (Y:Wallet A → Config G n → Poly R)
    (admitted:WilsonOriginalBornLedger.priced W P R A K born (f₀) w u regular hard Y) :
    WilsonOriginalBornLedger.priced W P R A K born (f₁) w u (ν*(fee)*c+regular) hard Y ∧
    Tableau K A (stamp) := by
  obtain ⟨C,counted,next,rent,forced,hits,crown,physical,quiet⟩:=admitted
  letI : Countable C:=counted
  let fixed:=Mutation.grow X Q h L j g d W next
  have room:0 ≤ (width):=by linarith [W.p.exponent_pos]
  have stamped:=Mutation.fidelity Q h L j A K X table
  have funds:=Mutation.leases X Q h L j g d w t H stock rate W next upperFee atDate rent
  have prior:=Lamps.joinPaid (Scene.Armada.paid X w t stock W.p upperFee) rent
  have seated:=Mutation.pencil Q h L j g d W F A K X next table hits crown
  have same (t₀:Wallet A) (U:Config G n) :
      (born.join ((f₀).join next.old)).log t₀ U=(born.join ((f₁).join fixed.old)).log t₀ U := by
    have before:=Lamps.joinLog t₀ U (active.sums room stock.positive t₀ U) (prior.sums room stock.positive t₀ U)
    have after:=Lamps.joinLog t₀ U (active.sums room stock.positive t₀ U) (funds.2.sums room stock.positive t₀ U)
    exact before.trans ((congrArg (fun e=>born.log t₀ U+e)
      (Mutation.syllable X Q h L j g d w t H stock rate room W next upperFee atDate rent t₀ U)).trans after.symm)
  have field (t₀:Wallet A) (U:Config G n) :
      (⟨born.join ((f₀).join next.old),next.hard⟩:Gallery (Wallet A) _ P.origin W R).density t₀ U=
      (⟨born.join ((f₁).join fixed.old),fixed.hard⟩:Gallery (Wallet A) _ P.origin W R).density t₀ U := by
    unfold Gallery.density
    change _ • (Poly.pass ((born.join ((f₀).join next.old)).log t₀ U)*_) =
      _ • (Poly.pass ((born.join ((f₁).join fixed.old)).log t₀ U)*_)
    rw [same t₀ U]
    rfl
  refine ⟨⟨_,inferInstance,fixed,funds.1,forced,seated.2,crown,?_,?_⟩,stamped⟩
  · exact fun t₀ U=>(field t₀ U).symm.trans (physical t₀ U)
  · exact fun t₀ U=>(congrArg (fun e:Poly R=>e.part R.quiet) (field t₀ U).symm).trans (quiet t₀ U)

end YM.Integration.WilsonOriginalBornRestamp
