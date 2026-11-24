import YM.Integration.WilsonMovingForkPrintedFile
import YM.Integration.WilsonOriginalTwoFlatIRFlatLedger

/-! The deposited material fixes both the compact print and its zero-angular
ordinary polynomial. Each occupied scalar is evaluated on the material's
own earlier vacuum, with its own front and relative placement. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkDepositedPrint
open Function Filter Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums PhysicalNext.Repeat.Legato WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet
open WilsonOriginalCensusDatedMaterial (Material words)
open WilsonOlderFreshGraphSlate
open WilsonMovingForkPrintedFile (Board)
open scoped Classical BigOperators Topology

structure Sheet {G:Gauge}(R:Run G)(N i:ℕ){n:ℕ}{side:Side}(pins:Fin n → Site side) where
  index:Type
  [count:Fintype index]
  load:Fin n → ℕ
  order:ℕ
  strip:ℝ
  binder:index → Binder (Passport.point pins) (Stock.census (Fin n))
  source:Material R N i order load strip binder
  wallet:Wallet (room (Fin n))

attribute [instance] Sheet.count

variable {G:Gauge}{R:Run G}{N i n:ℕ}{side:Side}{pins:Fin n → Site side}(H:Sheet R N i pins)

def board:Board G pins where
  index:=H.index
  load:=H.load
  order:=H.order
  strip:=H.strip
  binder:=H.binder
  copies:=words H.source
  wallet:=H.wallet

def polynomial (g:ℝ):Poly (Stock.census (Fin n)):=
  ∏a:H.index,(1+Poly.send (H.binder a).mode
    ((∏v∈(H.binder a).mode.val,(H.wallet v).val)*Complex.ofReal
      (∑e:Fin (H.order+1),g^e.val*WilsonOriginalTwoFlatIRFlatLedger.occupied H.source a e)))

theorem flat (g:ℝ):
    WilsonOriginalTwoFlatIRMounted.value (board H).binder (board H).load (board H).copies g
      (board H).wallet (1:Config G side)=polynomial H g:=by
  unfold board WilsonOriginalTwoFlatIRMounted.value polynomial
  apply Finset.prod_congr rfl
  intro a _
  exact congrArg (fun v:ℂ=>1+Poly.send (H.binder a).mode ((∏i∈(H.binder a).mode.val,(H.wallet i).val)*v))
    (WilsonOriginalTwoFlatIRFlatLedger.original H.source a g)

theorem rooted:
    (∑a:(board H).index,Real.exp ((board H).strip*((board H).binder a).length)*
      WilsonIndependentCollarSlateIntensity.amount ((board H).copies a) ((board H).binder a).center) ≤
    ∑a:H.index,Real.exp (H.strip*(H.binder a).length)*(1+∑e:Fin (H.order+1),(words H.source a).fare e):=by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  let T:=words H.source a
  let P:=WilsonOlderFreshGraphPointWallet.point (H.binder a).center
  have pay:=WilsonOlderFreshGraphVote.before_tests P T.roll T.fare H.strip T.paid T.legal T.positive
    (WilsonOlderFreshGraphArmada.value disk) H.source.radius.le
  have small:WilsonIndependentCollarSlateIntensity.amount T (H.binder a).center ≤ ∑e:Fin (H.order+1),T.fare e:=by
    have count:WilsonIndependentCollarSlateIntensity.amount T (H.binder a).center ≤
        Real.exp (H.strip*P.length)*(∑e:Fin (H.order+1),T.fare e):=pay.2.2
    simpa [P,WilsonOlderFreshGraphPointWallet.point,WilsonOriginalStarSceneRows.length] using count
  exact small.trans (le_add_of_nonneg_left zero_le_one)

end YM.Integration.WilsonMovingForkDepositedPrint
