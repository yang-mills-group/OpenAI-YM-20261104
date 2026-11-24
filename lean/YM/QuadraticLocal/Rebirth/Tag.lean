import YM.QuadraticLocal.Fk.Window
import YM.QuadraticLocal.Rebirth.Reprints
/-!
# Projection endpoint: rebirth of the actual cover model log

 Use unmasked model letter, NOT receipt after remasking. Ward-preserving stamps. Orientation
 kept in Link; prove homogeneity along that link. All this for connected conditional-marked
 coefficients of *every* arity in the Census. Field-independent marks retained too. Use
 current coupling units also on those terms (rank =0 case).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
open QuadraticLocal.Sunrise Marker Earn
variable {ι V α:Type} [DecidableEq V] {R:Census V} {G:Gauge} {n:Side} {P:Passport n V}
open Comparison.RG02 Comparison.RG02.Adjacent
namespace Sleeve
local notation "A"=> (Stationary.Link G n)
variable (X: Row P R G α) (t:α) (w:V→ℕ)
local notation "u★"=> X.lamp.lag
local notation "xρ"=> X.lamp.r
local notation "τ"=> X.lamp.e
variable (M:ι→Row P R G α)
set_option quotPrecheck false
local notation "X'"=> (Stationary.arm G n 1)
local notation "K"=> (Q.Clock.Art.Texture) -- placeholder
variable (Kp:R.Mode)

def coin (i:ℕ)(x:Stationary.Link G n): ℂ:= ( Poly.send X.mode ( X.paint t * (X.markReceipt i x:ℂ)) ).part Kp

lemma heat (b:ℝ)(hp:b ≠0)(i:ℕ)(x:A): b^i • (Sleeve.coin X t Kp i (b⁻¹ • x))= b^X.lamp.lag • Sleeve.coin X t Kp i x:= by
   have he:u★=(X.lamp.e:ℤ)- (X.lamp.r:ℤ):= rfl; unfold coin; simp_rw [Poly.part_send]; split
   next h=>
    unfold Row.markReceipt; split
    next hj=>
       let r:=i-X.lamp.e+X.lamp.r; let F:= Radial.jet (QuadraticLocal.Poetry.Helmet.frame X.atom X.center) r x; rw [show Radial.jet _ r (b⁻¹ • x)= (b⁻¹)^r*F from Tensor.homogeneous (Tensor.coeff (QuadraticLocal.Poetry.Helmet.frame X.atom X.center) r 0) x b⁻¹]
       have hz:(i:ℤ)-(r:ℤ)=u★:=by unfold r; omega
       have hs:b^i*(b⁻¹)^r=b^X.lamp.lag:= by rw [← hz,zpow_sub₀ hp,zpow_natCast,zpow_natCast, div_eq_mul_inv,inv_pow]
       change b^i • (X.paint t * ( ((b⁻¹)^r* F:ℝ):ℂ))=b^(X.lamp.lag) • (X.paint t* (F:ℂ)); rw [←hs]; simp_rw [Complex.real_smul]; push_cast; ring
    next=> simp
   next=> simp
lemma unseen (i:ℕ)(he:i < X.lamp.e)(x:A): Sleeve.coin X t Kp i x=0:= by simp [ Sleeve.coin, Row.markReceipt,he.not_ge]

variable (z:Finset ℤ) (Q:Pace.Coin)(h:Q 0=0)(L j:ℕ)
local notation "Y"=> (Mutation.stamp M Q h L j)
local notation "F"=> (caliber Q h).back L
lemma maturity (i:ι)(u':Mutation.ways M j i)(k:ℕ)(x:A) : Sleeve.coin ( Y ⟨i,u'⟩ ) t Kp k x = if u'.val ≤ k then (Chart.tariff Q h L (M i).lamp.lag u'.val : ℂ)* Sleeve.coin (M i) t Kp (k-u'.val) x else 0 := by
 by_cases hp:u'.val≤k; swap; · rw [if_neg hp]; apply Sleeve.unseen; rw [(Mutation.aged M Q h L j _).2]; change k< (M i).lamp.e+u'.val; omega
 rw [ if_pos hp]; unfold Sleeve.coin; rw [ Poly.part_send, Poly.part_send, Mutation.mode ]; change (if Kp=(M i).mode then _ else 0) = _; split; next=>
    have hv:k-u'.val-(M i).lamp.e=k-((M i).lamp.e+u'.val):=(by omega); have he:(Y ⟨i,u'⟩).lamp.e=( M i ).lamp.e+u'.val:=rfl
    by_cases hk: (M i).lamp.e≤ k-u'.val;
    · simp_rw [Row.markReceipt,he,hv,if_pos hk,if_pos (show (M i).lamp.e+u'.val≤k from by omega)]; change (_ * (M i).paint t )* (_ :ℂ)= _; rw [mul_assoc]; rfl -- rw leaves?
    simp_rw [ Row.markReceipt,he, if_neg hk, if_neg (show ¬ (M i).lamp.e+u'.val≤k from by omega) ]; simp
 next=> simp
-- relation at sweep n<=j.Real signed.He.Frame.Member. use mature to collect parent sum.
local notation "C" v:max i:max x:max=> ( Sleeve.coin ( M i ) t Kp v x )
end Sleeve
end YM.QuadraticLocal.Rebirth
