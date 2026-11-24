import YM.QuadraticLocal.Rebirth.Digits
import YM.QuadraticLocal.Rebirth.Reprints
/-!
# Reitter the entire unmasked connected kernel through a bend of its chart.
 Finite budgets on concerned sources. Cauchy merging (no differentiated volume exchange!).
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

local notation "V'"=> (fun i:ι=>Sleeve.coin (M i) t Kp)
-- membership must cover all.Label budgets complete.Edge.St.Frame.Consumer.Stock.*
variable (S:Finset ℤ) (hS:∀ i,(M i).lamp.lag∈ S)
variable {a b:ℝ} {u v:ℕ}
variable (Q:Pace.Coin)(h:Q 0=0)(L j:ℕ)
variable [Fintype V]
set_option quotPrecheck false
local notation "PΩ"=> (fun i:ι=>(M i).paint t)
variable (ha: Air.Staff M (fun i:ι=>(M i).paint t) w a u)
local notation "Z"=> (Mutation.stamp M Q h L j)
variable (T:Finset Age)(B:AllOrder.Floe.Layout G)
local notation "Y" => Air.craft M (fun i:ι=>(M i).paint t) w B T
local notation "z'"=> (fun z:ℤ=> Chart.tariff Q h L z)
local notation "pℓ"=> ( 𝓝 (0:ℝ))
open Comparison.RG02.Moving Path Shift
local notation "Ξ"=> (caliber Q h).back L
local notation "W₁"=> Sleeve.currency t w M Kp T B
local notation "V₁"=> Sleeve.treasury t M Kp
local notation "H"=> (Z)

local notation "D₁"=> (Sleeve.spindle t M Kp Q h L S)
variable (x: Stationary.Link G n)
local notation "Y*"=> (Z)
local notation "F" i:max u:max=> (Sleeve.coin (Z ⟨i,u⟩) t Kp)
local notation "κ" i:max=> ( M i )
local notation "up"=> ( Mutation.ways M j )
omit [Fintype V] in
lemma youth (i:ι) (k:ℕ) (he:k≤j): (∑ b: up i,( F i b ) k x)=∑ a∈range (k+1), (Chart.tariff Q h L ( M i ).lamp.lag (k-a):ℂ)*Sleeve.coin (M i) t Kp a x := by
   let m:= j-(M i).lamp.e; let f(b:ℕ):=(Chart.tariff Q h L (M i).lamp.lag b:ℂ)*Sleeve.coin (M i) t Kp (k-b) x; let u(k':ℕ):= if k'≤k then f k' else 0;
   change ∑ b: Mutation.ways M j i,_ = _; rw [sum_congr rfl («g»:=fun b:up i=>u b.val) (fun b _=> Sleeve.maturity t M Kp Q h L j i b k x), Fin.sum_univ_eq_sum_range u (m+1)];
   have hp: ∑ i∈range (m+1),u i=∑ i∈range (k+1),u i:= by
      rcases le_total k m with h|h; · symm; apply Finset.sum_subset (range_mono (by omega)); intro k' hi hh; unfold u; exact if_neg (by simp only [mem_range] at hh; omega)
      apply Finset.sum_subset (range_mono (by omega)); intro i₀ hk hv; rw [show u i₀=f i₀ from if_pos (mem_range_succ_iff.mp hk)]; unfold f; rw [Sleeve.unseen t (X:=M i) Kp (k-i₀) (by unfold m at hv; simp only [mem_range] at hv hk; omega),mul_zero] -- order arg
   rw [hp,← Finset.sum_range_reflect]; refine Finset.sum_congr rfl (fun i hi=>?_); unfold u f; simp only [Nat.add_sub_cancel]; have he: i ≤ k:= mem_range_succ_iff.mp hi; rw [Nat.sub_sub_self he, if_pos (by omega)]

variable (hz: Air.Staff (Mutation.stamp M Q h L j) (fun i=> ( Mutation.stamp M Q h L j i ).paint t) w b v)
local notation "pP"=> (fun i: Mutation.Names M j => ( Z i ).paint t)
include hz -- he not persisted.
local notation "moneyE" z:max u:max=> ( ((Chart.tariff Q h L z u):ℂ) )
include hS ha
local notation "Wz"=> (Sleeve.currency t w ( Mutation.stamp M Q h L j ) Kp T B)
lemma news_lamp (k:ℕ)(he:k≤j): Sleeve.currency t w (Mutation.stamp M Q h L j) Kp T B k x=Sleeve.spindle t M Kp Q h L S k x:=by
    let f(v:ℕ) (z:ℤ) i:= if ( M i ).lamp.lag=z then ( moneyE z (k-v) )*( Sleeve.coin (M i) t Kp v x ) else 0; let g(v:ℕ)(z:ℤ) := ( moneyE z (k-v) )*( V₁ v z x ); have hf (v:ℕ) (z:ℤ): HasSum (f v z) (g v z):= by
        apply HasSum.congr_fun ((funding t w M Kp ha T B z x v).mul_left ( moneyE z (k-v) )); intro k; unfold f; split; rfl; rw [mul_zero]
    let F₁ i:= ∑ v:up i, (F i v) k x; let A' := ( Finset.range (k+1) ); let f₁ (y:ℕ)(i:ι):=∑ z∈S,f y z i; let t' i:= ∑ y∈ A', f₁ y i; have hh : HasSum t' (D₁ k x):= hasSum_sum (f:=f₁) («s»:=A') (a:=fun v=> ∑ z∈S,g v z) (fun i _=> hasSum_sum («f»:=f i) («s»:=S) (fun z _=> hf i z)); -- arg t signature
    apply ((real_income t w (Mutation.stamp M Q h L j) Kp hz T B k x).sigma (g:=F₁) (fun i=> hasSum_fintype _ ) ).unique; apply HasSum.congr_fun hh; intro i; unfold F₁; rw [youth t M Kp Q h L j x i k he]; unfold t' f₁ f; simp [hS i,A']
lemma reexpressed (k:ℕ) (he:k≤j):
     Adjacent.born (Sleeve.currency t w M Kp T B) ((caliber Q h).back L) 0 j k x= Sleeve.currency t w ( Mutation.stamp M Q h L j ) Kp T B k x:= (born_message t w M Kp S hS Q h L j ha T B x k he).trans (news_lamp t w M Kp S hS Q h L j ha T B x hz k he).symm
end Sleeve
end YM.QuadraticLocal.Rebirth
