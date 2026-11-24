import YM.QuadraticLocal.Sunrise.Power
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped BigOperators Topology Classical ContDiff
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I] (J:Census V)
variable (p:I→ Poly J)
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
local notation "φ"=> I→ℝ
local notation "M"=> MvPolynomial I ℝ
local notation "χω"=> (I→ℝ)×Y
local notation "ξ"=> Poly J
local notation "ν"=> Poly.bead J
open MeasureTheory
variable {f g:(I→ℝ)→ℝ} {T: ((I→ℝ)×Y)→ ℝ}
-- polynomial class and choose.Have separability for Plan.N. & integration.
open PowerSeries
local notation "τ"=> Scatter.transmit J p
variable (u v:Book (I→ℝ)) (hu:Clear u)(hv:Clear v)
namespace Reveal
local notation "U"=> u
open Launch
variable (F G:PTable J)(w:V→ℕ)
local notation "θ"=> tag J p
local notation "Φ"=> hom J w
local notation "B"=> Fintype.card V
local notation "Xs"=> series J
local notation "K"=> Index
local notation "log!"=> Extra.Trajectories.connected
variable {r n:ℕ}
def roof (v:ℕ): PTable J:= ∑ i∈range v, (-((↑(i+1):ℂ))⁻¹) • (1-F)^(i+1)
lemma height (v:ℕ) (w':ℕ): Xs v (roof J F w')=logTo w' (Xs v F):= by unfold roof logTo; rw [_root_.map_sum]; simp_rw [series_smul,_root_.map_pow,map_sub,_root_.map_one]
lemma eUp (r:ℕ) (t:ℕ): Φ (roof J F r) = roof J (Φ F) r:=by unfold roof; rw [_root_.map_sum]; simp_rw [Launch.move,_root_.map_pow,map_sub,_root_.map_one]
lemma signs (he:r≤n)(hh:UnitLeading (Xs r F)): log! (Xs r F)= Xs r (roof J F (B + n)):= (log_to (Xs r F) hh (B+n) (fun i=> ((room_for B (fun t:J.Mode=> Finset.card_le_univ _)) i).trans (by omega))).trans (height J F r (B+n)).symm
lemma lifted (h:Xs r G= Poly.pass (Xs r F)): Xs r (Φ G)=Poly.pass (Xs r (Φ F)):=by
 let z:=Fintype.card (V ⊕ Fin r); let X:= ∑ i∈range (z+1),(i.factorial:ℂ)⁻¹ • F^i; have ht :Xs r G=Xs r X:=by rw [h,Poly.pass]; unfold X; rw [_root_.map_sum]; apply sum_congr rfl; intro i _; rw [series_smul,_root_.map_pow]
 rw [show Xs r (Φ G)=_ from (Launch.through J w G X _ ht)]; change Xs r (Φ X)=_; unfold Poly.pass X; rw [_root_.map_sum,_root_.map_sum]; apply sum_congr rfl; intro i _; rw [Launch.move,_root_.map_pow, series_smul,_root_.map_pow]
lemma leading (he : u 0=1) : UnitLeading (Xs r (θ u)):=by rw [UnitLeading,← Join.pair_quiet,polarization]; change ((Nat.factorial 0:ℂ)* (coeff 0 (θ u)).part J.quiet)=1; rw [pointer,he,Scatter.one,Poly.one_part]; simp -- select
-- public when using heat.K.Photo.H.Scope
variable (hs:u 0=1)(hF:∀ i:ℕ,UnitLeading (series J i F))(hp:tag J p u= Launch.hom J w F)
include hF hs hp hu
lemma reports (t:J.Mode)(he:n≤ r) : (τ (LOG u (n+Launch.index J w t))).part t = (observe J r (log! (Xs r F)) n).part t := by
 let k:= r+ Launch.index J w t; have hv : Xs k (θ (LOG u))= Xs k (Φ (roof J F (B+k))):=by
    rw [← answer J p u hu k hs, eUp J F w _ 0, hp]; exact signs J (Φ F) le_rfl (hp ▸ leading J p u hs)
 rw [signs J F (n:=k) (Nat.le_add_right r _) (hF r), observation J r _ he , ← show (PowerSeries.coeff (n+Launch.index J w t) (Φ (roof J F (B+k)))).part t=(PowerSeries.coeff n (roof J F (B+k))).part t from Launch.headgate J w (roof J F (B+k)) t n]
 let c:= n+Launch.index J w t; have hh:c≤ k:= Nat.add_le_add_right he _; rw [← observation J k _ hh, ← hv, observation J k _ hh,pointer]
lemma reports_hot (t:J.Mode)(ht:t ≠ J.quiet)(he:n≤ r) : (τ (LOG u (n+Launch.index J w t))).part t = (observe J r (Order.logMarked (Xs r F)) n).part t := by
 rw [reports J p u hu F w hs hF hp t he, log_full (hF _), observe_add,Poly.part_plus,← log_vacant (hF _),observe_bottom,pure_marks,if_neg ht,zero_add] -- potential `rw` self issue
end Reveal
end YM.QuadraticLocal.Sunrise
