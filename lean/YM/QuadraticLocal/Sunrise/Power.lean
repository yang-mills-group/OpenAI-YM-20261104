import YM.QuadraticLocal.Sunrise.Launch
import YM.QuadraticLocal.Sunrise.Bead
/-!
# Matrix at the κ plus mark bill. Formal trace from Run.Bulk.Fk surgery
No opaque label equivalence; COST of Mark identities only appears after SPEC revenue.
-/
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
-- moment units X. No Y reserve assertion
abbrev tag:= PowerSeries.mk (fun i=>Scatter.transmit J p (u i))
local notation "θ"=> tag J p
local notation "Λ"=> (Poly J)
lemma pointer (i:ℕ): PowerSeries.coeff i (θ u)=τ (u i):= coeff_mk ..
include hu hv
lemma union : θ (alters u v)= θ u * θ v:= by
 ext1 k
 rw [pointer,coeff_mul]; simp_rw [pointer, ←Scatter.carry (hu _) (hv _)]; rw [← Scatter.pile _ _ _ (fun i hi=> (hu _).mul (hv _))]
 refine congr_arg τ (funext fun x=> ?_); change plus (swap u x) (swap v x) k = _; rw [plus_sum, Finset.sum_apply]; rfl
omit hv
lemma times (k:ℕ): θ (energy u k)=(θ u)^k:=by
 induction k with
 | zero=>
    ext1 k; rw [pointer,pow_zero,coeff_one,level]; by_cases h:k=0
    · subst k; simp only [if_true]; exact Scatter.one ..
    rw [if_neg h,show wirings (X:=φ) (fun _=>1) k=0 from (by ext1 x; simp [wirings,just,Function.swap,h])]; exact Scatter.chars ..
 | succ k ih=> rw [powered, Reveal.union J p _ _ (fun i=> square_p (fun i=>hu i) _ i) hu, ih, pow_succ]
variable (r:ℕ)
local notation "Λ0"=> Fintype.card (V ⊕ Fin r)
lemma pennant (he:u 0=0): Poly.pass (series J r (θ u))=series J r (θ (EXP u)):= by
 let F(i:ℕ):=(i.factorial:ℂ)⁻¹; let p':= tag J p u; let z:=Λ0; let t := ∑ j∈range (z+1), F j • (p'^j)
 rw [show Poly.pass _=(series J r) t from ?_,Order.trunc_complete]; swap
 · unfold t p' Poly.pass; rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [series_smul,map_pow]
 ext1 i; rw [coeff_trunc,coeff_trunc]; split_ifs with h
 · unfold t; rw [pointer,Expo he (show i≤ z from (Nat.le_of_lt_succ h).trans (by simp [z])),map_sum]; unfold arrow; rw [Finset.sum_apply]; let f(j:ℕ):= energy u j i
   change ∑ x∈_,(coeff i (F x • p' ^ x))= τ (∑ j∈range (z+1), ((j.factorial:ℝ)⁻¹) • energy u j i); rw [Scatter.pile _ _ _ (fun j _=> Plausible.scale ((j.factorial:ℝ)⁻¹) (square_p (fun i=>hu i) j i))]; refine sum_congr rfl fun j _=>?_ ; rw [show p'^j= tag _ p (energy u j) from (times J p u hu j).symm,coeff_smul,pointer]; change F j • _ = τ (((j.factorial:ℝ)⁻¹) • f j); rw [Scatter.mul _ _ _ (square_p (fun i=>hu i) j i)]; unfold F; push_cast; rfl
 rfl
local notation "B₀"=> Board J r
omit hu
lemma canon (he:u 0=0) : (series J r (θ u)).part (B₀).quiet=0:=by
   rw [← (Join.pair_quiet (R:=J) (S:=indices r)),polarization] -- maybe
   change (Nat.factorial 0:ℂ)* (coeff 0 (tag J p u)).part J.quiet=0
   rw [pointer,he,Scatter.chars,Poly.part_nil,mul_zero]
include hu
lemma answer (he:u 0=1) : Extra.Trajectories.connected (series J r (θ u))=series J r (θ (LOG u)):=by
   have hF: Clear (LOG u):= fun i=> Response.log_p (fun i=>hu i) he i
   have h0: LOG u 0=0:= fades he
   have hu':= pennant J p (LOG u) hF r h0
   rw [Fire.exponent_inv he] at hu'; rw [← hu']
   apply Cumulants.connected_pass (canon J p (LOG u) r h0)
end Reveal
end YM.QuadraticLocal.Sunrise
