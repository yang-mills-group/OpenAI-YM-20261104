import YM.QuadraticLocal.Poetry.Planet
/-!
# Pump value, color integral, and level proof
 Site registry projection knows all lamp roots and normalized basis stamps not chosen after tests.
 Use on deployed *real kernel*, never substitute actual POL scope. Warranty: entire curvature
 across any small and large periods, rank shift before tags. Allows STILL unrounded canonical answer,
 E.Read. Continue propagating through actual charts separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Rovers
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
local notation "R"=> Point (Coarse G)
open Pinned Knot Picket
variable (F:AllOrder.Ink.Field (Coarse G⊕M))(h:Fixed H q F)(hp:F.Good a C k)
local notation "U"=> planet F
variable (A: Stationary.Link G n)(v:rule M n)(x:Site n)(hφ:∀ n (A:Link G n)(v:rule M n)(p:BaseSites G n),F.table n (mingle A v)=F.table n (mingle (A-gradientA G n p) v))
local notation "Xp"=> sendLink x A
local notation "s"=> pathGradient Xp
local notation "Y" => Xp - grad (pathGradient Xp)
variable (ha:0<a)(hf:Roll.Faith (planet F) H q k b D)(hb:0<b)
include ha hφ hb hf hp h
lemma house : F.site n x (mingle A v)=(planet F).goal x A v:= by
 let C₀:= ‖arm G n 1 A‖; have ht:∀ i,‖s i‖≤ C₀*size i:=fun q=> Pinned.path_price _ q (fun i=> norm_le_pi_norm (arm G n 1 A) _)
 rw [ticket H q F A v x (pathGradient Xp) (show 0 ≤ C₀ from by positivity) ht ha hp h hφ]; unfold Roll.goal; let g:= (U).dusk x A v; change _ = ∑' i:((i:F.Ty) × Project (F.slip i)),(U).dusk x A v i; rw [((U).confirmed H q hf hb x A v).tsum_sigma]; apply tsum_congr; intro i; rw [tsum_fintype]; exact message (F.slip i) (F.fee i) A x v
variable (hγ:∀ n (A:Link G n)(v:rule M n)(u:G.El), F.table n (mingle (stain u A) v)=F.table n (mingle A v))
local notation "X"=> Roll.illuminate (planet F)
include hγ
lemma gallery : F.site n x (mingle A v)= (X).goal x A v:= by
 obtain ⟨P,hP⟩:= Texture.samples G k; let g(q:G.El):= F.site n x (mingle (stain q A) v); let G₁(i:G.El)(j:(planet F).Ty):= (U).dusk x (Stationary.stain i A) v j; let T i j:= P i *G₁ i j; have hh i : g i= ∑' j:(planet F).Ty,G₁ i j:= house H q F h hp (stain i A) v x hφ ha hf hb; have ht i : g i= F.site n x (mingle A v):= by unfold g; rw [← h.receipt, hγ, Picket.Fixed.receipt _ _ _ h]
 rw [show F.site _ _ _=∑ i∈P.support,P i * g i from ?_]; swap; · simp_rw [ht,← Finset.sum_mul,Texture.economy P hP,one_mul]
 have hv : ∀ i, HasSum (T i) (P i*g i):= fun i=> (hh i).symm ▸ (((U).confirmed H q hf hb x (stain i A) v).hasSum.mul_left (P i))
 unfold Roll.goal; refine ((hasSum_sum (f:=T) (a:=fun i:G.El=>P i*g i) («s»:=P.support) (fun i _=> hv i)).congr_fun (fun j=>?_)).tsum_eq.symm
 -- `congr_fun` goal
 exact Lantern.rank ((U).leg j) x A v P hP (((U).leg j).card_le (hf.pinned j).tall).1
end YM.QuadraticLocal.Poetry.Rovers
