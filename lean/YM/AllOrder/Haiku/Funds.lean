import YM.AllOrder.Haiku.Origin
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Pump
open Further.PhysicalPeriodLimitF933 Shingle Macrame
variable {A:ℕ→Bills (Coarse G)} {B:ℕ→ Ink.Field (Coarse G)} {P D:ℕ→ℝ} {K:ℕ→Side→ℝ}{Ad: Side→ Prop}
variable (H:∀ k≤N,Pert Ad (A k) (B k) (D k) (P k) (K k) (k+2)) (h : ∀ k≤ N,Ink.Echo.Pulsed (K k))(hD:∀ k ≤ N, 0<D k)(h0:Often Ad)
    (hv : ∀ n k, Ad n → k ≤ N → Etiquette A n k) (n:Side) (hk:k ≤ N)
include H h hD h0 hv hk
lemma armament : Etiquette (fun r n=>(B r).table n) n k := by
 let τ:= Ink.Echo.amplify n; let v p:= convey (α:=L) (Ink.Echo.arm n p); refine ⟨fun X' Y' Z x hX hY hz he=> ?_,fun x u hx=> ?_⟩
 · refine Ink.Echo.index n H h hD h0 X' hX hY hk (fun c p W ht=> ?_); let A0:= hv c k ht hk; let w t:= Z t ∘ W.cut; let V:=convey W (α:=L); let z₁(t:ℝ):=V (X' t); let z₂(t:ℝ):=V (Y' t)
   apply A0.stain z₁ z₂ w x (V.contDiff.contDiffAt.comp _ hX) (V.contDiff.contDiffAt.comp _ hY); · apply tendsto_pi_nhds.mpr; intro i; exact tendsto_pi_nhds.mp hz (W.cut i)
   have hZ(t:ℝ)(V:ℝ→F[n]): life (G:=G) (convey W ∘ V) t=W.links (life V t):= by unfold life echo; simp only [Function.comp_apply]; rw [← map_smul, billing]
   filter_upwards [he] with t ht; rw [show z₂= convey W ∘ Y' from rfl, show z₁= convey W ∘ X' from rfl,hZ, hZ, show life (G:=G) Y' t= _ from ht,  Haiku.colored] -- probably life z₁ defeq rw issue
 let y := orderTurn (G:=G) u ∘ x; refine tendsto_nhds_unique_of_eventuallyEq (Ink.Echo.inspect n H h hD h0 x hx hk) (Ink.Echo.inspect n H h hD h0 y ((orderTurn u).contDiff.contDiffAt.comp _ hx) hk) ?_; rcases h0 with ⟨d,hd⟩; filter_upwards [(Ink.Echo.limitless n).eventually (eventually_ge_atTop d)] with i hi
 let V':= v i; let p':= V' ∘ x; apply congr_arg; change weigh p' _ _= weigh (V'∘ y) _ _; rw [(hv (τ i) k (hd _ hi) hk).sign p' u (V'.contDiff.contDiffAt.comp _ hx)]; rw [show orderTurn (G:=G) u ∘ p'= V' ∘ y from funext fun j=>(signing i u (x j)).symm]
end Pump
end YM.AllOrder.Haiku
