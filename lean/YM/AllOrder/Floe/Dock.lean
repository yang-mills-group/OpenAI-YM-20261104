import YM.AllOrder.Iron.Canvas
import YM.AllOrder.Floe.Coast
import YM.AllOrder.Floe.Alpine
/-!
# Senior width payments. The prestage choices (`fore` from post geometry
 estimate of inverse coarse Hessian and `breath` from patch.Setup) must cover
 any Licence purchase at old mesh.Coordinate depends only on precursor expenses.
  Θ belt constants & loop expenses also inside the market."early.Learn."
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a b C D Λ σ:ℝ}{k N l:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
set_option quotPrecheck false
local notation "Q[" n "," hn "]"=> (arbitrate P K (n:=n) hn)
variable {ι:Type} [Nonempty ι] (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i)) (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "A[" i "," n "]"=> clay P K (x i) p n
local notation "u[" i "," n "]"=> Lapis.orbit T[n] (F i n)
variable (V:ι→ Layout G) (T:Finset Age) (hV:∀ i,Legal T (V i)) (Γ:ι→ℝ)
local notation "D[" i "," n "," hn "]"=> (startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO)
local notation "W"=> License (Ad G P K) Γ
-- receipt capacitance after fixing Q at ≥k.Opaque s.Width.
structure PortPre (p : Clip)(x : ι→PathData G)(σ A B:ℝ) where
 peak : ι → Stalk (Lobby P K G) (Lobby P K G)
 deep : ι → Stalk (RealSlice.Vertical G P K) (RealSlice.Vertical G P K)
 nonneg:0≤A ∧ 0≤B
 peak_bound : ∀ i,Belt (peak i) σ A
 deep_bound : ∀ i,Belt (deep i) σ B
 sheet : ∀ n i, Ad G P K n→ direct (peak i) n=headMatrix (seedT P K p (x i) n)
 put : ∀ n i, Ad G P K n→ direct (deep i) n=(Ker.Start.pulse P K p (x i) n)⁻¹
-- for `bed data`; Γ fixed.
variable {C' B B' γ δ ε η:ℝ}
include hx hB Q
open Iron
variable (D':Sky K G P.J δ γ ε) (T':ι→Bed) (hT:∀ i, Attached (T' i) (x i)) (hZ:∀ i,(T' i).metric.strip δ γ) (hh:∀ i n,Floor (T' i) p n ε η)(hg:∀ i n,Bid.Sworn (T' i) n G)
local notation "γ₀" => small_a (Iron.breath a (N+3))
include hh hg hT hZ
lemma tracks : Nonempty (PortPre P K p x (min (γ₀) D'.width) (rev P K p Q 1) (D'.p P)):= by
 choose f h₁ hf using fun i:ι => class_payoff P K (x i) p Q (hx i) hB (show 1+1 ≤ N+3 from (by omega)); choose g h₂ hG' using fun i:ι=> D'.handle P rfl Q (x i) (hx i) (hT i) (hZ i) (hh i) (hg i) hB
 have he: 0<a:= (hx (Classical.arbitrary ι)).width; have hy : 0 ≤ (rev P K p Q 1):= by unfold rev; have ht:= reignQ P K p x L Q hB hx|>.2.2.1; exact mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le) (boltC_pos _ (Iron.breath_pos he ..)).le
 refine ⟨⟨fun i=> stick (f i),fun i=> stick (g i),⟨hy,D'.nonneg _⟩,fun i=>(stick_belt (h₁ i)).debt (min_le_left ..) le_rfl, fun i=>(stick_belt (h₂ i)).debt (min_le_right ..) le_rfl, fun n i hn=> by rw [stick_entry,← hf i n hn]; rfl, fun n i hn=> by rw [stick_entry,←hG' i n hn, green, Ker.Spine.unpack]⟩⟩
omit hh hg hT hZ
variable (A:PortPre P K p x b B B')(ht:0<b)
-- variable after? include/omit
include A
lemma standing (hn:Ad G P K n)(i:ι) : direct (A.peak i) n= Kinetic.mail (exteriorL G n) (interiorL P K G hn) A[i,n] ∧ direct (A.deep i) n= (Kinetic.pulse (exteriorL G n) (interiorL P K G hn) A[i,n])⁻¹:= by rw [A.sheet n i hn, A.put n i hn,pcs,meters]; trivial
abbrev stalk (i:ι) := applyM (A.peak i) (A.deep i)
omit hB hx Q
include ht
lemma tide : ∀ i,Belt (stalk P K p x A i) b (billH (Coarse G) (RealSlice.Vertical G P K) B B'):= fun i=> (rentM (n:=three) (A.peak i) (A.deep i) 0 0 ht.le (A.peak_bound i) (A.deep_bound i) A.nonneg.2).1
lemma granted : 0≤ billH (Coarse G) (RealSlice.Vertical G P K) B B' := by have hx:= A.nonneg; unfold billH; have hv:=hx.1; have hh:= hx.2; positivity
end YM.AllOrder.Floe
