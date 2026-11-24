import YM.Qlocal.Quipu.Shaper
import YM.Qlocal.Quipu.Sector
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Tern
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial AllOrder Fire Laplace Laplace.SigmaP Ker Ker.Start
open Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Tilt
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{c r:Side}{a b C D Λ σ:ℝ}{k N l i j n m:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
variable {α:Type}[Fintype α] [DecidableEq α] {B:Marker.Census α}
local notation "Y"=> ((Coarse G⊕α)⊕ J)
local notation "Ω[" n "]"=> rule ((Coarse G⊕α)⊕J) n
variable (t:Senses B)(M: Vase t G i) (p:α→Site P.L) (π:ℕ→Prop)(A:Album ℕ t G i)
variable (hc: Ad G P K c)(x:Site c)(V:Ker.rule ((Coarse G⊕α)⊕RealSlice.Vertical G P K) c)
set_option quotPrecheck false
open Vase Album Arbor
local notation "T₀"=> Tern.plane P K hc
local notation "Q⌖"=> tag P K t p M hc x k
local notation "L'"=> zstar S[c] t p x
local notation "W"=> Tern.vehicle (α:=α) P K hc
local notation "Z"=> chip P N a
local notation "Φ"=> Tern.heightZ P K t p π A
local notation "Λ'"=> (heightZ P K t p π A)
variable (h:Health (a:=a) A C)(ha:0<a) (hQ: PaintSupply G N σ)(hB:P.Branches K G)
include h ha hQ
lemma facts (n:Side)(hn:I₀ n): let f:= Φ n k; let a':=Z; Scatter Prod.fst (weaker N a') N f 0 (stampZ P G B t i k N σ a*C*countCost (a'/2)) ∧ ContDiffAt ℝ ω f 0:= finance P K t p π A hn _ h ha hQ (Metric.mem_ball_self zero_lt_one)
def pageT (k h:ℕ)(n:Side):= iteratedFDeriv ℝ (h+1) (heightZ P K t p π A n k) 0
local notation "V1"=> pageT P K t p π A k j
local notation "F1"=>fun (n:Side)=> extractF (V1 n)
def rateF (P:Patch) (G:Gauge)(B:Marker.Census α)(t:Senses B)(i k N j:ℕ)(a σ:ℝ):=stampZ P G B t i k N σ a * countCost (chip P N a/2)*boltC j (weaker N (chip P N a))
include hB
lemma squeezes : 0<weaker N Z:= by unfold weaker; apply div_pos (Tern.chip_pos P ha _) (by positivity)
lemma fees_ge : 0 ≤ rateF P G B t i k N j a σ := mul_nonneg (mul_nonneg (stamp_pos P K t ha hQ) ((count_pos (half_pos (Tern.chip_pos P ha N))).le)) (boltC_pos j (squeezes P K t A h ha hQ hB)).le
lemma qualified (hk:j+1 ≤ N): ∃ f : Fan ((Coarse G⊕α)⊕ J) ((Coarse G⊕α)⊕J) j, Cap f (small_a (weaker N (chip P N a))) (rateF P G B t i k N j a σ*C) ∧ ∀ n:Side,Ad G P K n→ extractF (pageT P K t p π A k j n)=pieces f n:= by
 let he := dock_larger P K hB; let η:=stampZ P G B t i k N σ a*C*countCost (Z/2); let w:=weaker N Z; have hp n (hh:I₀ n): ContDiffAt ℝ ω (Φ n k) 0:= (facts P K t p π A h ha hQ n hh).2
 have hy : rateF P G B t i k N j a σ*C=η*boltC j w:= by unfold η rateF w; ring
 rw [hy]; let f:=F1; apply obtain_fan he; rotate_left
 · intro n hn i t₀; let u:Fin (j+1)→ Leaf n ((Coarse G⊕α)⊕ J):= Fin.cons i t₀; have hv:= (facts P K t p π A h ha hQ n hn (k:=k)).1 _ hk u 0; let H:=V1 n; change |extractF (H) i t₀| ≤ _; apply le_trans (b:=‖entry (Φ n k) 0 u‖); swap
   · apply hv.trans_eq; rw [spanSites,Fin.sum_univ_succ, separation_self, zero_add]; rfl -- no orientation?
   apply le_of_eq; refine (congr_arg abs ?_); unfold entry extractF H pageT; apply congr_arg; funext s; refine Fin.cases rfl (fun i=>rfl) s
 · exact squeezes P K t A h ha hQ hB
 · exact mul_nonneg (mul_nonneg (stamp_pos P K t ha hQ) ((tsum_nonneg h.1).trans h.2.2)) (count_pos (half_pos (Tern.chip_pos P ha _))).le
 have hg (c r:Side)(hn:I₀ c)(hm:I₀ r)(n:ℕ)(L:Lacing P c r n): pilots L.low (V1 c) (V1 r):= flight L.low (hp c hn) (hp r hm) (Eventually.of_forall fun v=> recruits P K t p π A hn hm v L) -- shadow
 have hu(c:Side)(hc:I₀ c)(p:Site c):pilots (Macrame.parallel p) (V1 c) (V1 c):= hg c c hc hc 1 (Macrame.Lace.hub p (le_trans (by norm_num : 2 ≤ 3) (enough P K hc)))
 refine ⟨fun n a=>pilots.still (hu n a),fun n m a b L hv=>?_⟩; exact cooks _ (pow_pos (Nat.pos_of_mul_pos_left (show 0<n.val*L from hv ▸ m.property)) _) (hg n m b a (L^4) (Macrame.Lace.project hv (show 2 ≤ n.val from le_trans (by norm_num) (enough P K b)))) (hu m a) -- order
end YM.Qlocal.Quipu.Sonnet.Tern
