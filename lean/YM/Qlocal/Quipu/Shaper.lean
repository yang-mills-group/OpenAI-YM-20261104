import YM.Qlocal.Quipu.Auth
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
local notation "V'"=> (Metric.ball (0:Ω[c]) 1)
local notation "G'"=> (tents (pawn P K α G) c)
-- paid root radius ANY warp. `Vℓ` in unit ball => Beacon.
-- Amplify by L (core estimate needed to sustain widths); poly and dearth.Ex.All unused pre-L α.
variable (h:Health (a:=a) A C)(ha:0<a) (hQ: PaintSupply G N σ)(hv:V∈ Metric.ball 0 1)
def chip (P:Patch)(N:ℕ)(a:ℝ):= P.L.val*a/(2*(N+1:ℕ))
protected lemma chip_pos (ha:0<a)(N):0<chip P N a:= by unfold chip; positivity
local notation "Z"=> chip P N a
local notation "Q*"=> (funds P G α t i k N σ (a/2))
def stampZ (P:Patch) (G:Gauge)(B:Marker.Census α)(t:Senses B)(i k N:ℕ)(σ a:ℝ):= funds P G α t i k N σ (a/2)*Real.exp (12* N*chip P N a)
local notation "Q'"=> stampZ P G B t i k N σ a
include P K ha hQ
lemma stamp_pos : 0≤ stampZ P G B t i k N σ a:= mul_nonneg (funds_ge P K t hQ (half_pos ha)) (Real.exp_pos _).le
omit hQ P in
private lemma fee2 : M.fare (a/2) ≤ M.fare a:= by
 unfold Vase.fare; gcongr; · exact M.nn_size -- maybe gcongr consumes nonneg goals
 exact (half_le_self ha.le)
local notation "k'"=> Q* * M.fare (a/2)
include hv
lemma savory : Beacon Prod.fst Z N Q⌖ x V (Q' * M.fare a):= by
 let r:= M.momentum
 apply Beacon.mono (Allows.beacon (checked P K t M p hc x V hQ hv (a:=a/2) (k:=k) (half_pos ha)) (belongs P K t M p hc x k) (Filter.univ_mem) (Tern.chip_pos P ha N|>.le)); let A:=r/P.L.val
 have hM: (A:ℝ) * P.L.val ≤ r:=by exact_mod_cast Nat.div_mul_le_self r P.L.val
 unfold funds stampZ Vase.fare; -- simplify exp. budget x : 
 change (Q*)* (M.sizeC * Real.exp (a/2*r)) * Real.exp (Z*↑(N*(A+12))) ≤ (Q*)*Real.exp (12*N*Z)*(M.sizeC*Real.exp (a*r)); rw [show (Q*)* (M.sizeC * Real.exp (a/2*r))*Real.exp (Z*↑(N*(A+12))) =((Q*)* M.sizeC)*(Real.exp (a/2*r)*Real.exp (Z*↑(N*(A+12)))) from by ring, (mul_mul_mul_comm (Q*) (Real.exp (12*N*Z)) _ _)]; simp_rw [← Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (mul_nonneg (funds_ge P K t hQ (half_pos ha)) M.nn_size)
 unfold chip; push_cast; field_simp; nlinarith [show 0≤(r:ℝ) from by positivity, mul_le_mul_of_nonneg_left hM ha.le, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM ha.le) (Nat.cast_nonneg (α:=ℝ) N)]
include h
lemma season : ContDiffAt ℝ ω (ridge P K t p π A (k:=k) hc x) V:= by
 let T (x': Places t c) (y:Ω[c]):= let s0:=x'; if x' (pivot t) = x then picture π A (drew S[c] x' p) k (W y) * placard s0 (lands P K y) else 0;
 have hW := (equates P K hc V hQ hv).1
 rw [show ridge P K t p π A (k:=k) hc x=(fun y=> ∑ x', T x' y) from funext fun y=> Arbor.sector S[c] p x (W y) _ π h ha]
 refine ContDiffAt.sum (fun i hi=>?_); unfold T; dsimp only; split; swap; · exact contDiffAt_const
 apply ContDiffAt.mul (winter _ A _ k h ha W hW); exact (lands_cost P K t V hv i (N:=N)).analytic -- order args
lemma counted : Beacon Prod.fst Z N (ridge P K t p π A (k:=k) hc x) x V (Q'*C) := by
 let A' i':= fun y=> Arbor.village S[c] p π A (lands P K y) k (W y) x i'; let P':= Metric.ball (0:Ω[c]) 1
 let f j:=funds P G α t i k N σ a * (A j).fare a; let f' j:= Q' * (A j).fare a
 have He j:0≤f j:= mul_nonneg (funds_ge P K t hQ ha) (h.1 j); have He' j:0≤f' j:=mul_nonneg (stamp_pos P K t ha hQ) (h.1 j)
 refine beacon_tsum (u:=A') Metric.isOpen_ball ((convex_ball ..).isPreconnected) (P:=f) (Q:=f') (h.2.1.mul_left _) (budget_scale (stamp_pos P K t ha hQ) h) (fun i y hy=> ?_) hv (fun j=> ?_)
 · unfold A' Arbor.village; split; exact checked P K t (A i) p hc x y hQ hy ha; apply allows_const; exact norm_zero.trans_le (He i)
 unfold A' Arbor.village; split; exact savory P K t (A j) p hc x V ha hQ hv; intro k hk q; refine (_root_.norm_eq_zero.mpr ?_).trans_le (mul_nonneg (He' _) (Real.exp_pos _).le); unfold entry; cases k<;>simp
-- final scatter
include hc
lemma finance : let Q:= heightZ (t:=t) P K p π A c k; Scatter Prod.fst (weaker N Z) N Q V (Q'*C*countCost (Z/2)) ∧ ContDiffAt ℝ ω Q V:= by
 intro v; rw [show v=(fun y=>∑ x:Site c,ridge P K t p π A (k:=k) hc x y) from funext fun y=> dif_pos hc]; have hp x:= season P K t p π A hc x V h ha hQ hv (k:=k); have hF x (_:x∈univ) := hp x; refine ⟨?_,ContDiffAt.sum hF⟩; have ht :0 ≤ C:= (tsum_nonneg h.1).trans h.2.2; simpa only [Nat.cast_one,mul_one] using! scatter (Multiplicity.injective (Function.injective_id)) hp (fun x=>counted (k:=k) P K t p π A hc x V h ha hQ hv) (Tern.chip_pos P ha _) (mul_nonneg (stamp_pos P K t ha hQ) ht)
end YM.Qlocal.Quipu.Sonnet.Tern
