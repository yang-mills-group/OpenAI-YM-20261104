import YM.Qlocal.Quipu.Shingle
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
local notation "Q"=> tag P K t p M hc x k
local notation "L'"=> zstar S[c] t p x
local notation "W"=> Tern.vehicle (α:=α) P K hc
local notation "V'"=> (Metric.ball (0:Ω[c]) 1)
local notation "G'"=> (tents (pawn P K α G) c)
set_option maxHeartbeats 300000 in
lemma shortplane : ‖Tern.plane (α:=α) P K hc‖ ≤ 1:= by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro j; change ‖leaner P K i ((mapper P K G (enough P K hc)).symm j)‖≤ _; exact norm_le_pi_norm i (up (Tilt.passB (G:=G) P K α α) ((mapper P K G (enough P K hc)).symm j))
variable (hQ: PaintSupply G N σ)(hv:V∈ Metric.ball 0 1)
local notation "u0"=> composeCost N (fineCost G N σ) 1
local notation "d0"=> 1+composeCost N (fineCost G N σ) 1 -- macro precedence
include hQ hv
lemma capable (e: Edge (Site (below P c))) : Allows N (fun v=> G.mat ((W v) e)) V u0:= by
 have hp : ‖T₀ V‖≤1:= ((ContinuousLinearMap.le_of_opNorm_le _ (shortplane (α:=α) P K hc) V)).trans (by simpa only [one_mul] using (mem_ball_zero_iff.mp hv).le); exact ((fine_supply T[c] hQ).2.2 _ _ hp).comp (allows_linear (shortplane P K hc) hp)
omit hv in
include P K in
lemma payok : 0≤composeCost N (fineCost G N σ) 1:= by
 unfold composeCost; have ht:= hQ.1; have hv : 0≤ fineCost G N σ:= (fine_supply T[RealSlice.three] hQ).2.1
 positivity
lemma equates : Weather W V∧ Mode W V N (1+composeCost N (fineCost G N σ) 1):= by
 let d:= u0; have he e:=capable P K hc V hQ hv e; refine ⟨fun i=>(he i).analytic,add_nonneg zero_le_one (payok P K hQ), fun j=> ?_⟩; have hp:Brush N d 1 (fun v=>G.mat (W v j)) V:= Brush.offer.2 ⟨((he j).analytic.of_le le_top),(he j).norm_le⟩; have hf:= thicken (f:=fun v=>W v j) hp; simpa only [mul_one] using! hf -- thicken arg f
-- credit/stamp.Marker cost presence matches. independent.#
omit hQ in
lemma lands_cost (T:Places t c): Allows N (placard T ∘ lands (G:=G) P K) V ((1+(essence t).card:ℝ)^N):= by
 let L0(i:↥(essence t)) : Ω[c] →L[ℝ]ℝ:= ContinuousLinearMap.proj (φ:=fun _: Leaf c ((Coarse G⊕α)⊕J)=>ℝ) (T i, pawn P K α G i.val); have hh (i):Brush N 1 1 (L0 i) V:= by
    have hm:‖L0 i‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; exact norm_le_pi_norm v ..
    refine (Brush.linearB (L0 i) ?_ ?_ zero_le_one); exact (ContinuousLinearMap.le_of_opNorm_le _ hm V).trans (by simpa only [one_mul] using (mem_ball_zero_iff.mp hv).le); simpa using hm
 let u:= (essence t).card
 have ht:Brush N 1 (u:ℝ) (placard T ∘ lands P K) V:= by simpa using! (Brush.all_prod univ _ (fun _=>1) (fun _=>1) (fun i _=> hh i)); -- footprint.Log
 refine ⟨?_, fun i hi=> (Brush.offer.1 (ht.trim.climb (by simp [u]) le_rfl)).inside _ hi⟩; exact (((product_rank T).lead G').read.smooth).contDiffAt
-- moments spreads
abbrev funds (P:Patch)(G:Gauge)(α:Type)[Fintype α][DecidableEq α]{B:Marker.Census α}(t:Senses B) (n k N:ℕ) (σ a:ℝ):= 2^N * Vase.capita G n k N (1+composeCost N (fineCost G N σ) 1) a *((1+(essence t).card:ℝ)^N)
-- actually remove first factors. Hue.Header.L title.
omit hv in
include P K in
lemma funds_ge(ha:0<a) : 0≤funds P G α t i k N σ a:=by
 have hp:= payok P K hQ; have hr:0≤1+composeCost N (fineCost G N σ) 1:=add_nonneg zero_le_one hp; unfold funds; have hh:= capita_ge G i k N hr ha; positivity
lemma checked (ha:0<a): Allows N (tag P K t p M hc x k) V ((funds P G α t i k N σ a)* Vase.fare M a):=by
 let w:= M.momentum; let d:= u0; let f:= M.fare a; let b:=capita G i k N (1+d) a; let T:=family S[c] M.stage p x; let a':=((1+(essence t).card:ℝ)^N); have hs:0≤ funds P G α t i k N σ a:=funds_ge P K t hQ ha; have hg:0≤d:=payok P K hQ; have h'b:0≤b:=capita_ge G i k N (add_nonneg zero_le_one hg) ha; have h'f:0≤f:=M.nn_size.trans (M.sizes ha.le)
 unfold tag Arbor.mass; have hL:= equates P K hc V hQ hv; have h:Allows N (M.read L' k ∘ W) V (b*f):= by
    have hp:= M.palace L' (hL.2) k ha; refine ⟨?_,(Brush.offer.1 hp).inside⟩; rw [show (M.read L' k ∘ W)=Complex.reCLM ∘ (M.swatch L' k ∘ Work.F02.physical ∘ W) from ?_]; swap; · funext t; rw [Function.comp_apply]; exact ((congr_arg Complex.re (real_bill M L' (W t) k)).trans (Complex.ofReal_re _)).symm
    exact Complex.reCLM.contDiff.contDiffAt.comp _ (((M.reign L' k ).restrict_scalars ℝ).contDiffAt.comp _ (Work.F02.physical_contDiffAt hL.1))
 -- check precedence.Auth.
 split; next hQ0 => refine (Allows.bilinear (ContinuousLinearMap.mul ℝ ℝ) h (lands_cost P K t V hv T) (ContinuousLinearMap.opNorm_mul_le ..)).mono ?_; unfold funds; change 2^N*1*(b*f)*a' ≤ 2^N*b*a'*f; apply le_of_eq; ring
 exact allows_const _ ((norm_zero).trans_le (mul_nonneg hs h'f))
end YM.Qlocal.Quipu.Sonnet.Tern
