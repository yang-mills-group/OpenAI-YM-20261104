import YM.AllOrder.Haiku.Readback
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a C Λ:ℝ}{k N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)

-- ι neutral. require at least one input context. realized at scheduled Tube and full σ via graph. station choose irrelevance.
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ){L':ℕ}
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
    (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
local notation "Lℓ"=> Lobby P K G
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
open AllOrder.Haiku AllOrder.Haiku.Coat Further.PhysicalPeriodLimitF933 Shingle Macrame
variable (q:Clip) (u:ι→PathData G) (g:ι→ℝ) {b C' :ℝ}(V:ι→ℝ)(H:∀ i,(u i).Bounds q b C' (V i)) (W: ι → Towers P.L) -- namespace?
def Gate (t r c:ℝ)(i:ι)(n:Side):= ClassicalMatch (S:=dock P K n) (trees P K n) p q (x i) (u i) (F i n) ∧ FiniteBound (S:=dock P K n) (trees P K n) (x i) (u i) p q (g i) O (F i n) t r c
-- W actually only needed for passing to Local.Pure.frame, can build from Stamp.A? keep

def channel (W: Towers P.L)(i:ι)(n:Side): Tube G (dock P K n) := ⟨W,x i,p,u i,q⟩
def home (k:ℕ)(i:ι)(n:Side) : rule (Coarse G) n→ℝ := topiary P K p O x L Q hx hO F h k i n + Stipend q (u i) (g i) k n
local notation "E0"=> rule (Coarse G) n
local notation "H0"=> home P K p O x L Q hx hO F h q u g

variable {i:ι}{t r c:ℝ}(T : Gate P K p O x F q u g t r c i n)(ht: Ad G P K n)
include T W ht
lemma read_fee (hk:k ≤ 2)(u₀ v:rule (Coarse G) n) : let Q':=channel P K p x q u (W i) i n; let Ψ:= subtractΨ (F:= T[n]) O Q' (label S[n]) (F i n) (g i); let Y:= Stationary.arm G n 1; home P K p O x L Q hx hO F h q u g k i n u₀-H0 k i n v= jet Ψ k (Y v)-jet Ψ k (Y u₀):= by
   intro Q' Ψ Y; let w:= Q'.up; let S':= T[n]; let M:= startup T[n] O (label S[n]) (x i) p Q ht (hx i) (h i n ht) hO; let X'(x₀:rule (Coarse G) n) := ratePlan M k (exteriorL G n x₀)
   have hu(x₀: E0):=actual_top P K p O x L Q hx hO F h i n ht (k:=k) x₀; let f:= topiary P K p O x L Q hx hO F h k i n; let a:=just (preview M) k; let b:= just (Real.log (scaleP (ρ:=F i n) T[n] O (label S[n]) Q')) k
   have hg(x₀:E0): b+ Local.Pure.flip T[n] Q' O (F i n) (label S[n]) k (exteriorL G n x₀) = a+ f x₀ := by rw [← show X' x₀= a+f x₀ from hu x₀]; exact (Response.seed_shadow _ (label S[n]) hO Q' Q ht (hx i) (h i n ht) _ _).symm -- order
   have hz(x:E0): b+board O Q' (F:=T[n]) (label S[n]) (F i n) (g i) k x= a+ H0 k i n x:= by rw [board, ←add_assoc, hg, add_assoc]; rfl
   rw [← annual O Q' (label S[n]) _ (g i) Q ht hO (hx i) (h i n ht) T.1 T.2 hk]; have ht:= hz u₀; have he:=hz v; linarith only [ht,he]
include H
lemma first_two (hk:k<2) (hG:G.Simple): Constant (home P K p O x L Q hx hO F h q u g k i n):= by
 interval_cases k
 · intro X Y; apply sub_eq_zero.mp; rw [read_fee P K p O x L Q hx hO F h q u g W T ht (by norm_num : 0≤2)]; simp
 let f:= H0 1 i n; let Ψ:= subtractΨ O (channel P K p x q u (W i) i n) (label S[n]) (F i n) (g i); let ℓ:= (fderiv ℝ Ψ 0) ∘L (Stationary.arm G n 1).toContinuousLinearMap; have hs: f=(fun _=> f 0)- ⇑ℓ:= by
    funext X; have he:= read_fee P K p O x L Q hx hO F h q u g W T ht (by norm_num : 1≤2) X 0; change f X = f 0- _; rw [eq_sub_iff_add_eq]
    change f X - f 0= jet Ψ _ _-jet Ψ _ _ at he; rw [map_zero, zero_first,zero_first,map_zero] at he; change f X - f 0= 0-ℓ X at he; linarith
 have hV : Stationary.Stained G f := fun j=> by let f':=topiary P K p O x L Q hx hO F h 1 i n; let ht': f' ∘ Stationary.stain j=ᶠ[𝓝 0] f':=Eventually.of_forall ((Refuge.respectful P K p O x L Q hx hO F h 1 i n ht).paints j); exact ht'.add (Coat.presentable q _ _ (H i) _ _ j)
 have heQ : AnalyticAt ℝ f 0:=by rw (occs:=.pos [1]) [hs]; exact analyticAt_const.sub (ℓ.analyticAt _)
 have hv : fderiv ℝ f 0=0:= by apply ContinuousLinearMap.ext; intro X'; have he:= Project.still_one hG hV heQ; simpa [iteratedFDeriv_one_apply] using DFunLike.congr_fun he ![X']
 have hf : fderiv ℝ f 0= -ℓ:= by rw (occs:=.pos [1]) [hs]; rw [fderiv_sub (by exact differentiableAt_const _) ℓ.differentiableAt,ℓ.fderiv]; simp
 have hh: Constant f:= by
    rw (occs:=.pos [1]) [hs]; rw [show ℓ=0 from (neg_eq_zero).1 (hf.symm.trans hv)]; intros x y; rfl
 exact hh
-- second
omit H
def bite (V₀ η:ℝ)(G:Gauge)(t:ℝ)(x: ℝ) (n:Side):= (2:ℝ)⁻¹*((Fintype.card (Uniform.Primary n G):ℝ)^2*x^2 * ((Fintype.card (Site n):ℝ)*t*V₀*Real.exp (-η*n.val)))
lemma second_fee (v : rule (Coarse G) n) {R0:ℝ}(hm: ‖Stationary.arm G n 1 v‖ ≤ R0): |H0 2 i n v-H0 2 i n 0| ≤ bite c r G t R0 n:= by
 let M':= channel P K p x q u (W i) i n; let Y:= Stationary.arm G n 1 v; let F':= Precision.thermal T[n] (label S[n]) p (x i) (F i n) O; let G':=draft («c»:=n) (g i) (u i) q; let K':= F'-G'; let P':= fderiv ℝ (fderiv ℝ K') 0; 
 rw [read_fee P K p O x L Q hx hO F h q u g W T ht (by norm_num : 2≤2) v 0,map_zero, jet_two_H,jet_two_H,map_zero,mul_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg (by norm_num : 0≤ (2:ℝ)⁻¹)];
 refine mul_le_mul_of_nonneg_left (Glowing.confer P' ?_ Y Y hm hm) (by norm_num); intro x' y a b ha hb ; have hA:ContDiffAt ℝ ω F' 0:= T.2.born (label S[n]); have hB:ContDiffAt ℝ ω G' 0:= T.2.classicalResult;
 rw [← (show ∀ a b:Bid.Dir G n,iteratedFDeriv ℝ 2 K' 0 ![a,b]= P' a b from fun a b=> by rw [iteratedFDeriv_two_apply]; rfl), show K'=F'-G' from rfl, iteratedFDeriv_sub_apply (hA.of_le le_top) (hB.of_le le_top),_root_.sub_apply]; exact T.2.wave_price (label S[n]) x' y a b ha hb
end YM.AllOrder.Kinetic.Port
