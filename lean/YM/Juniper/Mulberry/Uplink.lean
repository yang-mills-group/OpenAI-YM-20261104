import YM.Juniper.Mulberry.Drape
/-!
 # Financial org + radius upgrade (from grant for the E model)
 Uniform charge needed on POLY shell. Numerical inequalities
 *inside each stage* with gain, then buy them on actual path. log polynomial
 POST output paid. Need enough INTERNAL orders (ρ^n replaced by (ρ/ζ)^n),
 degrade one time not iterated; retains honest multiple Input bills. Precision
 loss only here for comparing outputs to arctic. Note Ψ/ϕ/B weights unchanged.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson Pressure Lattice
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open LocalAtlas
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {ι : Type}[Fintype ι][DecidableEq ι]
    {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {φ ψ : E × Poll.Body ι→ℝ}{ρ:E→ Poll.Body ι}{M : E→ Matrix ι ι ℝ}
    {k n : ℕ} {x:ℝ × E}{D b p W t q d C L : ℝ}
local notation "K"=> (M 0)⁻¹
local notation "F" => Poll.Body ι
local notation "V" => ℝ × E
local notation "g" => grace φ ψ ρ M
local notation "μ"=> sweep (M 0)⁻¹
local notation "Ω"=> closedBall (0:Poll.Body ι) D
local notation "v"=> b/q
local notation "X"=> (Real.exp (-1)*(1/2:ℝ))
local notation "X!"=> (X / 2)
local notation "Y!"=> (Real.exp 1 + X!)
structure Status (k n:ℕ)(p W Z B D L d A q C:ℝ) :Prop where
   tuition : 1 ≤ D
   mad : ∀ y∈Icc (-1:ℝ) 1, Brush k Z 1 Real.exp y
   nature : Treasury k L (Real.exp (-1)*(1/2:ℝ)/2) (Real.exp 1+ Real.exp (-1)*(1/2:ℝ)/2)
   possible : 0<q
   sane : q ≤ 1
   scaledSmall : B/q ≤1
   simple : (fee k p D+W)*(B/q) ≤ 1
   fraction : 0<d
   solvent : d^2 ≤ (1/2:ℝ)
   wheat : let a:=clump k (travelW k p D W) Z; let e:= a*(d*gamut A C (2*((k+2)*k)) + d^2*d⁻¹); Mulberry.cost0 k n (clump k (fee k p D+W) Z) (B/q) e ≤ Real.exp (-1)*(1/2:ℝ)/2
section here
variable (H : Golf φ ψ ρ M k D b b p) {f: Poll.Body ι→ (ℝ×E)→ℝ}(hs : Tilt k b D q W f)
variable {Z A:ℝ}(hn:n+1≤ k) (hp:Status k n p W Z b D L d A q C)
     (hh: (sweep (M 0)⁻¹).real (closedBall (0:Poll.Body ι) D)ᶜ ≤ d^2)
     (hv:(Fintype.card ι:ℝ) ≤ A) (hK:∀ z:ι→ℝ, dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ C*dotProduct z z)
local notation "g!"=> (g+f)
local notation "V'"=> foldR (g!) q
local notation "a!"=> clump k (travelW k p D W) Z
abbrev freightJ (k:ℕ)(p D W C Z d R:ℝ) := clump k (travelW k p D W) Z * (d*gamut R C (2*((k+2)*k))+d^2*d⁻¹)
abbrev tokens (k:ℕ)(p D W C Z R:ℝ) := (clump k (travelW k p D W) Z)*gamut R C ((k+2)*k)
local notation "v!"=> tokens k p D W C Z A
local notation "η*"=> freightJ k p D W C Z d A
abbrev ticket (k n:ℕ)(p D W C Z d A L b:ℝ) := esteem n k Z (fee k p D+W) (tokens k p D W C Z A) (freightJ k p D W C Z d A) b L
abbrev receiptQ (k:ℕ)(p D W Z L:ℝ) := clump k (clump k (fee k p D+W) Z) L
local notation "t"=> ticket k n p D W C Z d A L v
local notation "P"=> Mulberry.cut μ Ω (g!)
local notation "Q"=> clean μ (g!) n
local notation "Q'"=> receiptQ k p D W Z L
include H hn hp hh hK hv hs
lemma bureau (hx:‖x‖<b): let Φ:= sampleLog μ Ω g!; X ≤ Mulberry.cut μ Ω (g!) x ∧ Brush k Q' q⁻¹ Φ x ∧ Brush k t b⁻¹ (Φ-Q) x:=by -- let F shadow macro! remove
   intro f'; have hq:= hp.possible; let u:= q; let x':= std V (q⁻¹) x; have hE : (M 0).PosDef:= (H.gram 0 (norm_zero.trans_lt H.pos)).1
   let F₀:= g!; have hG : Paint Ω k (foldR F₀ q) v (fee k p D+W):= sea H hs hp.tuition hq hp.sane hp.scaledSmall hp.simple
   have ha z:= Mulberry.to_sky H hs hp.tuition hq hp.sane z; have hz i (hi:i≤k):= evacuation H hs hp.tuition hq hp.sane i hi
   have h' {i:ℕ}(hi:i≤ n):= earnings K D hG hp.mad hz ha hE.inv hK hv (hi.trans (by omega)); have hH:‖x'‖<b/q:= (torsion hq _).2 ((show std (ℝ × E) q x'=x from smul_inv_smul₀ hq.ne' _) ▸ hx)
   obtain ⟨he,ht⟩:= Mulberry.rides μ Ω hG measurableSet_closedBall hp.mad hn (hh.trans hp.solvent) (fun _ hi=> h' hi|>.2) (at_nose K D (div_pos H.pos hq) hG hp.mad hz ha hE.inv hK hv hh hn hp.fraction) hp.wheat hp.nature hH
   have hs(z:F): F₀ z 0=0:= by
       have ht:= hG.air z; change F₀ z (std (ℝ×E) q 0)=_ at ht; rwa [map_zero] at ht
   have hD:0<b:= H.pos; refine ⟨?_,?_,?_⟩
   · have hq':= (Mulberry.purchases hG measurableSet_closedBall (by omega) hp.mad (hh.trans hp.solvent) hH).1; rw [cut_scale μ Ω q F₀] at hq'; rw [Function.comp_apply,show std V q x'=x from smul_inv_smul₀ hq.ne' _] at hq'; exact hq'
   · rw [← one_div]; exact rewind_full _ ht hq
   rw [clearLog μ q F₀ n hs ?_] at he; swap
   · intro z; have hY:= reel (F₀ z) ((ha z).smaller (show n≤k by omega)) hq.ne'; rwa [map_zero] at hY
   rw [show b⁻¹=v⁻¹/q from (by field_simp)] -- inversion parse
   exact rewind_full _ he hq
end here
end YM.Juniper.Mulberry
