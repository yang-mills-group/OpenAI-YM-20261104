import YM.AllOrder.Plateau.Prism
import YM.AllOrder.Plateau.Work
/-!
# Fiscal toll warp. Fixed any Step Patch; `region._` finite context proofs late. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ}
local notation "E"=>Positions (Primary n G)
section know
open Kinetic.Port
variable (P:Patch)(K:KernelChoices){a Λ:ℝ}
local notation "S[" n "]"=> dock P K n
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(U: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (U i))
    (hO:LocalRatio O)
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
variable {R:ℕ→ι→Ink.Field (Coarse G)} {T : Repertoire ι G}
local notation "𝒜"=> Area ι
variable (H : Presence P K p O x U Q hx hO F h R)(H₀:Canopy P K p O x U Q hx hO F h U R H)
    (B : BillBoard U T N) (v:ℕ) {D:ℝ→ℝ} {e:ℝ}
set_option quotPrecheck false
local notation "L"=>P.L
local notation "ℍ"=> Claim G P.L (region G P.L v U)
local notation "g"=> (fun i: 𝒜=> gStep i.2.2)
local notation "Δ"=>Plateau.chopWind P K p O x U Q hx hO F h H H₀
local notation "Θ"=>Plateau.chopCut U B
variable (hD:Rate G P.L 0 D) (hk:k≤N)
include hk hD
lemma corner_wind (t:ℝ) (k':ℕ) : ℍ t (fun x i=> Δ i.1 k' k (g i) (D x) i.2.1):= by
 let Λ:= (region G P.L v U); let h:Claim G P.L Λ (1/2:ℝ) (fun _ i=>1+(g i)⁻¹):= (Claim.weaken (Claim.eve_path 1) (by norm_num)).add (reverse_area G P.L U v);
 unfold Plateau.chopWind; apply Claim.sprocket; intro i hi; have hi:= Finset.mem_range.mp hi; have ht:= H₀.forms i (by omega); have hf:= (Pay.area G P.L U v ht.story).mul (dearth_area G P.L U v _ ht.berth (t - (↑(i+2):ℝ))); unfold Lapis.tollS; refine (((beta_area G P.L U v|>.power i).mul (((Claim.hires hD|>.power k').mul (((hf.mul (h.power (i+2))).r_scale (Rail.mantle k' (i+2))).r_scale _)))).r_scale 2).weaken ?_; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) i]
open Shop
omit hD hk in
lemma ratio_rate (k' w:ℕ): ℍ (((w:ℝ)-(k':ℝ))/2) (fun _ z=> ratioW (g z) k' w):= by
   simp only [ratioW,← inv_pow]; exact ((Claim.power (beta_area G P.L U v) k').mul ((Claim.power (reverse_area G P.L U v) w))).weaken (by push_cast; linarith)
local notation "ω₁" => air N
local notation "Y₀" => (fun x:ℝ=> betaF G x P.L ^ ω₁)
def omegaL (I k:ℕ):= 1+air I * (k+3:ℕ)
omit hD
omit hk in
lemma earns (hk:k≤N) : Shop.output k (edgeW N) > omegaL N k:= by
 let i:= (4+(N:ℝ)); let e:=edgeW N; have hp := edge_pp N; have hi: 0< i:=by unfold i; positivity
 have he: (e/i)*(k+3:ℕ) < e:=by
   have hv: ((i:ℝ))*(e/i)=e:=by field_simp
   have hk': (↑(k+3):ℝ) < i:= by unfold i; push_cast; linarith [Nat.cast_le (α:=ℝ)|>.mpr hk]
   have he': 0<e/i:=div_pos hp hi; nlinarith only [mul_lt_mul_of_pos_left hk' he',hv]
 unfold Shop.output omegaL air; unfold e i at he; push_cast at he ⊢; linarith only [he]
include hD
lemma corner_cut (j:ℕ)(Z:ℝ): ℍ (omegaL N k) (fun x i=> Θ i.1 j k (g i) (D x) Z (Y₀ x) (radiusB x)) := by
 unfold chopCut; apply Claim.sprocket; intro l hl; apply Claim.sprocket; intro r _; have hv :l ≤ k:= by rw [mem_range] at hl; omega
 obtain ⟨hz,h'⟩:= B.birth l (by omega) r; let u:= r.val+2; have h : u ≤ l+2 := by have ht:= r.isLt; unfold u; omega
 let hp:= Grade.area G P.L U v h'.1; let t:= air N * (k-l+u+1:ℕ); let ht:= Claim.power (Claim.hires (G:=G) («L»:=P.L) (A:=region G P.L v U) (Rate.power (a:=air N))) (k-l+u+1); let hx:= Claim.hires (A:=region G P.L v U) (dearth_rate G P.L _ (half_pos hz) t)
 let D':=fun x=> (D x)^j; let H : ℍ 0 (fun x _=> D' x):= ((Claim.hires hD).power j).weaken (by simp)
 let s (x:ℝ)(z:𝒜):= shin G (B.air l r) (B.fee l r z.1) (D x) Z (Y₀ x) j u k l (radiusB x); have hT: ℍ t s:= by
    unfold s shin tollS; exact Claim.add (Claim.weaken ((((H.mul (hp.r_scale _)).r_scale 2)).mul ht) (by simp [t])) ((Claim.r_scale (H.mul ((hx.mul hp).r_scale _)) _).weaken (by simp))
 refine ((ratio_rate (G:=G) P U v l u).mul hT).weaken ?_
 let n':=(k-l:ℕ); have hN: (n':ℝ)= (k:ℝ)-l := Nat.cast_sub hv; let a:=air N; have ha:= buys_air N|>.1; have hb: (((u:ℝ)-(l:ℝ))/2+a* ((k:ℝ)-(l:ℝ)+u+1)) ≤ 1+a*((k:ℝ)+3):=by
    nlinarith [mul_nonneg (show 0≤a+1/2 from (by unfold a; linarith)) (show 0≤ (l:ℝ)+2-u from (by exact sub_nonneg.mpr (by exact_mod_cast h)))]
 unfold omegaL; dsimp only [t]; push_cast; rw [Nat.cast_sub hv]; exact hb
variable (q:Clip)(α x': ι→ℝ)(hα:Grade U (fun x=> |α x|))(hx':Grade U x')
    (B':BareRates.pre G σ Z j)
include hx' hα
lemma corner_local : ℍ (omegaL N k) (fun x i=> i.2.2 * (edges B' q (D x) (x' i.1) (α i.1) (Y₀ x) k).1 + (edges B' q (D x) (x' i.1) (α i.1) (Y₀ x) k).2):= by
 let h:= Claim.hires (G:=G) («L»:=P.L) (A:=region G P.L v U) (Rate.power (a:=air N)); -- binder x untyped
 let a:=Grade.area G P.L U v hα; let b:= Grade.area G P.L U v hx'; let H: ℍ 0 (fun x _=> D x^j):= ((Claim.hires hD).power j).weaken (by simp); unfold edges tollS; apply Claim.add ;
 · exact ((hats G P.L U v).mul (((H.r_scale (BareRates.bill B' q)).r_scale 2).mul (h.power _))).weaken (by unfold omegaL; simp)
 exact (((H.mul ((((Claim.eve_path 1).add a).add b).r_scale (BareRates.bill B' q))).r_scale 2).mul (h.power _)).weaken (by unfold omegaL; push_cast; have hh:= buys_air N|>.1; linarith only [hh])
end know
end YM.AllOrder.Plateau
