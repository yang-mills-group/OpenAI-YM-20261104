import YM.MSbar.Jade.Polka
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Jade
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
variable {G:Gauge}{c f:Side} {S:StepData c f}(F:Forest S.ratio)(R:Rep G f)(v:S.Choices)(J:Voice G)(Q:Palisade)(χ:ChartRatio G)
local notation "V"=>Primary c G
local notation "P"=>Key F G
local notation "G!"=>Joint F G
local notation "T"=>Positions (Joint F G)
local notation "x!"=> Positions (Primary c G)
local notation "Ω"=> address F G
open Kelvin Next.SectorChange
variable (X Y: Support f)
variable (x y:Positions (Joint F G)) (W:Finset (Joint F G))
variable (h:S.patch.Branches S.kernel G)
variable {a b B D A K t E:ℝ}{d p:ℕ}(hp: t*A < a)(hh:0<t)(hx:‖x‖≤ A)(hy:‖y‖ ≤ A)
variable (hf:∀ i∈ Finset.univ\W,x i= y i)
include h hp hh hx hy hf
local notation "u!"=> pushChart F G v
lemma eaves (p:ℕ) {s:ℝ}(hr:p+2+1 ≤ d) (hA: s=t⁻¹^2) (hS:∀ i:Bond c,∀ x :Positions (Joint F G),‖x‖ < a→ Allows d (arch F v i) x B) : let H:= singularity (pushChart F G v) 2
   |(-s* pushChart F G v (t • x) - (-s*pushChart F G v (t • y))) + (taste p (picture x H) t -taste p (picture y H) t)| ≤ W.card * cities 4 (noiseCost S.patch) * (2* B * A^(2+p+1)) * t^(p+1) :=by
    intro H; let L(i:Bond c) := curbL (Ω) (S.ratio.embed i.1) (noiseCost S.patch); have ht' : Premier u!:=(bornCosts v h).line (relayB F G); let A':= W.card*cities 4 (noiseCost S.patch); have hV: (farQ W L).card ≤ A':= allowance W (S.ratio.embed ∘ Prod.fst) (Ω) (noiseCost S.patch) (flagC S.ratio Prod.fst (powerP c Axis)); have hₓ(v:T)(h:‖v‖≤A):‖t •v‖≤t*A:=by rw [norm_smul,Real.norm_of_nonneg hh.le]; exact mul_le_mul_of_nonneg_left h hh.le
    let b:= blockTaylor (2+p) u!; have hz:= rays_p (U:=Parma.arch (G:=G) F v) L W (fun i=>_root_.funext fun k=>behove F v i k h) (2+p) (by omega) hS (hₓ x hx) (hₓ y hy) hp (fun i hi=> congr_arg (t*·) (hf _ hi)) (Eventually.of_forall (fun x=>robe F v x)) (robe F v _) (robe F v _); have ht(x:T):b (t•x)= t^2*taste p (picture x H) t:= by unfold b; rw [← drives,Rolling.lens 2 p u! (fun i hi x=> ht'.zeroP i x hi)]; -- binder
    have hA':0≤B:=(hS (Classical.arbitrary (Bond c)) _ (lt_of_le_of_lt (hₓ x hx) hp)).nonneg; have hB':0≤ s:= hA ▸ sq_nonneg _
    rw [show _+_= -s*((u! (t•x)-u! (t•y))-(b (t•x)-b (t•y))) from (by rw [ht,ht,hA]; field_simp;ring), abs_mul,abs_neg,abs_of_nonneg hB']; refine (mul_le_mul_of_nonneg_left hz hB').trans ?_; have h₂: 0 ≤ A:= (norm_nonneg _).trans hx; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show ((farQ W L).card:ℝ) ≤ A' by exact_mod_cast hV) (by positivity : 0 ≤ 2*B*(t*A)^(2+p+1))) hB').trans_eq; rw [hA]; norm_cast; rw [mul_pow t]; unfold A';rw [show t^(2+p+1)= t^2*t^(p+1) from (by ring)]; field_simp -- avoid cast
-- signal W reader.T.need sum equality on actual x.Gamma.pr.
omit hp h hh hx hy hf
lemma benign (x:F.Free)(z:T):signal F x χ (haul _ (curbL (address F G) x.val.1 0) z)=signal F x χ z:=by unfold signal Function.comp; refine congr_arg _ ?_; ext i; change (if _ then _ else _) = _; apply if_pos; simp [curbL,address]
lemma invoice (x:T)(h:LocalRatio χ)(g: ∀ i : F.Free, cord F i G x∈ Metric.ball 0 χ.radius): swung F χ x=∑ i:F.Free, signal F i χ x:=by
    unfold swung capitalJ pay signal smelt; simp only [Function.comp_apply,Finset.sum_sub_distrib]; change Real.log _ - Real.log (∏ i:F.Free, χ.scale*χ.J _) = _; rw [Real.log_prod (fun x _=> ?_), Real.log_prod (fun x _=>?_)]; rfl; exact (mul_pos h.scale (h.pos 0 (Metric.mem_ball_self h.patch))).ne'; exact (mul_pos h.scale (h.pos _ (g _))).ne'
include hp hh hx hy hf
variable (hχ:LocalRatio χ)
include hχ
lemma curled (p:ℕ)(he: p+1≤d)(h1:∀ i:F.Free, cord F i G (t•x)∈ Metric.ball 0 χ.radius)(h2:∀ i:F.Free,cord F i G (t•y) ∈ Metric.ball 0 χ.radius)(ha:∀ i:F.Free,∀ x:T,‖x‖<a → Allows d (signal F i χ) x B)(hB:0 ≤ B): let H:= singularity (swung F χ) 0
    |(swung F χ (t • x)-swung F χ (t •y)) -(taste p (picture x H) t-taste p (picture y H) t)| ≤ W.card*cities 4 0*(2*B*A^(p+1))*t^(p+1) :=by
    intro H; let L(i:F.Free):=curbL (Ω) i.val.1 0; have hₓ(v:T)(h:‖v‖≤A):‖t •v‖≤t*A:=by rw [norm_smul,Real.norm_of_nonneg hh.le]; exact mul_le_mul_of_nonneg_left h hh.le
    let v(i:F.Free):=i.val.1; have hP:(farQ W L).card ≤ W.card*cities 4 0:= allowance W v (Ω) 0 ((powerP f Axis).comp (f:=fun (x:F.Free)=>x.val) Subtype.val_injective); have hA:0 ≤ A:=(norm_nonneg _).trans hx
    unfold H; rw [drives,drives]; apply (rays_p (U:=fun x:F.Free=>signal F x χ) L W (fun i=>_root_.funext fun z=> benign F χ i z) p he ha (hₓ x hx) (hₓ y hy) hp (fun i hi=> congr_arg (t*·) (hf i hi)) (sting F χ hχ) (invoice F χ _ hχ h1) (invoice F χ _ hχ h2)).trans; refine (mul_le_mul_of_nonneg_right (show ((farQ W L).card:ℝ) ≤ ↑(W.card*cities 4 0) by exact_mod_cast hP) ?_).trans_eq ?_; · positivity
    rw [mul_pow t A _]; push_cast;ring -- card cast issue
end YM.MSbar.Jade
