import YM.AllOrder.Plateau.Clarity
/-!
# Whole real cost of a tall `salary`-path ticket. Early ages truly zero pieces;
not secretly permitting sizeable E in early budgets. Later pure estimates.
-/
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
section pearl
variable (A:Packet G k) {a C g y D :ℝ}(ha:0<a)(hb:SumBudget (fun i=>(A i).budget a) C)
    (hk:0<k) (p j:ℕ)
local notation "L"=>Kinetic.Port.exteriorL G n
include ha hb
lemma staid (p:ℕ) (hp:p<k): iteratedFDeriv ℝ p (speak A n) 0=0:= by
 rw [sail_back]; let F:=turnSeries A (m:=n); have he:= turns_analytic (m:=n) A ha hb; let l: E→L[ℝ] Link G n:= (Kinetic.Port.exteriorL G n).symm.toContinuousLinearMap; change iteratedFDeriv _ p (F ∘ l) _=_; rw [Next.Foundations.jets_linear _ (he.contDiffAt.of_le le_top), (rays_jet he k).1 (turns_low _ ha hb) p hp]; ext1 x; rfl
local notation "Ψ"=> speak (crop w ∘ A) n
lemma staid_zero (h:0<k): speak A n 0=0:= by rw [← norm_eq_zero,← norm_iteratedFDeriv_zero (𝕜:=ℝ), staid A ha hb 0 h]; exact norm_zero
variable (hA:PaintSupply G j Z)(h: k ≤ j)(hg:0<g) (hy:0<y)(hr:y≤1)(ht:1≤D)(hh:(Fintype.card (Primary n G):ℝ)≤D)
local notation "U"=> tollS D j (C*Plateau.amt G k j a Z)*2
include hk hA h hg hy hr ht hh
lemma stay (x:E)(hx:‖x‖<y) : Brush j (ratioW g p k*((U)*y^k)) y⁻¹ (ratioW g p k • Ψ) x:= by
 let f := crop w ∘ A; have h₀:=staid_zero (n:=n) f ha (sold A ha hb w) hk; have h1(z:E)(hz:z ∈ ball 0 y) : Brush j (U) 1 (speak f n) z := by
    have hv:=speaking f ha (sold A ha hb w) hA (by omega) ht hh z ((ball_subset_ball hr) hz); rw [Shellac.off,h₀,show (fun _ : Positions (Primary n G)=> (0:ℝ))=0 from rfl,sub_zero] at hv; exact hv
 let z:E:=0; have he0(r:ℕ)(hex:r<k) : normJ r (speak f n) 0*y^r≤0:= by unfold normJ; rw [staid f ha (sold A ha hb w) r hex,norm_zero,zero_mul];
 have ht:= Shellac.pools hy hr h ((h1 z (mem_ball_self hy)).nonneg) (b:=0) le_rfl (fun i he=>(h1 i he).smooth) (fun i _ ht z hz=> (Brush.offer.1 (h1 z hz)).inside _ ht) he0 x (mem_ball_zero_iff.mpr hx); rw [mul_zero,add_zero] at ht; rw (occs:=.pos [1]) [← Real.norm_of_nonneg (ratioW_pos p k hg|>.le)]; exact ht.smul _
end pearl
open Kinetic.Port
lemma vacantCrop {ι:Type} (w k:ℕ) (i:Fin (k+1))(j:ι)(t:Positions (Primary n G)) : speak (crop w ∘ (unpop ι G k i j)) n t=0:= by
 let U:= unpop ι G k i j; unfold speak Stationary.orbitRaw Precision.uncut Patch.average; have he(q U'):∀ (u:Site n), (crop w (U q)).unmasked U' u= 0:= by
     intro i'; unfold crop; split; unfold U; simp [unpop,Stationary.issue,Stationary.artery,Atom.unmasked,Atom.poly]; simp
 unfold U at he; simp_rw [Function.comp_apply,he] -- unfold U stuck
 simp
section sake
variable {V:Type} [Nonempty V] (U : V→ℝ){f:Repertoire V G}(A:BillBoard U f N) (ht:∀ i<3,f i=unpop V G i)
    {Ω y:ℝ} (hΩ:1≤Ω)(hQ:(Fintype.card (Primary n G):ℝ)≤Ω) (hY:0<y)(hp:y≤1)
    (hZ:PaintSupply G j Z) (hk:k≤N)

abbrev scalp (G:Gauge)(p A D Z y b:ℝ)(l k j:ℕ):= ratioW b l k * (tollS D j (A*Plateau.amt G k j p Z)*2*y^k)
def pick (i:V)(W' k j:ℕ) (p D y b:ℝ) := ∑ l∈ Finset.range (k+1),∑ r:Fin (l+1), if 3≤l then scalp G (A.air l r) (A.fee l r i) D p y b l (r.val+2) j else 0
include A hk ht hZ hΩ hQ hY hp
lemma saliva (v:V)(i:E) (he:k+2≤ j)(hb:0<β)(hi:‖i‖<y): Brush j (pick U A v w k j Z Ω y β) y⁻¹ (peal f v β w k n) i:= by
 unfold pick peal; refine Brush.spree _ _ _ (inv_pos.mpr hY).le (fun l hl=> Brush.spree _ _ _ (inv_pos.mpr hY).le (fun r hr=> ?_));
 let c:= (A.air l r); let d:= A.fee l r v; let p:= ratioW β l (r.val+2); have hh:= Finset.mem_range.mp hl; obtain ⟨h₁,h₂⟩:= A.birth l (by omega) r
 change Brush j (if _ then _ else _) _ _ i; split; next hz => exact stay (f l r v) h₁ (h₂.2 v|>.1) (by omega) l j hZ (by have hh:=r.isLt; omega) hb hY hp hΩ hQ _ hi
 next hz =>
    have hg:= ht l (by omega); let S':= speak (crop w ∘ f l r v) n; let H₁:∀ x',S' x'=0:=fun i=> by unfold S'; rw [hg]; exact vacantCrop .. -- z dependent
    -- inspect lambdas
    change Brush j (0:ℝ) _ (fun x'=>p*S' x') i; simp_rw [H₁,mul_zero]; simpa only [norm_zero] using! Brush.certified (x:=i) (k:=j) (inv_nonneg.mpr hY.le) (0:ℝ)
omit ht hZ hΩ hQ hY hp
include A hk in
lemma peal_zero (v:V)(b:ℝ) : peal f v b w k n 0=0:= by
 unfold peal; apply Finset.sum_eq_zero; intro l hl; apply Finset.sum_eq_zero; intro r _; have he:= mem_range.mp hl; obtain ⟨h₁,h₂⟩:= A.birth l (by omega) r; rw [staid_zero (crop w ∘ f l r v) h₁ (sold _ h₁ (h₂.2 v|>.1) w) (by omega),mul_zero]
variable (P:Patch) (p:ℕ) (f₀:ℝ→ℝ)
local notation "ℍ"=>Claim G P.L (region G P.L p U)
open Shop
set_option quotPrecheck false
local notation "Y₀"=> (fun x:ℝ=>betaF G x P.L ^ (Shop.air N))
-- can combine hp w.Does produce enough β slack?
-- omegaL N 2=1+air*5=−1.5+δ*5. use `Shop.output 2 (edgeW N)`, true k all incl k=2 not θ high. 
include hk
lemma price_phase (hF:Rate G P.L 0 f₀) (h:2≤N)(Z:ℝ)(j:ℕ): ℍ (Shop.output 2 (edgeW N)) (fun x i=>pick U A i.1 (radiusB x) k j Z (f₀ x) (Y₀ x) (gStep i.2.2)):= by
 unfold pick; apply Claim.sprocket; intro l hl; apply Claim.sprocket; intro r _; by_cases h':3≤l
 ·  simp_rw [if_pos h']
    have he:= mem_range.mp hl; let s:= r.val+2; have hS:s≤l+2:=by have h:=r.isLt; unfold s; omega
    let c:= A.air l r; let d:= A.fee l r; let H:=Claim.hires (A:=region G P.L p U) (Rate.power (G:=G) (L:=P.L) (a:=air N)); let a:=edgeW N; let b:=4+(N:ℝ); have hv:0<a/b:=div_pos (edge_pp N) (by unfold b; positivity); let hs:= Grade.area G P.L U p (f:=d) (A.birth l (by omega) r|>.2.1)
    unfold scalp tollS; have hT (y:ℕ): ℍ ((↑s-(l:ℝ))/2+ Shop.air N * s) (fun x i=> ratioW (gStep i.2.2) l s* ((f₀ x)^j * (d i.1 * Plateau.amt G s j c Z)*2*(Y₀ x)^s)):= by
       exact ((ratio_rate P U p l s).mul (((((Claim.hires hF).power j).mul (hs.r_scale _)).r_scale _).mul (H.power _))).weaken (by simp)
    have hr:(s:ℝ)<b:=by unfold b; have H:= Nat.cast_le (α:=ℝ)|>.mpr (show s≤ N+2 from (by omega)); push_cast at H; linarith
    refine (hT 0).weaken ?_; unfold Shop.output Shop.air; have hh:b*(a/b)=a:=by have h:0 < b:= (by unfold b; positivity); field_simp
    dsimp only [b,a] at hr hv hh; push_cast; nlinarith only [mul_lt_mul_of_pos_right hr hv,hh,show (3:ℝ)≤l by exact_mod_cast h']
 · simp_rw [if_neg h']; exact Claim.zeroC _
end sake
end YM.AllOrder.Plateau
