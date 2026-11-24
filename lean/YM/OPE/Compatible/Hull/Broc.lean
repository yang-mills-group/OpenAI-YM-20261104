import YM.OPE.Compatible.Hull.Knee
import YM.OPE.Compatible.Hull.Nook
import YM.OPE.Compatible.Hull.Spoon
import YM.OPE.Compatible.Hull.Bud
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Source Labels Source.Drops
section
open Beamer
variable {H:Hol G}{θ:ℝ}(P:Pad G)(f:Config G n→ℂ)(t:ℝ) (U:BudgetPoint)(h:2*(b+1)<n.val)(Q:Acceptance o U (k+6) f b θ)(A:ℂ→L[ℝ]ℝ)
variable {d:ℕ} (W:Snap G d)
variable {η:ℝ}
-- η chosen polynomial clock. Mark fee scales D-independent >=0
abbrev θh:= Θrank t U.threshold
noncomputable def θW (P:Pad G)(b j:ℕ) (t:ℝ)(A:ℂ→L[ℝ]ℝ):= ‖A‖*((lights P j).choose)*sizeQ b ^j*t*((strideSize G).choose)^j
lemma νB (ht:0 ≤ t)(x:ℝ): basicT P t b i U A x=θW P b i x A*θh t U ^i:=by unfold basicT θW; rw [Real.norm_of_nonneg (mul_nonneg ht (inv_nonneg.mpr U.threshold_pos.le)),mul_pow]; ring -- unused hyp?
include Q
lemma actualR (hx:i ≤ k+6)(ht:0<t)(hV:KiteB H W U.threshold i b η) (V: OrderedFinpartition i):
       let p:= iteratedFDeriv ℝ V.length (Artifact o P h U f A t) 0
       let Q₁(j):=iteratedDeriv (V.partSize j) (JargonR t U H W b) 0
       let Q₂(j):=Packer G b (Exposure (4*b) (Sie (iteratedDeriv (V.partSize j) (Spindle.flash W) 0)))
       ‖p Q₁-(θh t U)⁻¹ ^ V.length*p Q₂‖ ≤ θW P b V.length θ A * (V.length:ℝ) * η^(V.length-1) * η * U.threshold:=by
          intro p Q₁ Q₂; let Z(j):=iteratedDeriv (V.partSize j) (sprintD H b U.threshold W) 0; let a:= θh t U; have ha:0<a:=mul_pos ht (inv_pos.mpr U.threshold_pos); have hz :Q₁ = a⁻¹ • Z:=by funext j; exact iteratedDeriv_const_smul (hV.smooth.of_le (Nat.cast_le.mpr (V.partSize_le j))) _
          have hh(j):Q₂ j= iteratedDeriv (V.partSize j) (spanT H b W) 0 := (spanI ..).symm; let v:= V.length; have ht₁:= (apriced o P h U f A Q.Shush Q.ready Q.toll ((V.length_le.trans hx).trans Q.guard) t 0); rw [νB P _ U A ht.le _] at ht₁; let D:=θW P b v θ A; let B:=η; have hP:0 ≤ D*a^v:= (norm_nonneg _).trans ht₁; have he:= hV.pos; have hx(h : 0 < v): v-1+1=v:=by omega -- may unused remove
          rw[hz,show p (a⁻¹ • Z)=a⁻¹ ^v*p Z from ?_,← mul_sub]; swap; · simpa using! p.map_smul_univ (fun _=>a⁻¹) Z
          rw [norm_mul,norm_pow,Real.norm_of_nonneg (inv_pos.mpr ha).le]; have hK:max ‖Z‖ ‖Q₂‖ ≤η:= max_le ((pi_norm_le_iff_of_nonneg he).2 (fun j=>hV.bump' _ (V.partSize_le j))) ((pi_norm_le_iff_of_nonneg he).2 (fun j=>by rw [hh]; exact hV.bump _ (V.partSize_le j)))
          have hs:‖Z-Q₂‖≤η*U.threshold:= (pi_norm_le_iff_of_nonneg (mul_nonneg he U.threshold_pos.le)).2 fun j=>by rw [Pi.sub_apply,hh]; exact hV.dif _ (V.partSize_le j)
          have hy:= p.norm_image_sub_le Z Q₂; rw [Fintype.card_fin] at hy; refine le_trans (mul_le_mul_of_nonneg_left (hy.trans (show _≤ D*a^v*v*η^(v-1)*(η*U.threshold) from ?_)) (pow_nonneg (inv_pos.mpr ha).le v)) ?_; exact (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right ht₁ (Nat.cast_nonneg v)) (pow_le_pow_left₀ (by positivity:0 ≤ max ‖Z‖ ‖Q₂‖) hK _) (by positivity) (mul_nonneg hP (Nat.cast_nonneg v))) hs (norm_nonneg _) (mul_nonneg (mul_nonneg hP (Nat.cast_nonneg v)) (pow_nonneg hV.pos _)))
          exact Eq.le (by change a⁻¹ ^ v*(D*a^v*v*η^(v-1)*(η*U.threshold))= D*v*η^(v-1)*η*U.threshold; rw[inv_pow]; field_simp) -- nonzer
variable (R:KernelChoices)(y:Train r) (hr:4 ≤ r)
def nubK (H:Gauge)(B:ℕ)(U:Train r)(K:KernelChoices)(Hn:4 ≤ r)(n:Side):ℝ:= RinB (Fpaper H B) (cookV H U K Hn n B)
abbrev JRead (V:OrderedFinpartition i)(s:Seat (k+6) m (Shade G))(W:Snap G d):= (θh t U)⁻¹ ^ V.length * ((V.length.factorial:ℝ)* wholeX (lilies m (k+6) _ s V.length) (fun j=> Sie (iteratedDeriv (V.partSize j) (Spindle.flash W) 0)))
lemma taxStory (hx: i < k+6)(ht:0<t)(hV:KiteB H W U.threshold i b η)(B:OrderedFinpartition i)(hX:2*(4*b+1)<n.val)(m:ℕ):
     let p:= Recon o P h U f A R y hr t Q; let q:= boostS (rentV G y hr R n) (1/2) m (k+6) (Locket p m).val
     let S:= Artifact o P h U f A t; let v:=B.length
     let Z(j):= iteratedDeriv (B.partSize j) (JargonR t U H W b) 0
     ‖iteratedFDeriv ℝ v S 0 Z-JRead t U (m:=m) B q W‖ ≤ θW P b v θ A * v * η^(v-1)*η*U.threshold + θW P b (v+1) θ A * θh t U * η^v * nubK G b y R hr n :=by
            intro p q S v Z; let F:= Vessel R y G n hr; let K:=Cane G b o; let μ':Measure (Bid.Dir G n):=Measure.addHaar; let g:=fun j=> Sie (iteratedDeriv (B.partSize j) (Spindle.flash W) 0); let V(j):=Packer G b (Exposure _ (g j)); let a:=θh t U; have ha:0<a:=mul_pos ht (inv_pos.mpr U.threshold_pos); have hb: v < k+6:= Nat.lt_of_le_of_lt B.length_le hx; have hp: Stature S (k+6):=impeccable o P h U f A Q t; let φ:=iteratedFDeriv ℝ v S 0; let c:=cookV G y R hr n b; let d:=θW P b (v+1) θ A; let e:=a⁻¹^v; have hl:0 ≤ e:=pow_nonneg (inv_pos.mpr ha).le v
            have hv:JRead t U (m:=m) B q W =e*taxA F μ' K S V:=by
                 apply congr_arg (e*·); rw [DawnH o P h U f A R y hr Q t g hX hb.le m,← _root_.mul_assoc,mul_inv_cancel₀ (show (v.factorial:ℝ)≠0 from by positivity),one_mul]
            rw [hv]; change ‖φ Z-e*taxA F μ' K S V‖≤ _; refine (norm_sub_le_norm_sub_add_norm_sub (φ Z) (e*φ V) _).trans (add_le_add (actualR o P f t U h Q A W hx.le ht hV B) ?_)
            rw [←mul_sub,norm_mul,Real.norm_of_nonneg hl]; have hU(x):‖iteratedFDeriv ℝ (v+1) S x‖ ≤ d*a^(v+1):=(apriced o P h U f A Q.Shush Q.ready Q.toll (hb.trans_le Q.guard) t x).trans_eq (νB P _ _ A ht.le _); have hθ:0 ≤ nubK G b y R hr n:=by
                 have hu:0≤c:=by unfold c cookV; exact mul_nonneg (mul_nonneg (rentV G y hr R n).positive (sq_nonneg _)) (sq_nonneg _)
                 unfold nubK RinB; change 0 ≤ 1+_*c; positivity
            apply (mul_le_mul_of_nonneg_left (RisRR F (Measure.addHaar) K hp hb (fun i=> avenue o y R hr b i i) V hU) hl).trans; have he: ∏ j,‖V j‖ ≤ η^v:=by
                   refine (Finset.prod_le_prod (fun i _=> norm_nonneg _) (g:=fun _=>η) (fun i _=>?_)).trans_eq ?_; swap; · simp [v]
                   rw [show V i= _ from (show V i=iteratedDeriv (B.partSize i) (spanT H b W) 0 from (spanI ..).symm)]; exact hV.bump _ (B.partSize_le i)
            exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he ((norm_nonneg _).trans (hU 0))) hθ) hl).trans_eq (by change e*(d*a^(v+1)* _* _)=d*a*_*_; unfold e; rw [inv_pow,pow_succ a]; field_simp)
end
end YM.OPE.Spells
