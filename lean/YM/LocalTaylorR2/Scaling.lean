import YM.LocalTaylorR2.License
import YM.LocalTaylorR2.Curriculum
/-!
# Numeric spending before the step

No absolute-stage constants suppressed for the actual path. `Rate` used
ONLY to justify pre-step decisions. ζ is a reserve set by perturbative
order. Positive allowance ε is arbitrary. No weakening a post-Support rate
in the application to actual E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves RG01.Survive PhysicalNext.Repeat
open Charge Candle Tender AnalyticBridge VerifiedReset
namespace Tail
variable {θ ν t e ζ:ℝ} {b r w D x : ℝ→ℝ}
lemma meters (W:ℝ→ℝ) (h:Rate G L t W) (u:ℝ): Rate G L t (fun x=> degreePrice (radiusB x) (W x) u):= by
  unfold degreePrice stretch; have he:=Census.width_rate G L 1 0; simp only [one_mul,add_zero] at he; simp_rw [div_eq_mul_inv]
  simpa only [zero_add] using! (((he.mul h).mul_right _).mul_left _)

lemma marked (Q: YM.ConnectedActivityE6.Target G P) (hm:0<μ) (ζ:ℝ): ∀ᶠ x:ℝ in atTop, betaF G x L^ζ ≤ Real.exp (Q.mark L μ x) := by
  have hf : Rate G L (-ζ-1) (fun x=> Real.exp (-Q.mark L μ x)) := by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x
    dsimp only; rw [Real.rpow_two]; change Real.exp (- Delay.hatWin G L _ _ x)=_; unfold Delay.hatWin; congr 1; ring
  filter_upwards [((Rate.power (a:=ζ)).mul hf).below (by linarith) 1 zero_lt_one] with x h
  apply (div_le_one (Real.exp_pos _)).1; rw [div_eq_mul_inv, ← Real.exp_neg]; exact (le_abs_self _).trans h

lemma incline (f:ℝ→ℝ)(l:ℕ)(Hf:Rate G L e f) (hb:Rate G L t b) (hm:0<μ) (hv:e+t≤ν) (he:Q.rate≤ν) :
    Rate G L ν (fun x=> massb Q L μ x θ (f x) l (b x)) :=
  ((Q.rate_root (β:=1) (C:=0) _ hm).weaken he).add (((Hf.mul_left _).mul hb).weaken hv)
lemma tangent (D B b x r f : ℝ→ℝ)(l n j:ℕ)(Hf:Rate G L e f) (hb:Rate G L t b) (hm:0<μ) (hv:e+t ≤ ν) (he:Q.rate≤ν)
    (hD:Rate G L 0 D)(hB:Rate G L 0 B)(hx:Rate G L 0 x)(hr:Rate G L 0 r):
    Rate G L ν (fun s=> Price.secondQ Q L μ s θ (f s) (D s) (x s) (B s) (r s) (b s) l n j):=by
  let k s:= Price.slope (D s) (x s) (B s) (r s) l j
  have hk : Rate G L 0 k:= by
    apply hB.add
    have hs : Rate G L 0 (fun s=> 1+D s+2*r s*(l+3:ℝ)):= ((Rate.const (G:=G) 1).add hD).add ((hr.mul_left 2).mul_right _)
    simpa only [zero_mul,zero_add] using! hx.mul (hs.pow j)
  have hh := incline (θ:=θ) f l Hf hb hm hv he
  unfold Price.secondQ treeYield; simp only [pow_zero,mul_one]; simpa only [zero_add] using! ((hk.mul ((hh.mul_right _).mul_left _)).mul_left (2^j)) -- underscores ambiguous

-- read-price measure even in worst budget chart selected.
def report (G:Gauge)(j n:ℕ)(δ s w u ρ:ℝ)(k:ℕ):ℝ:=u*((ρ^k)⁻¹*(collars G δ s j n*(w*(1-1/2)⁻¹)))
lemma height (G:Gauge) (l j n:ℕ) (θ e δ α:ℝ) : Rate G L (-e*l+α) (fun x => report G j n δ x (betaF G x L^α) θ (betaF G x L^e) l):= by
  have hf:Rate G L (-e*l) (fun x=> ((betaF G x L^e)^l:ℝ)⁻¹):= by
    apply Rate.congr Rate.power
    filter_upwards [Delay.shift_pos G L] with x hx
    rw [← Real.rpow_mul_natCast hx.le e l,neg_mul,Real.rpow_neg hx.le]
  have he : Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
  have hp : Rate G L 0 (fun x=>collars G δ x j n):=by simpa only [zero_mul] using! ((he.pow (n*j)).mul_right (Reserves.polyPrice δ (n*j)))
  unfold report; simpa only [zero_add] using! ((hf.mul (hp.mul ((Rate.power (a:=α)).mul_right _))).mul_left θ)

abbrev requested (k:ℕ)(ε:ℝ) := -(k:ℝ)/2+ε/2
lemma plan (l:ℕ) (ε:ℝ) (hε:0<ε): ∃ e:ℝ, 0<e ∧ e<1/2 ∧ ∀ i:ℕ, i≤l+1 → -e*i < requested i ε:= by
  let δ:= min (ε/(2*(l+1:ℝ))) (1/8)
  have hδ:0<δ:=lt_min (by positivity) (by norm_num)
  obtain ⟨e,he,hE⟩:= exists_between (show 1/2-δ<1/2 by linarith)
  refine ⟨e,(by linarith only [min_le_right (ε/(2*(l+1:ℝ))) (show ℝ from 1/8),he]),hE,fun i hi=> ?_⟩
  unfold requested
  have hv: (1/2-e)*(l+1)<δ*(l+1):=mul_lt_mul_of_pos_right (by linarith) (by positivity)
  have hp:δ*(l+1) ≤ ε/2:= by refine (mul_le_mul_of_nonneg_right (min_le_left ..) (show (0:ℝ)≤l+1 by positivity)).trans ?_; apply le_of_eq; field_simp
  have h : (i:ℝ)≤l+1:= by exact_mod_cast hi
  nlinarith only [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hE.le),hv,hp]
end Tail
end YM.LocalTaylorR2
