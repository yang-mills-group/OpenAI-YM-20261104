import YM.XSpace.Fore

/-!
# Uniform plate local sums

`Issued` buys at least zeroth derivative inner integral, eventual ordinary
absolute convergence (ℂ finite-dimensional, not ℕ→ oscillatory).
`Safety` handles enough horizon room for the Taylor currency on lattice data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Shade
open MeasureTheory Function Set Filter Future Lattice Scale Sail Further.FreeCovariance.KP Drama Lows Litter
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {ι:Type} {L:Filter ι}{d:ℕ} {a:ι→ℝ}
abbrev Cut := ContDiffBump (0:E4)
open Playpen
lemma size_actual {b:ℝ}(h:0<b)(x:Cover): b*reach x ≤ ‖actual b x‖ ∧ ‖actual b x‖≤2*b*reach x:=by
  unfold actual; rw [norm_smul,Real.norm_of_nonneg h.le]; constructor
  · gcongr; exact (west ..).1
  rw [mul_comm (2:ℝ) b,mul_assoc]; gcongr; exact (west ..).2
variable (c:Cut)
def pace (b:ℝ)(x:Cover):ℂ:= if 0<b then (↑(c (actual b x)):ℂ) else 0
lemma pace_le (b:ℝ)(x:Cover): ‖pace c b x‖≤1:=by unfold pace; split; rw [Complex.norm_real,Real.norm_of_nonneg c.nonneg]; exact c.le_one; simp
lemma tag (b:ℝ)(x:Cover)(h: pace c b x≠0): 0<b∧ ‖actual b x‖<c.rOut :=by unfold pace at h; split at h; rename_i H; refine ⟨H,lt_of_not_ge (fun hh=> h ?_)⟩; rw [c.zero_of_le_dist (by simpa using hh),Complex.ofReal_zero]; contradiction
lemma cent (b:ℝ)(x:Cover)(h: pace c b x≠0): b*reach x< c.rOut:= ((size_actual (tag _ _ _ h).1 x).1).trans_lt (tag c _ _ h).2
lemma cut_inside (c:Cut)(x:Cover)(b:ℝ)(h:0<b)(ht:‖actual b x‖≤ c.rIn): pace c b x=1:=by rw [pace,if_pos h,c.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using ht),Complex.ofReal_one]
def outfit (b:ℝ): Cover →₀ ℂ:= Finsupp.ofSupportFinite (pace c b) (by
  refine (Finset.finite_toSet (box ⌈c.rOut / b⌉₊)).subset fun i hi=> ?_; change i∈box _; rw [box_rate]; have h:=tag c _ _ hi; have hx:(reach i:ℝ)≤ c.rOut / b:=(le_div_iff₀ h.1).2 (le_of_lt (mul_comm b ((reach i:ℕ):ℝ) ▸ cent c _ _ hi)); exact_mod_cast hx.trans (Nat.le_ceil _) )
lemma outfit_eq (b:ℝ)(x:Cover):outfit c b x=pace c b x:=by change Finsupp.ofSupportFinite _ _ x=_; rw [Finsupp.ofSupportFinite_coe]

def Safety (r:ι→ℕ)(L:Filter ι)(a:ι→ℝ):Prop := ∃ b:ℝ,c.rOut<b∧∀ᶠ i in L,b ≤ a i*r i
variable {r:ι→ℕ}{X:ι→ Trace.Contact G}
variable (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
include he S in
lemma legal (u:E4): Tendsto (fun i=> pace c (a i) (mark (a i) u)) L (𝓝 (↑(c u):ℂ)):= (Complex.continuous_ofReal.continuousAt.tendsto.comp (c.continuous.continuousAt.tendsto.comp (marks u S he))).congr' (he.mono fun i hi=> (if_pos hi).symm)
include he S in
lemma allows (p:Safety c r L a)(n:ℕ) : ∀ᶠ i in L,∀ x, pace c (a i) x≠0→ reach x+n≤r i ∧ a i*area x≤ c.rOut+1:=by
  obtain ⟨b,hb,H⟩:=p; filter_upwards [he,H, (S.mul_const (n:ℝ)).eventually (gt_mem_nhds (show 0*(↑n:ℝ) < b-c.rOut by linarith)), S.eventually (ge_mem_nhds zero_lt_one)] with i hi hh hp hz x hx; have hw:= cent c _ _ hx; refine ⟨?_,?_⟩; swap; · unfold area; linarith
  have hs: (reach x:ℝ)+n ≤ r i:= (mul_le_mul_iff_right₀ hi).mp (by linarith); exact_mod_cast hs
-- kernel point almost everywhere convergence uses actual target-assumed inputs: `Sees` only through ball support, including boundary

variable [L.IsCountablyGenerated] {k d Bn:ℕ}
open Mu MvPolynomial Future
variable (B:ι→Hat G d) (K:Studio L a r X) (P:Tile G)
private def review (i:ι)(A:ι→Trace.Contact G)(x:Cover):ℂ:= tick a i d* pace c (a i) x*Remainder P A B a i x
include he S K
lemma sum_lesson (h:Book G (d+4) P) (hb: Safety c r L a)(p: Likely L B)(HH:∀ᶠ i in L,orchestra d (a i) (B i)= gather d (X i)) (h₀:Sees L a (fun _=>0) X)(Ht:∀ u:E4,‖u‖≤c.rOut→u≠0→ Sees L a (fun i=> mark (a i) u) X) : Issued L (fun i (x:Cover)=> tick a i d* pace c (a i) x*Remainder P X B a i x) := by
  set b:=c.rOut+1; have hp:=c.rOut_pos
  obtain ⟨n,D,hD,H⟩:= outer b B K he (by unfold b; linarith) p HH P h; let T i x:= tick a i d* pace c (a i) x*Remainder P X B a i x
  refine speeds T he ((near_minor (4*b+1)).const_mul (D*64)) (close_pay _ _ _ hD he ?_) ?_
  · filter_upwards [H,allows c S he hb n,he] with i hi hh hv x hx; let k:=mark (a i); have he: pace c (a i) x≠0:=fun ht=> hx (by simp [T,ht]); obtain ⟨hr,hb⟩:=hh x he; refine ⟨hb,?_⟩; unfold T; rw [norm_mul,norm_mul,tick,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hv.le]; refine (mul_le_mul (b:=(a i)⁻¹^d*1) (?_) (hi x hr hb) (norm_nonneg _) (?_)).trans_eq ?_
    · exact mul_le_mul_of_nonneg_left (pace_le c _ _) (pow_nonneg (inv_nonneg.mpr hv.le) _)
    · positivity
    rw [mul_one, carry_cost,inv_pow, pow_add (area x)]; have h:=included x; field_simp; simp [mul_pow]; ring
  filter_upwards [almost_all] with u hu; by_cases H:‖u‖≤c.rOut
  · have h': Tendsto (fun i=> a i • rcast (mark (a i) u)) L (𝓝 u):= marks u S he
    have hv:= on_target S he h' B p h hu (Ht u H hu) h₀
    refine Likely.congr ((show Likely L _ from ⟨_,legal c S he u⟩).mul hv) (Eventually.of_forall fun i=>?_) -- syntax
    unfold tick Playpen.steps; change _ * _=(a i:ℂ)⁻¹^4 * _; unfold T tick; rw [pow_add]; ring
  have he:= (marks u S he).norm.eventually (lt_mem_nhds (lt_of_not_ge H)); refine Likely.congr (Likely.zero (T:=ℂ)) (he.mono fun i hi=>?_); unfold Playpen.steps T; have ht : pace c (a i) (mark (a i) u) =0:= by_contra fun h=> not_lt.mpr hi.le (tag _ _ _ h).2; dsimp only; rw [ht,mul_zero, zero_mul,mul_zero]
end YM.XSpace.Shade
