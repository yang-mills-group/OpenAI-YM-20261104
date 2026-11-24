import YM.Frontier6.Exact.Follower

/-! First two-field at own relative length ‖x−y‖, then transfer to full
orthonormal Jacobi normal coordinate. Orientation x2−x1 positive
(the order within `S.useAt` immaterial on separated locus). Coordinates
fixed independent of subtraction s. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory Org
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(s:StateIndex K) {d b n:ℕ}(B:S.Field b)(D:S.Field d)

def pointOf (r:ℝ): Set E4 := {x:E4| ‖x‖=r}
def atRoot (x:E4) : Reader K:=fun s _ y v=> pairRead K s B D v x 0 y
abbrev aside (x:E4):= (1/2:ℝ) • x
lemma aside_size (x:E4): ‖aside x‖= ‖x‖/2:=by unfold aside; rw [norm_smul,Real.norm_of_nonneg (by norm_num)]; ring

def twoPair (x:E4) : Reader K:= fun s _ y v=> pairRead K s B D v (aside x) (-aside x) y
lemma pairs_clear {x:E4}{r:ℝ}(hr:‖aside x‖ ≤ r/2)(hx:x≠0){y:Points n}(hy:clearC r y):
  Points.cons (aside x) (Points.cons (-aside x) y)∈conf _:=by
  let p:= aside x
  have hp:p≠0:=smul_ne_zero (by norm_num) hx; have hp':‖-p‖≤r/2:=by rw [norm_neg]; exact hr
  refine gap_conf (a:=0) le_rfl (gap_append (gap_down (clear_translation hp' hy) ((norm_nonneg _).trans hr)) (aside x) (fun i=> ?_))
  refine Fin.cases ?_ (fun j=> ?_) i
  · change 0 < ‖-p-p‖
    apply norm_pos_iff.mpr; rw [show -p-p=(-(2:ℝ)) • p by rw [neg_smul,two_smul]; abel]; exact smul_ne_zero (by norm_num) hp
  change 0 < ‖y j - p‖; exact lt_of_le_of_lt ((norm_nonneg _).trans hr) (by linarith only [clear_exterior hy j, norm_sub_norm_le (y j) p,hr])
lemma root_shift {x:E4}{y:Points n}(v:Fin n→ S.Tag)(h: Points.cons (aside x) (Points.cons (-aside x) y)∈conf _):
  twoPair K B D x s n y v= shiftedReader K (-aside x) (atRoot K B D x) s n y v:=by
  have hh:= readings_shift K s (aside x) (Points.cons (-aside x) y) (Fin.cons ⟨b,B⟩ v) D h (aside x)
  have he:aside x + aside x=x:=by rw [← add_smul,show (1:ℝ)/2+1/2=1 by norm_num,one_smul]
  rw [he,across_cons,neg_add_cancel] at hh; change _=atRoot K B D x s n (Points.across (- -_) y) _; rw [neg_neg]; exact hh.symm

abbrev normalRat:ℝ:= Real.sqrt 2
lemma normalRat_pos : 0 < normalRat:=Real.sqrt_pos.2 (by norm_num)
lemma normalRat_sq : normalRat^2=2:= Real.sq_sqrt (by norm_num)
def normal2 (x:E4):= aside (normalRat • x)
lemma centered_normal (x:E4): (-normal2 x)+normal2 x=0:= by simp
lemma normal_size (x:E4): ‖normal2 x‖= normalRat/2 * ‖x‖:=by unfold normal2; rw [aside_size,norm_smul,Real.norm_of_nonneg normalRat_pos.le]; ring
/-- characterizes orthogonal Jacobi slice (normalized). -/
lemma orth_normal (x:E4): ‖-normal2 x‖^2 + ‖normal2 x‖^2=‖x‖^2:=by
  rw [norm_neg,normal_size,mul_pow,div_pow,normalRat_sq]; ring
lemma normal_inv (x:E4): (normalRat)⁻¹ • ((normal2 x)-(-normal2 x))=x:=by
  unfold normal2 aside; rw [sub_neg_eq_add,← add_smul,show (1:ℝ)/2+1/2=1 by norm_num,one_smul,inv_smul_smul₀ normalRat_pos.ne']
lemma normal_ne (x:E4) (he:x ≠ 0): normalRat • x ≠ 0:=smul_ne_zero normalRat_pos.ne' he
/-- Final punctured pair relative to centroid at zero. `x` is *orthonormal*
relative coordinate; the optional constant Jacobians are not included in the
kernel. Extend against full E4 `volume`. -/
def pair (x:E4): Reader K:= twoPair K B D (normalRat • x)
lemma pair_at (x:E4)(y:Points n)(v:Fin n→ S.Tag):
  pair K B D x s n y v=S.useAt (state K s) (Points.cons (normal2 x) (Points.cons (-normal2 x) y)) (Fin.cons ⟨d,D⟩ (Fin.cons ⟨b,B⟩ v)):= pair_reads ..

open Bid Canvas Platform MergeProof MergeProof.Ribbons Next.UVStress Cells Extraction.Around Next.Extract Dash PhysicalNext.Repeat.Legato
variable {H:Table C.book}{M:ℕ→Table C.book}{Q:Bin H}{Y:DiffPlan S} (h:Base C F H M Q S Y) (hp:PairProducer C) (hg:G.Simple) (hW:Extraction.Wcmain C)(hG:Grill C F)
include h hp hg hW hG
lemma root_dual : DualEstimate K pointOf (atRoot K B D) ((b:ℝ)+d):=by
  intro I inst n v w L hL hv ε hε A ha
  refine ⟨1,zero_le_one,?_⟩
  filter_upwards [anchor_dual K v h hp hg hW hG B D w hL hv hε ha] with r hr x hx y hy u c hc hQ
  change ‖listen K B D v y u c x‖ ≤ _; rw [one_mul,sub_add_eq_sub_sub]; exact hr _ hx _ hy u c hc hQ
lemma two_dual : DualEstimate K pointOf (twoPair K B D) ((b:ℝ)+d):=by
  let p:= fun x:E4=>-aside x
  have hh:∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈pointOf r, ‖p x‖ ≤ r:= Eventually.of_forall fun r x (hx:‖x‖=r) => by rw [← hx]; unfold p; rw [norm_neg,aside_size]; exact half_le_self (norm_nonneg _)
  have he:= (root_dual K B D h hp hg hW hG).recenters K _ _ _ p hG hh
  intro I inst n v w L hL hv ε hε A ha
  obtain ⟨a,ha',hU⟩:= family_gap hL hv
  obtain ⟨M,hM,H⟩:= he I n v w L hL hv ε hε A ha
  refine ⟨M,hM,?_⟩
  filter_upwards [H,mem_nhdsWithin_of_mem_nhds (ge_mem_nhds ha'),self_mem_nhdsWithin] with r hr hx h' x (hy:‖x‖=r) y hy' s c hc hK
  refine le_trans (le_of_eq (congr_arg norm (Finset.sum_congr rfl ?_))) (hr x hy y hy' s c hc hK)
  intro i _; exact congr_arg (c i * ·) (root_shift K (s i) B D _ (pairs_clear (by rw [aside_size,hy]; exact div_le_div_of_nonneg_right hx (by norm_num)) (norm_pos_iff.mp (by rw [hy]; exact mem_Ioi.mp h')) (hU _ hy' i)))
lemma pair_dual : DualEstimate K pointOf (pair K B D) ((b:ℝ)+d):=by
  intro I inst n v w L hL hv ε hε A ha
  obtain ⟨W,hA,hT⟩:= two_dual K B D h hp hg hW hG I n v w L hL hv ε hε A ha
  let t:= (w:ℝ)-(b+d:ℝ)-ε
  have he:Tendsto (fun r:ℝ=> normalRat*r) (𝓝[>] 0) (𝓝[>] 0):= by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds; simpa only [mul_zero] using (show Tendsto (fun r:ℝ=>r) (𝓝 0) (𝓝 0) from tendsto_id).const_mul normalRat -- check
    · exact ((show ∀ᶠ r:ℝ in 𝓝[>] 0,0<r from self_mem_nhdsWithin).mono fun r hr=> mul_pos normalRat_pos hr)
  refine ⟨W*normalRat^t, mul_nonneg hA (Real.rpow_nonneg normalRat_pos.le _),?_⟩
  filter_upwards [self_mem_nhdsWithin,he.eventually hT] with r hr h x (hx:‖x‖=r) y hy s c hc he
  refine (h (normalRat • x) (show ‖normalRat • x‖= normalRat*r by rw [norm_smul,Real.norm_of_nonneg normalRat_pos.le,hx]) y hy s c hc he).trans_eq ?_
  rw [Real.mul_rpow normalRat_pos.le (mem_Ioi.mp hr).le,mul_assoc]
end YM.Frontier6
