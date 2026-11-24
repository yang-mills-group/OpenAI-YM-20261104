import YM.OPE.Compatible.Maestro.Ticket
/-!
# Pair of timers.

The second one uses an OVER-resolution determined afterwards by the
maximum log even at an ancestor. Works in unbalanced trees without first
comparing all the logarithms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot
variable {G:Gauge}{C:Family G}{I : Type}{l:Filter I}{T r : I→ℝ}{q:I→ℕ}{L b n:ℕ}
-- first index achieving mesh ≤ r. If r ≤0 dummy
private lemma later_grid (C:Family G) {r:ℝ}(hp:0<r):∃ i,C.S.a i ≤ r:= (C.S.shrinks.eventually (ge_mem_nhds hp)).exists
def firstTick (C:Family G)(r:ℝ):= if h:0 < r then Nat.find (later_grid C h) else 0
lemma tinyOf (C:Family G){r:ℝ}(hp:0<r): C.S.a (firstTick C r) ≤ r:=by rw [firstTick,dif_pos hp];exact Nat.find_spec (later_grid C hp)
lemma tinyUp {r:ℝ}(C:Family G)(hp:0<r)(hf:n < firstTick C r): r < C.S.a n:= lt_of_not_ge fun hh=> (hf.not_ge (by rw [firstTick,dif_pos hp]; exact Nat.find_min' _ hh))
lemma first_order {C:Family G}{r t:ℝ}(hp:0<r)(hh:r≤t): firstTick C t ≤ firstTick C r:=by nth_rw 1 [firstTick]; rw [dif_pos (hp.trans_le hh)]; exact Nat.find_min' _ ((tinyOf C hp).trans hh)
variable (hr:Tendsto r l (𝓝[>]0))
include hr
lemma tick_grow :Tendsto (fun i=>firstTick C (r i)) l atTop:=by
    apply tendsto_atTop.mpr; intro i; filter_upwards [hr.eventually self_mem_nhdsWithin,(hr.mono_right nhdsWithin_le_nhds|>.eventually (ge_mem_nhds (C.S.a_pos i)))] with j hp hi; exact C.S.strictAnti.le_iff_ge.mp ((tinyOf C (r:=r j) hp).trans hi) -- `iff` orientation
variable (hG:G.Simple)(A:Allot C)(ht:Tendsto T l atTop)(h:Score l T (fun i=> -Real.log (r i)))
include hG A ht h
lemma grid_choice : Round l T (fun i=>β C (firstTick C (r i))) ∧ Round l T (fun i=>C.S.a (firstTick C (r i))/r i):=by
    let q i:= firstTick C (r i); let p i:= q i-1; have hh:= tick_grow (C:=C) hr
    have hp:Tendsto p l atTop:=tendsto_atTop.mpr fun k=> by filter_upwards [hh.eventually_gt_atTop k] with j hj; change _ ≤ q j-1; change k< q j at hj; omega
    have hx : ∀ᶠ i in l,p i+1=q i∧ r i < C.S.a (p i) :=by
        filter_upwards [hh.eventually_gt_atTop 0,hr.eventually self_mem_nhdsWithin] with j hj hv; change 0 < q j at hj; have hz:p j < q j:= Nat.sub_one_lt (by omega : q j ≠ 0)
        exact ⟨show q j-1+1=q j from Nat.sub_add_cancel hj, tinyUp C hv hz⟩
    have he: Score l T (fun i=>C.S.scale (p i)):=by
       refine h.pointwise ?_ (Eventually.of_forall fun _=>Shoot.scale_nn ..); filter_upwards [hx,(hr.eventually self_mem_nhdsWithin)] with i ht he; unfold Schedule.scale; rw [Real.log_inv]; exact neg_le_neg (Real.log_le_log he ht.2.le)
    have hP:= scale_coin hG hp ht he
    have hQ:∀ᶠ i in l, 0 < r i:=hr.eventually self_mem_nhdsWithin
    have hv:∀ᶠ i in l,0 < C.S.a (q i)/r i:= hQ.mono fun i hi=>div_pos (C.S.a_pos _) hi
    refine ⟨(stepβ A hG ht hP.up).adjust (hx.mono (fun i hi=>congr_arg _ hi.1)),hv,(Score.steady (1:ℝ) ht).pointwise (hQ.mono (fun i h=> (div_le_one h).mpr (tinyOf C h))) (hv.mono (fun _ h=>h.le)),hP.up.pointwise ?_ (hv.mono (fun _ h=> (inv_pos.mpr h).le))⟩
    filter_upwards [hx] with i hi; rw [inv_div]; refine le_trans ((div_le_div_of_nonneg_right hi.2.le (C.S.a_pos _|>.le)).trans_eq ?_) (A.block_cheap (p i))
    rw [show firstTick C (r i)=_ from hi.1.symm,C.S.a_step]; have hx:=C.S.a_pos (p i); unfold extent; field_simp -- level unused
omit hG A ht h
-- refine interpolation many points even when projected with Purchase birth k. aperture =one extra + max(k(parent),target grid/T^N)
def resolution (C:Family G)(b L:ℕ)(η r t:ℝ):= max (closeK C b η r) (firstTick C (r/(t^L)))
variable {η:ℝ}(hη:0<η)
-- mesh request parent
set_option quotPrecheck false
local notation "x"=> fun i=> r i/T i^L
local notation "K!"=> fun i=> resolution C b L η (r i) (T i)
include ht
lemma sparse : Tendsto (fun i=>r i/T i^L) l (𝓝[>]0):=by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · have he : ∀ᶠ i in l,0 < x i ∧ x i ≤ r i:=by
         filter_upwards [hr.eventually self_mem_nhdsWithin,ht.eventually_ge_atTop 1] with i hi hT; have hy: 1 ≤ T i^L:=one_le_pow₀ hT; refine ⟨div_pos (show 0 < r i from hi) (zero_lt_one.trans_le hy),div_le_self (le_of_lt hi) hy⟩ -- cast
      exact squeeze_zero' (he.mono fun _ h=>h.1.le) (he.mono fun _ h=>h.2) (hr.mono_right nhdsWithin_le_nhds)
    filter_upwards [hr.eventually self_mem_nhdsWithin,ht.eventually_gt_atTop 0] with i hi ht using div_pos (show 0 < r i from hi) (pow_pos ht _)
lemma below_resolution: ∀ᶠ i in l,C.S.a (K! i)≤r i/T i^L:=by
    filter_upwards [(sparse (L:=L) hr ht).eventually self_mem_nhdsWithin] with i hi; exact le_trans (C.S.strictAnti.antitone (le_max_right (closeK C b η _) _)) (tinyOf C (show 0< r i / T i^L from hi))
include h
lemma sparse_score (L:ℕ): Score l T (fun i=> -Real.log (r i/T i^L)):=by
    let f i:= Real.log (T i); have hs: Score l T f:=Score.pointwise (Score.time ht) ((ht.eventually_ge_atTop 0).mono fun i h=>Real.log_le_self h) ((ht.eventually_ge_atTop 1).mono fun i h=> Real.log_nonneg h)
    refine (h.plus ((Score.steady (L:ℝ) ht).product hs) ht).congr ?_
    filter_upwards [hr.eventually self_mem_nhdsWithin,ht.eventually_gt_atTop 0] with i hi h; rw [Real.log_div (ne_of_gt hi) (pow_ne_zero _ h.ne'),Real.log_pow]; unfold f; ring
include hG A hη
lemma resolution_cost :Tendsto (K!) l atTop ∧ Round l T (fun i=> β C (K! i))∧ Round l T (fun i=> C.S.a (K! i)/r i):=by
    have hK:Tendsto K! l atTop:= tendsto_atTop_mono (fun _=> le_max_left ..) (elevated hG A b hη hr)
    have hV:= grid_choice (C:=C) (sparse (L:=L) hr ht) hG A ht (sparse_score hr ht h L)
    have hp:= epoch_score hG A b hη hr ht h
    have hA:=arrival_price hG A b hη hr ht h
    let a i:= closeK C b η (r i); let j i:=firstTick C (r i/T i^L)
    refine ⟨hK,Round.if_inv (Eventually.of_forall fun _=> β_pos ..) ?_ ht (Eventually.of_forall fun _=> (β_one ..).le),?_⟩
    · exact Score.congr (hp.up.maxS hV.1.up ht) (Eventually.of_forall fun i=> ((β_increases hG).monotone.map_sup ..).symm)
    have hx:Round l T (fun i=> C.S.a (j i)/r i):=by
       have hp: Round l T T:= Round.if_inv (ht.eventually_gt_atTop 0) (Score.time ht) ht (ht.eventually_ge_atTop _)
       apply (hV.2.div (hp.power L ht)).adjust
       filter_upwards [hr.eventually self_mem_nhdsWithin,ht.eventually_gt_atTop 0] with i hi he
       change C.S.a (j i)/_ /_= _; have hv:0<r i:=hi; field_simp
    refine (hA.less hx ht).adjust ?_
    filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi; have hf:0< r i:=hi; change min _ _= _
    unfold resolution; rcases le_total (a i) (j i) with h|h
    · rw [max_eq_right h]; exact min_eq_right (div_le_div_of_nonneg_right (C.S.strictAnti.antitone h) hf.le)
    rw [max_eq_left h]; exact min_eq_left (div_le_div_of_nonneg_right (C.S.strictAnti.antitone h) hf.le)
end YM.OPE.Arboreal
