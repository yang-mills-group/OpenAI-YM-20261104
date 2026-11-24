import YM.RG12.Alidade.Rental
import YM.RG12.Alidade.Hold
/-! # Precision adapter for producers. Pair inputs ONLY through order two with remainders
at low-order precision (no IR basis/readout factors established here if not first buying
this ticket or an initial comparative estimate on just short history).

* Coupling g_k is the prescribed `regulatorRun`, on the SAME all-cutoff filter as charts (sublimit of fuse).
* Length costs polynomial clock in general tickets; meter costs on expansions on these lenses; chart comparison before IR readout. Scope: which geometries and label spellings exactly:
 the two points QUOTED in `Shapes.scope`, not profiles smeared/c_asserted at any fixed physical scale. To plug master reports on its
 displacement rule only, must still move/disambiguate chart/profiles with same budgets before
 applying this contract. Our unconditional matrices don't supply that comparison. Uniformity not
 requested in discretization denominator N; host picks any sufficiently large N after horizon,
 and across all lit hops stays there with EXACT common-reflection spin. No other Ward inputs
 assumed.
* Cost of s/t: use actual mesh k and k+1; ONE anomaly response cost A_d/N * log(blockL) on the squared price at any such level; logarithm of L factor really required (not
 L-conditional A_L log L). Equivalent driver uses clipped dyad geometric ladder (later proofs).
 Strictly lowering entries of frame correction can have costs of any fixed meter powers. For
 bounded ratios through this march, such lifting losses into TRUE canonical calibration can be
 paid by even qlocal-order estimates above R=2 if on needed objects.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Lattice RG Source Real Frames Commission Rail
open Extraction Bid MergeProof Org Spec PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired YM.Pert.Dense
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{d:ℕ}
variable (U:Final C f S) (Q:OPE.Prescription U.sector.derivatives)(hQ:Q.Coherent)
variable {φ:Filter UVIndex}[φ.NeBot]{M:∀ d,ℕ→RepChart C d}
variable (P:Port C){lit:ℕ→Prop}
variable (h:G.Simple)(hO:Observing C U.room.cutoff φ M)
variable (i:Fin 3)(ax:Axis)
set_option quotPrecheck false
local notation "Z!"=>C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "meter"=> C.path.levels.clock.monitor
local notation "clk"=>epoch C.path.levels
local notation "σ"=>G.slopeConstant
local notation "arc!"=> (P.panels d i).arc
local notation "B!"=> U.sector.derivatives
local notation "X!"=> wheelR U d
variable {Y:ℕ → Col (wheelR U d)≃ₗ[ℂ] S.Field d} {Z:ℕ→TableL C d}{N:ℕ}{K:ℝ}{p:ℕ}

def slice (Y:Levels G)(i:ℕ):= Real.log (Y.S.block i).val
lemma slice_first (Y:Levels G)(i:ℕ):Real.log 3 ≤ slice Y i:=Real.log_le_log (by norm_num) (by exact_mod_cast Y.S.block_large i) -- unfold after? formula output in exact trans.rfl. test
lemma spicy (Y:Levels G) : ∀ᶠ i in atTop, epoch Y (i+1)/epoch Y i ≤2 := epoch_neighbor Y
lemma surges (Y:Levels G)(i:ℕ): epoch Y (i+1)/epoch Y i=1+slice Y i/(Real.log 3*epoch Y i) := by
   have he':0<epoch Y i:=zero_lt_one.trans_le (begun Y i)
   have hs: epoch Y (i+1)=epoch Y i+ slice Y i/ Real.log 3:=by unfold epoch slice; rw [Y.S.scale_succ,add_div]; ring
   rw [hs,add_div,div_self he'.ne']; congr 1; ring
-- simplify
lemma history_rule (Y:Levels G)(_h:G.Simple) : Tendsto (fun i=>epoch Y (i+1)/epoch Y i-1) atTop (𝓝 0) :=by
   have he:= Y.fits.mesh; have hi:= Y.S.divergent.eventually_gt_atTop 0; let τ:=epoch Y
   apply squeeze_zero' (g:=fun i=>slice Y i/Y.S.scale i) ?_ ?_ he
   · filter_upwards with i; linarith only [epoch_unit Y (Nat.le_succ i)]
   filter_upwards [hi] with i hi; rw [surges Y i,add_sub_cancel_left]
   exact div_le_div_of_nonneg_left (arc3.trans_le (slice_first ..)).le hi (by unfold epoch; field_simp; linarith only [arc3])
-- relation with drift and calendar. exact before all needed tests
lemma entrance (Y:Levels G)(h:G.Simple) : ∀ᶠ i in atTop, (Real.log 3)*epoch Y i /Y.clock.hatBeta i ≤ 2/σ :=by
   have he := Y.S.divergent.eventually_ge_atTop (Real.log 3)
   filter_upwards [he] with i hi
   rw [div_le_div_iff₀ (year Y i) (Gauge.slopeConstant_pos h)]
   have ht :Real.log 3*epoch Y i=Real.log 3+Y.S.scale i:=by unfold epoch; field_simp
   rw [ht]; unfold Calendar.hatBeta
   have h':0<Y.clock.bar:=Y.clock.bar_pos
   nlinarith only [mul_le_mul_of_nonneg_right hi (Gauge.slopeConstant_pos h).le, h']

/-- Local gauge-driver requirements, lower order version: all-order input NEVER needed here.
    Both geometry endpoints on same finer k+1 columns and exact engineering.
    First/second order `M` discrepancy from chart resolutions must be strictly filtration-lowering,
    and remaining second-order part `b` in `Stencil.Second.ledger`, Common-degree LOG response.
    Meter factors harmless at first order in the *individual* coefficients, even applied to
    qlocal's eta loss eta<=1/2. Need uniform second-order precision specifically in the
    measured dilation response `b`, not in the individual arrays. Also M correction is lower
    only for *changing scale*, so this criterion never asks that initial frame differ from free
    only below the diagonal. `Axis` real RC pair may be polished finite by producers (must
    identify at these exact asymptotic reports, e.g. no swapping unseleced and selected flows).

    Only asks this eventually on meshes and on one same convergence filter for the current
    horizon demands. Holder (sampleN) must already hold Assembly.Wears or Club. -/
structure PencilInput (q:ℕ→ℝ)(t:ℕ→ℝ)(Z:Levels G)(Y:ℕ → Col (wheelR U d)≃ₗ[ℂ] S.Field d)(lit:ℕ→Prop)(N:ℕ) : Prop where
   extract : ∃ A:ℝ,0≤A ∧ ∃ o:ℕ, ∀ᶠ k in atTop, lit k→ lit (k+1)→ let W:=Col (wheelR U d)
      let f(s):=sampleForm U (Shapes.scope ax N) d s
      let v:=Y (k+1)
      ∃ (Ξ: Charge (V:=W)) (Hp:Mixes (V:=W)), strict Hp.first ∧ strict Hp.second ∧
      Second Ξ Hp (Z.clock.monitor k^o) (q k) (A*slice Z k)
        ((f (t k)).eval ∘ v ∘ Frames.dilate (t k/t (k+1))) ((f (t (k+1))).eval ∘ v)

-- buy formally against a general expansion parameter with `Barred` costs (not itself
-- physics on C if unspecified g_k). Next port asks on true trajectories.
variable {U Q hQ P i}
variable (HC:Club M P U Q hQ φ d N ax lit i Z Y K p)
include h HC
set_option maxHeartbeats 400000 in
lemma turnkey {q:ℕ→ℝ}{m:ℝ}(hs:Barred (Z:=(Z!)) q m)(H:PencilInput U ax q (torchR (Z!) arc! N) (Z!) Y lit N):
    let t:=torchR (Z!) arc! N
    ∃ s:ℕ,Clearing (Z!) Y (lens U d ax N ∘ t) t (fun _=>0) s 1 lit K:=by
   intro t
   let g:=lens U d ax N ∘ t
   have hK:=HC.numbers.2; have hM:=Barred.affords hs; let B:=2/σ
   have hσ:=Gauge.slopeConstant_pos h; have heB:0 < B:=by unfold B; positivity
   obtain ⟨a,ha,o,hΞ⟩:=H.extract
   let c:=4*m*(a+(Real.log 3)⁻¹)*B
   have hc:0 ≤ c:= by unfold c; have hlog:0 ≤ (Real.log 3)⁻¹:=inv_nonneg.mpr arc3.le; positivity
   obtain ⟨k₀,hk₀⟩:=exists_nat_gt (K^2*c)
   have hy:= (history_rule C.path.levels h).const_mul (2*K^2*c)
   rw [mul_zero] at hy
   refine ⟨2*k₀,fun _=>⟨le_rfl,by norm_num⟩,?_⟩
   filter_upwards [hΞ,HC.active,(tendsto_add_atTop_nat 1).eventually HC.active,eventual_bar h hs o,entrance C.path.levels h, hy.eventually (ge_mem_nhds zero_lt_one),(epoch_late C.path.levels).eventually_ge_atTop 2] with k h1 h2 h3 hf h4 h5 h6 hx hz
   obtain ⟨Ξ,M',hl,hl',hh⟩:=h1 hx hz
   have hK₀: Tests (g k ∘ Y k) K:= (h2 hx).costs; have hK₁: Tests (g (k+1) ∘ Y (k+1)) K:= (h3 hz).costs
   obtain ⟨hC⟩:= hh.charter
   let z:=(meter k)^o; let x:=slice C.path.levels k; let r:= (clk (k+1)/clk k)-1
   let v:=q k; have hv:=hs.positive k;have hτ:= HC.calendar.1
   obtain ⟨J,hH,hJ,hU,hx0⟩:= remains M' Ξ v z hv.le hf.2.1 hC hl hl'
   have hr:0 ≤ r:=by unfold r; linarith only [epoch_unit C.path.levels (Nat.le_succ k)]
   have hσx:0 < x:= arc3.trans_le (slice_first (Z!) k)
   let y:=t k/t (k+1); have ht:0<y:=div_pos (hτ _) (hτ _)
   have hx' : x/χ k ≤ B*r:=by
      have hv:r=x/(Real.log 3*clk k):=by unfold r x; rw [surges,add_sub_cancel_left]
      rw [hv]; let u:= Real.log 3 * clk k;have hu:0<u:=mul_pos arc3 (zero_lt_one.trans_le (begun _ _))
      have hq:u ≤ B*χ k := (div_le_iff₀ (year (Z!) k)).mp h4
      rw [← mul_div_assoc, div_le_div_iff₀ (year (Z!) k) hu]; change x *u ≤ _ ; nlinarith only [mul_le_mul_of_nonneg_left hq hσx.le]
   let L:= pace (Y k) (Y (k+1)) y ht
   refine ⟨ht,⟨?_,?_,hK₀,hK₁, pace_form _ _ (h2 hx).wage (h3 hz).wage ht,?_,?_,?_⟩⟩ -- order Y _ infer?
   · exact le_rfl
   · exact J
   · exact ⟨hJ,hU⟩
   · exact fun v=>⟨(hx0 v).1.trans (mul_le_mul_of_nonneg_right (by simpa using h6) (norm_nonneg _)),(hx0 v).2.trans (mul_le_mul_of_nonneg_right (by simpa using h6) (norm_nonneg _))⟩
   intro w
   let u:Col (X!) := J w
   let f(i):=(sampleForm U (Shapes.scope ax N) d (t i)).eval
   let G:= f (k+1) (Y (k+1) w); let G':= f k (Y k (L u))
   have h' := tuned_pair Ξ M' hh (hf.2.1.trans (by norm_num)) u -- args
   have hc' : |G'-G| ≤ (27*z^3*(v^2*Real.sqrt v)+a*x*v^2)*‖u‖^2:=by
      unfold G' L; rw [pace_at,LinearEquiv.apply_symm_apply]; simpa only [Function.comp_apply,hH] using! (show |_| ≤ _ from (show |(f k ∘ Y (k+1) ∘ Frames.dilate y) u-(f (k+1) ∘ Y (k+1)) (turned M' v (J w))| ≤ _ from h'))
   have hGk: |G'-G| ≤ c*r*‖w‖^2:=by
      apply hc'.trans
      have hd:0 ≤ a+(Real.log 3)⁻¹ := add_nonneg ha (inv_pos.mpr arc3).le
      have hvκ : v^2 ≤ m/χ k:=(le_div_iff₀ (year (Z!) k)).mpr (hs.meters k)
      have hi:1 ≤ x*(Real.log 3)⁻¹:=by rw [← div_eq_mul_inv]; exact (one_le_div arc3).mpr (slice_first _ _)
      have ha':27*z^3*(v^2*Real.sqrt v)+a*x*v^2 ≤ (a+(Real.log 3)⁻¹)*x*v^2:=
        by nlinarith only [mul_le_mul_of_nonneg_right (show 27*z^3*Real.sqrt v ≤ 1 from hf.2.2) (sq_nonneg v),mul_le_mul_of_nonneg_right hi (sq_nonneg v)]
      have hu : ‖u‖^2 ≤ 4*‖w‖^2:=by nlinarith only [(show ‖u‖ ≤ 2*‖w‖ from (hx0 w).1),norm_nonneg u,norm_nonneg w]
      let l:=a+(Real.log 3)⁻¹
      have hΨ : l*x*v^2 ≤ l*m*(B*r):=by
         calc _ ≤ l*x*(m/χ k):= mul_le_mul_of_nonneg_left hvκ (mul_nonneg hd hσx.le)
              _ = l*m* (x /χ k):=by ring
              _ ≤ _:=mul_le_mul_of_nonneg_left hx' (mul_nonneg hd hM.le)
      exact (mul_le_mul (ha'.trans hΨ) hu (sq_nonneg _) (mul_nonneg (mul_nonneg hd hM.le) (mul_nonneg heB.le hr))).trans_eq (by unfold c l; ring)
   -- deduce coerc then tested
   have hν : ‖w‖ ≤ K*Real.sqrt G:= hK₁.lower _
   have hG :0 ≤ G:=by
      by_cases ho:w=0
      · unfold G;rw [ho,map_zero]; exact ((Frames.Gram.Square.zero _).ge)
      have h₁: 0 < Real.sqrt G:= pos_of_mul_pos_right ((norm_pos_iff.mpr ho).trans_le hν) (zero_le_one.trans hK)
      exact (Real.sqrt_pos.mp h₁).le
   have heK : ‖w‖^2 ≤ K^2*G:=by have ht:= pow_le_pow_left₀ (norm_nonneg _) hν 2; rwa [mul_pow,Real.sq_sqrt hG] at ht
   let s':=clk (k+1)/clk k; have hr₀:1+r ≤ s':=by unfold r s'; linarith
   have hKZ0 : 2*K^2*c*r ≤ 1:=h5
   have hf':= permits (m:=k₀) (s:=clk k) (s':=clk (k+1)) hG (norm_nonneg w) heK hc hGk hr hr₀ hk₀.le hKZ0
   rw [Real.exp_zero,mul_one]; exact hf'
-- High level low-order portal on shared variables. Anchored deterministic q or ALL Spear
-- sublimit values. Doesn't let q depend on the presentation correction scheme.
def Printed (U:Final C f S)(Q:OPE.Prescription U.sector.derivatives)(hQ:Q.Coherent)(P:Port C)(i:Fin 3)(d:ℕ)(lit:ℕ→Prop)(ax:Axis) : Prop :=
  ∀ (φ:Filter UVIndex)[φ.NeBot],φ ≤ f.fuse→∀ M,Observing C U.room.cutoff φ M→∀ q, Spear (C:=C) (Ultrafilter.of φ) q →
     ∀ᶠ N in atTop,∀ (Z:ℕ→TableL C d)(Y:ℕ → Col (wheelR U d)≃ₗ[ℂ] S.Field d)(K:ℝ)(p:ℕ),
     Club M P U Q hQ φ d N ax lit i Z Y K p → PencilInput U ax q (torchR C.path.levels (P.panels d i).arc N) C.path.levels Y lit N
omit HC [φ.NeBot] in
lemma proposals (he:Printed U Q hQ P i d lit ax) : Proposal U Q hQ P i d lit ax:=by
    intro φ x hb M hM t
    obtain ⟨q,hr,hA,-⟩:=coupling_price h U.room.cutoff hM
    filter_upwards [he φ hb M hM q hr] with N hN Z Y K p hC
    obtain ⟨s,hS⟩:=turnkey h ax hC hA (hN Z Y K p hC) -- order h
    exact ⟨s,1,hS⟩
end YM.RG12.Alidade
