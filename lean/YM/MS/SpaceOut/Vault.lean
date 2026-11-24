import YM.MS.SpaceOut.Bridge
/-!
# Piecewise cutoff Cost recover when derivatives identically zero in residual.Coord.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista
open scoped Topology ContDiff Interval
variable {I:Type}{S T:Scale I}{p q:QP}{D:I→Set QP}
variable (h:∀ i,2≤ S.length i)
include h
lemma curtainβ (hs:∀ i,D i⊆ firstZone Axis): Benefit S D (fun i p=>rim ( S.length i ) p):= by
    refine ⟨ fun i=> rim_s (h i),fun j=>?_ ⟩; obtain ⟨C,hC,hK⟩:= Fiddle.β_cost.total_bd j; refine ⟨ C,hC,0,fun i p hp=>?_ ⟩; obtain hu:= S.pos i; dsimp only; rw [ (( rim_at (h i) ( hs i hp ) ).iteratedFDeriv ℝ j).eq_of_nhds]; unfold west; rw [iteratedFDeriv_comp_const_smul _ ( door_sm.of_le (by exact_mod_cast le_top) ), norm_smul ]; simp only [pow_zero,mul_one,one_mul]; rw [ Real.norm_of_nonneg (pow_nonneg hu.le _),mul_comm ]; exact mul_le_mul_of_nonneg_right (hK _) (pow_nonneg hu.le _) -- `iterated` rewrite shape
lemma beltP {t:I→ℝ}(hs:∀ i,D i⊆ firstZone Axis): Benefit S D ( fun i p=>( veil ( S.length i ) (t i) p:ℂ )):= by
    apply Costs.ofReal; unfold SpaceOut.veil; refine Costs.sub ( Costs.scalar ( p:=fun _=>(1:ℝ) ) (Cost.of_le fun _ _ _=> ?_) ) ?_ ; · simp
    have he: Benefit S D (fun i (p:QP)=>Real.smoothTransition (t i/S.length i-1)) := Costs.scalar (Cost.of_le (fun _ _ _=> (by rw [Real.norm_of_nonneg ( Real.smoothTransition.nonneg _)]; exact smoothTransition.le_one _) ));
    convert he.rmul ( curtainβ h hs ) using 1; ext; simp
variable {t:ℝ}{r:I→ℝ}
omit h in
lemma patchsmall {n:ℝ}(h:2 ≤ n)(hp:n* ‖p‖ < 1)(hx:2*n≤t) : veil n t=ᶠ[𝓝 p] 0:= by
    have hn :0<n:=( by linarith ); filter_upwards [(continuous_const.mul continuous_norm).continuousAt.preimage_mem_nhds (gt_mem_nhds hp)] with x hx'; change 1-Real.smoothTransition (t/n-1)*rim n x=0; obtain hV:x∈Set.univ:=Set.mem_univ _; obtain hx': n*‖x‖<1:= hx'; have hx0: ‖x‖<keyV :=(by unfold keyV; nlinarith [Real.pi_gt_three,norm_nonneg x]); rw [(show Real.smoothTransition ( t/n-1 )=1 from smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hn]; linarith)),one_mul,rim_Q h hx0,west, door_c ?_,sub_self ]; rw [norm_smul_of_nonneg hn.le]; unfold Fiddle.inner; linarith [Real.pi_gt_three]
variable {f:I→QP→ℂ}
abbrev Gate1 (S T:Scale I)(i:I): Set QP:= firstZone Axis∩ {p:QP| T.length i<2*S.length i ∨ 1≤ S.length i * ‖p‖ }
def masker (S T:Scale I)(f:I→ QP → ℂ):= fun (i:I)(p:QP)=> (veil (S.length i) (T.length i) p:ℂ)*f i p
omit h in
lemma regionζ (i:I)(p:QP)(hp:p∈ Gate1 S T i): T.length i ≤ 2*T.weight i p*S.length i:= by
    obtain hh|hh:= (show T.length i<2*S.length i ∨ 1≤ S.length i * ‖p‖ from hp.2); · exact hh.le.trans ( mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by norm_num) ( T.one_le_weight i p )) (S.pos i|>.le) )
    unfold Scale.weight; obtain hw:= norm_nonneg p; obtain h':= S.pos i; obtain h'':= T.pos i; nlinarith
-- carry optional.Invariance. Lease.Folding.EPI
lemma crest (n:ℕ) (hp:∀ i, S.length i ≤ T.length i)(he:∀ i,T.basic i=S.basic i)(hf:Line T located f (fun i=> T.length i ^ n)): Line S located (masker S T f) (fun i=> S.length i ^ n * (S.length i / T.length i)) := by
    have hv:= clock_mesh hp n (regionζ (T:=T)) hf ( fun i x hx=> hx.1 ) he; obtain hx : Line S ( Gate1 S T ) (masker S T f) _ := Deposit hv (beltP h fun i x h=>h.1); intro j; refine ⟨ ( hx j ).smooth,fun n' => ?_⟩; obtain ⟨C,hC,w,hX⟩:=(hx j).quoted n'; refine ⟨ C,hC,w,fun i p hp=>?_⟩; by_cases hT:p∈Gate1 S T i; · exact hX i p hT
    have he: ¬ (T.length i<2*S.length i ∨ 1≤ S.length i * ‖p‖):= fun hc=> hT ⟨ hp,hc ⟩; push Not at he; have hN:= patchsmall (p:=p) ( h i ) he.2 he.1; dsimp only; have hm : masker S T f i=ᶠ[𝓝 p] 0:= by filter_upwards [ hN ] with x hx; rw [masker,hx]; simp
    rw [ (hm.iteratedFDeriv ℝ n').eq_of_nhds ]; simp only [ iteratedFDeriv_zero, Pi.zero_apply, norm_zero ]; -- first lemma ambiguous; inspect
    have ht:=S.pos i; have hk:= T.pos i; have he:=S.weight_pos i p; have hB := S.basic_pos i; change 0≤ C*S.basic i^w * _; positivity
end YM.MS.SpaceOut
