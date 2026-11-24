import YM.MSbar.Heath.Rad
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paths
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{W: Type*}{U V:Config G n}
variable {o:Site n}{R:Rep G n}{σ C T a v:ℝ}
open WilsonStartup
-- All dependence from single site change.
def Stab (o:Site n)(U V: Config G n) := ∀ X:Support n,o∉X→ Agrees (X:Set _) U V
lemma stitch (p:Edge (Site n))(V:Config G n)(W:G.El): Stab p.1 V (update V p W) :=fun X hx e he hf=> (update_of_ne (fun (h':e=p)=> hx (h' ▸ (show e.1∈ X from he))) W V).symm
lemma spread (h:Stab o U V) (s:Signed) : Stab ((turnSites s 0).symm o) (pull s 0 U) (pull s 0 V):= by
    intro i hi; apply agrees_pull; refine h _ (fun hz=> ?_); obtain ⟨j,hj,e⟩:= Finset.mem_image.mp hz; exact hi (Eq.recOn e (show (turnSites s 0).symm ((turnSites s 0) j) ∈ i by simp [hj])) -- dangerous
lemma halo_far (x:Site n)(m:ℕ)(he:m< separation o x) : o∉ halo m {x}:=by
   intro hg; obtain ⟨_,hp,ht⟩:= halo_spec.mp hg; rw [Finset.mem_singleton.mp hp,separation_comm] at ht; omega
lemma far_face (s:Face (Per n))(hp:Stab o U V) (he:2< separation o s.1) : faceValue U s=faceValue V s:= WilsonStartup.face_local _ U V (hp _ fun hx=> (Nat.not_lt_of_le (visit_near s hx)) he)
lemma flag_turns (t:ℝ)(i: Site n)(hp:Stab o U V)(he:4< separation o i) : i∈ flags t U ↔ i∈flags t V:=by
   simp only [flags_spec]; apply exists_congr; intro p; by_cases hv:i∈ touched p
   · rw [far_face p hp]; have hx:= visit_near p hv; rw [separation_comm i] at hx; have ht:= separation_triangle o p.1 i; omega
   simp [hv]
variable {d:Clip}{p:BudgetPoint}
lemma kept_turn (h:WilsonStartup.Decent d p) (i:Site n) (hp:Stab o U V)(he:p.B < separation o i): PathData.kept d p.threshold i U ↔ PathData.kept d p.threshold i V :=
    AnalyticBridge.VerifiedReset.kept_local d h i (hp _ (halo_far i p.B he))
-- vacuum near score sup paid: A on calm, B arbitrarily
open RG.PathData
include R
variable {clip:Clip}{p:BudgetPoint}(H: R.path.Bounds R.clip σ C T)(x:Face (Per n))
include H
local notation "d"=> R.path
private lemma global_e (U:Config G n): ‖R.path.ell U x‖≤ C*2:=by
    have hs := (H.rows x.2).2.1
    let g(i:ℕ):= |(R.path.row x.2 i).1| *Real.exp (σ*(R.path.row x.2 i).2.length)
    have he := (R.path.ell_dominated H x).absolute U
    have hg(i) : ‖R.path.ellTerms x i U‖≤ g i *2 := by
       rw [ellTerms,norm_smul]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg H.width.le (by positivity : 0≤((R.path.row x.2 i).2.length:ℝ))))) (Slot.eval_norm ..) (norm_nonneg _) ((H.rows x.2).1 i)
    apply le_trans (norm_tsum_le_tsum_norm he) _; refine (he.tsum_le_tsum hg (hs.mul_right _)).trans ?_
    rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (H.rows x.2|>.2.2) zero_le_two
lemma mean_stab (h:Stab o U V) : ‖R.path.ell U x-R.path.ell V x‖ ≤ (C*4)*Real.exp (-σ*separation o x.1):=by
    let A:=R.path.row x.2; let g(i:ℕ):=|(A i).1| *Real.exp (σ*(A i).2.length); let m:= separation o x.1; let a:=Real.exp (-σ*m); have ht:= R.path.ell_dominated H x; have hm(i): ‖R.path.ellTerms x i U-R.path.ellTerms x i V‖ ≤ g i*(4*a):=by
       by_cases hx: (A i).2.length < m
       · have h0 : R.path.ellTerms x i U=R.path.ellTerms x i V:=congr_arg ((A i).1 • ·) (AnalyticBridge.VerifiedReset.slot_reads _ _ _ _ (h _ fun H=> (AnalyticBridge.VerifiedReset.slot_length _ _ H).not_gt hx))
         rw [h0,sub_self,norm_zero]; exact mul_nonneg (H.rows x.2|>.1 i) (mul_nonneg (by norm_num) (Real.exp_pos _).le)
       have hA(v : Config G n): ‖R.path.ellTerms x i v‖≤|(A i).1| *2:= by
          rw [ellTerms,norm_smul]; exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (norm_nonneg _)
       have hv : 1 ≤ Real.exp (σ*(A i).2.length)*a:=by
          unfold a; rw [← Real.exp_add]; apply Real.one_le_exp; push Not at hx; have hi := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hx) H.width.le; linarith
       exact (norm_sub_le ..).trans ((add_le_add (hA U) (hA V)).trans (le_trans (le_mul_of_one_le_right (show 0≤|(A i).1| *2+|(A i).1| *2 by positivity) hv) (le_of_eq (by unfold g; ring))))
    let e i:=R.path.ellTerms x i U-R.path.ellTerms x i V; have hf:= ((H.rows x.2).2.1|>.mul_right (4*a)); have he := hf.of_nonneg_of_le (g:=fun i=>‖e i‖) (fun i=> norm_nonneg _) hm
    unfold ell; rw [← (ht.summable U).tsum_sub (ht.summable V)]
    refine (norm_tsum_le_tsum_norm he).trans ((he.tsum_le_tsum hm hf).trans ?_); rw [tsum_mul_right]; exact (mul_le_mul_of_nonneg_right (H.rows x.2 |>.2.2) (mul_nonneg (by norm_num : 0 ≤ (4:ℝ)) (Real.exp_pos _).le)).trans_eq (mul_assoc ..).symm
lemma base_stab (hp:Stab o U V)(hq:R.p.B < separation o x.1)(hc:Decent R.clip R.p): |R.path.baseTerm R.clip R.p U x-R.path.baseTerm R.clip R.p V x| ≤ (C*4)*(C*2)*Real.exp (-σ*separation o x.1):=by
    rw [baseTerm,baseTerm,far_face _ hp (hc.radius.trans_lt hq)]; rw [kept_turn hc _ hp hq,add_sub_add_left_eq_sub]; split
    next h=>
      rw [← sub_div, abs_div, abs_of_nonneg (zero_le_two (α:=ℝ)), sq_sub_sq, abs_mul]
      have hv:|‖R.path.ell U x‖-‖R.path.ell V x‖|≤ _ := abs_norm_sub_norm_le (R.path.ell U x) (R.path.ell V x)
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]; rw [div_le_iff₀ (by norm_num: 0 < (2:ℝ))]
      have hi: ‖R.path.ell U x‖+‖R.path.ell V x‖≤ C*2+C*2:=add_le_add (global_e H x U) (global_e H x V)
      refine (mul_le_mul hi (hv.trans (mean_stab H x hp)) (abs_nonneg _) ((add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hi)).trans_eq ?_; ring
    next h=> simp only [sub_zero, abs_zero]; have hf := le_trans (norm_nonneg _) (global_e H x U)
             have hi:C≥0:=by linarith
             positivity
end YM.MSbar.Heath
