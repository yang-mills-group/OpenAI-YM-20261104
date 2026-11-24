import YM.OPE.Compatible.Ash.Need
import YM.Pert.Fourier.Visits
/-!
# ∞ qualitative sufficient, even periods
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}
def hull : List Axis→Cover→ℝ
 | [],x=> Pert.Cellular.coverLine x
 | i::D,x=> hull D (x+step i)-hull D x
lemma calm (M:ℕ→Side)(he:∀ᶠ i in atTop, Even (M i).val)(hp:Tendsto (fun i=>(M i).val) atTop atTop)(a:Cover)(D:List Axis): Tendsto (fun i=> mildX D (wrap (M i) a)) atTop (𝓝 (hull D a)):=by
   induction D generalizing a with
   | nil=>simp_rw [mild_tip]; rw [Metric.tendsto_nhds]; intro ε hε
          obtain ⟨C,hC,A,hA,H⟩:=Pert.Cellular.toroid_cost a; obtain ⟨r,hr,hx⟩:∃ r:ℝ, 0<r∧r≤1 ∧ C*r^2<ε:=by
              let r:=min ((ε/(C+1))/2) (1:ℝ) -- parse
              have hh:0 < r:=by unfold r; positivity
              have hu:r ≤ 1:=min_le_right ..; refine ⟨r,hh,hu,?_⟩; 
              have h := (show r≤ (ε/(C+1))/2 from min_le_left ..); have hc:0<C+1:=add_pos_of_nonneg_of_pos hC zero_lt_one
              have ht:2*r ≤ ε/(C+1):=by linarith
              have hy:2*r*(C+1) ≤ ε:=(le_div_iff₀ hc).1 ht
              nlinarith [mul_nonneg hC (show 0≤r-r^2 from by nlinarith only [hu,hh])]
          have hy: Tendsto (fun i=>((M i).val:ℝ)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hp)
          let f(i):=(M i).val; filter_upwards [he, (hy.const_mul 8).eventually (ge_mem_nhds (show 8*0<r from by linarith)), ((((hy.const_mul A).div_const (r^4)).const_add (C*r^2)).eventually (gt_mem_nhds (show _ from by simpa only [mul_zero,zero_div,add_zero] using hx.2)))] with i hi hh hv
          rw [dist_eq_norm,Pert.Cellular.weighted a _ hi, hull,Pert.Cellular.cover_interp]; exact lt_of_le_of_lt (H hi hr hx.1 hh) hv
   | cons i D ih=>simp_rw [mild_more,← wrap_step _ i, ←map_add, hull]; exact (ih (a+step i)).sub (ih a)
def nextP (U:Gloam): Gloam where
  M i:= U.M (i+1)
  q:=U.q
  growth:=U.growth
  law i:=U.law (i+1)
lemma coal (p:ℕ→ℝ)(h:Cleared (nextP U) p):Cleared U p:=by
   intro m hm; obtain ⟨a,h⟩:= h m hm; obtain ⟨C,hC,H⟩:=h
   let b:=fun i:ℕ=> (U.q'^i)⁻¹ • a i; refine ⟨b,C,hC,fun i=>?_⟩
   apply le_trans (b:=C*((nextP U).h i)^m) ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((nextP U).h_pos _).le (U.anti (show i≤ i+1 from by omega)) _) hC)
   convert! H i using 1; rw [Pi.sub_apply,Pi.sub_apply,billX,billX]; congr 2; apply Finset.sum_congr rfl; intro j _; unfold coral b; rw [smul_smul, show (nextP U).h i=U.h i/U.q' from U.h_succ i]; rw [div_pow,div_eq_mul_inv]
lemma inhabitC (U:Gloam)(a:Cover)(D:List Axis)(he:∀ᶠ i in atTop,Even (U.M i).val):
  Cleared U (fun i=>(U.h i^(D.length+2))⁻¹*(mildX D (wrap (U.M i) a)-hull D a)):=by
    let A:=U.ratio; let f(i):= mildX D (wrap (U.M i) a); let Y:ℕ:=D.length+2
    let t(p:Site U.q)(i:ℕ): Site ((nextP U).M i):=(rye (A i)).embed p
    have ht(p:Site U.q): Drone (nextP U) (t p):=by
         intro i; let w:= ((nextP U).ratio i); change wrap _ ((U.M (i+1)).val • Lattice.lift p) = w.embed (wrap _ ((U.M i).val • Lattice.lift p)); rw [w.embed_wrap]; congr 1; rw [U.law i,mul_comm _,mul_smul]; rfl
    let R(p:Site U.q)(i:ℕ):= joint (U.h (i+1)) D (t p i+wrap _ a)
    let B:Finset (Site U.q):=Finset.univ.erase 0
    let c:ℝ:=(U.q'^Y)⁻¹
    let g(p:Site U.q)(i:ℕ):=c*(R p i).re
    have hc(p:Site U.q)(hp:p∈B): Cleared U (g p):=by
        apply (coal (g p)); refine Cleared.glu (c • Complex.reCLM) (clear_jointX (ht p) ?_ D a) -- defeq
        let W:= rye (U.ratio 0); refine fun H=> (Finset.mem_erase.mp hp).1 (W.embed_injective  (a₂:=0) ?_); rw [show W.embed p=0 from H]; exact (W.root.map_zero).symm
    let G:=∑ p∈B,g p
    have hy(i):f i-f (i+1)=U.h i^Y • G i:=by
       unfold f; rw [aliasX (U.ratio i), ← Finset.sum_erase_add _ _ (a:=0) (by simp),show (rye (U.ratio i)).embed 0=0 from (rye _).root.map_zero, zero_add,add_sub_cancel_right]; unfold G; rw [Finset.sum_apply,Finset.smul_sum]; exact Finset.sum_congr rfl (fun p _=> by unfold g R; rw [full_X _ _ _ (U.h_pos (i+1)),U.h_succ]; change (U.h i/U.q')^Y*(joint _ D _).re=U.h i^Y*(c*(joint _ D (_)).re); unfold c; rw [div_pow,div_eq_mul_inv, mul_assoc]; rfl
       )
    exact gap (n:=Y) (M:=ℝ) (by unfold Y;omega) (Cleared.tally B g hc) _ (calm (U.M) he U.sides a D) hy
end YM.OPE.Balsam
