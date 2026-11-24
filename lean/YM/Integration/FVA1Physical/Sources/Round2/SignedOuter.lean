import YM.Integration.FVA1Physical.Sources.Round2.SignedHost
import YM.Integration.FVA1Physical.Sources.Round2.ScalarCollar
import YM.Integration.FVA1Physical.Sources.Round2.TwoPhysicalFields

/-! Transport the whole signed physical posterior through an arbitrary rough
exterior by first removing its full forced share in the outer expectation.
Only the local copied chart is compared to the independent polynomial. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels MSbar MSbar.Bulk
open Push Push.AbsoluteSums Push.GridApprox.Attach RGComparison.Core16.Spool
open YM.Integration.FVA1Physical.Wilson
open scoped BigOperators Classical
variable {G:Gauge} {c n:Side} {S:StepData c n} {R:Rep G n} {F:Frame G 0}

theorem signed_outer (Q:Coefficient F n) (z:Site n) (D:SectionData F) {P:Hol G} (form:Q.Format z P R)
    {κ M t K σ C δ Λ w B err rare:ℝ} (fund:Q.remBound z R κ M)
    (O:Config G c) (adm:Admitted O R S σ C δ Λ w) (pos:∀ W,0 < R.eval W)
    (storm:Psalm S R t K) (clean:flags t O=∅) (K0:0 ≤ K)
    (φ bank:Config G n→ℝ) (mφ:Measurable φ) (mb:Measurable bank)
    (bound:∀ U,|φ U| ≤ B) (exactness:∀ U,(φ U:ℂ)=Q.exponentialEntry z D R U+forcedShare Q R U)
    (H:Set (Config G n)) (hH:MeasurableSet H) (outside:chance S R O Hᶜ ≤ rare)
    (copy:Config G n → Config G n) (mc:Measurable copy) (k:Config G n→Site n→G.El) (r:ℕ)
    (inside:∀ U∈H,flags R.p.threshold (copy U)=∅ ∧
      Agrees (halo (r*leg R.p.B+8) {z}) (gauge (k U) U) (copy U) ∧
      |φ (copy U)-bank (copy U)| ≤ err) (he:0 ≤ err) :
    |expect S R O φ-expect S R O (H.indicator (bank ∘ copy))| ≤
      K*(κ*M)+(B+M)*rare+2*Real.exp (-R.p.supportExponent*r)*M+err := by
  let Rg:=fun U=>(Q.exponentialEntry z D R U).re
  let Fr:=fun U=>(forcedShare Q R U).re
  have eq (U):φ U=Rg U+Fr U:=congrArg Complex.re (exactness U)
  have eR:=centered_entry Q form fund D
  have base:flags R.p.threshold (1:Config G n)=∅:=by
    apply voids (r:=R.p.threshold) _ le_rfl
    intro e _
    change G.chord 1 ≤ _
    rw [G.chord_one];exact div_nonneg R.p.threshold_pos.le (by norm_num)
  have ref:φ 1=Rg 1 := by
    rw [eq];dsimp only [Fr];rw [empty_share Q 1 base,Complex.zero_re,add_zero]
  have M0:0 ≤ M:=by obtain ⟨a,b,ha,hb,ab,_⟩:=fund;exact (add_nonneg ha hb).trans ab
  have B0:0 ≤ B:=(abs_nonneg _).trans (bound 1)
  have cash:∀ U,|Rg U| ≤ B+M:=by
    intro U
    have gap:|Rg U-Rg 1|≤M:=by
      simpa only [Complex.sub_re,Rg,eR.1] using (Complex.abs_re_le_norm _).trans (eR.2.2.2 U)
    have center:|Rg 1|≤B:= ref ▸ bound 1
    calc |Rg U|=|Rg U-Rg 1+Rg 1| := by rw [sub_add_cancel]
         _ ≤ _ := (abs_add_le ..).trans ((add_le_add gap center).trans_eq (add_comm ..))
  have env:Envelope Rg:=⟨Complex.continuous_re.measurable.comp eR.2.1,B+M,cash⟩
  have envf:Envelope Fr:=by
    have fr:Fr=φ-Rg:=funext fun U=>by change Fr U=φ U-Rg U;linarith only [eq U]
    rw [fr]
    exact ⟨mφ.sub env.meas,_,fun U=>(abs_sub ..).trans (add_le_add (bound U) (cash U))⟩
  let E:=expect S R O
  have split:E φ=E Rg+E Fr:=by
    have h:=e_sum O adm env envf
    rw [show Rg+Fr=φ from funext fun U=>(eq U).symm] at h
    exact h
  have pay:|E φ-E Rg| ≤ K*(κ*M):=by
    rw [split,add_sub_cancel_left]
    exact signed_host_posterior S R Q z form fund O adm pos storm clean K0 false
  have cut:=expect_on_chart O hH adm Rg env.meas (add_nonneg B0 M0) cash outside
  let s:=2*Real.exp (-R.p.supportExponent*r)*M
  have s0:0 ≤ s:=mul_nonneg (mul_nonneg zero_le_two (Real.exp_nonneg _)) M0
  have chart:|E (H.indicator (bank ∘ copy))-E (H.indicator Rg)| ≤ s+err:=by
    have restricted:Envelope (H.indicator Rg):=Envelope.piece hH env (Envelope.const 0)
    apply expect_difference adm ((mb.comp mc).indicator hH) restricted
    intro U
    by_cases hit:U∈H
    swap
    · simpa only [Set.indicator_of_notMem hit,sub_self,abs_zero] using add_nonneg s0 he
    obtain ⟨quiet,agree,win⟩:=inside U hit
    have same:φ (copy U)=Rg (copy U):=by rw [eq];dsimp only [Fr];rw [empty_share Q _ quiet,Complex.zero_re,add_zero]
    have near:=scalar_regular_collar R Q z D form fund r (gauge (k U) U) (copy U) agree
    have gap:|Rg U-Rg (copy U)| ≤ s:=by
      rw [eR.2.2.1 (k U) U] at near
      exact (Complex.abs_re_le_norm _).trans near
    rw [Set.indicator_of_mem hit,Set.indicator_of_mem hit,Function.comp_apply,abs_sub_comm]
    exact (abs_sub_le _ (Rg (copy U)) _).trans (add_le_add gap (same ▸ win))
  have wanted:|E (H.indicator Rg)-E (H.indicator (bank ∘ copy))| ≤ s+err:=(abs_sub_comm ..).le.trans chart
  exact (abs_sub_le _ (E Rg) _).trans ((add_le_add pay ((abs_sub_le _ (E (H.indicator Rg)) _).trans
    (add_le_add cut wanted))).trans_eq (by dsimp only [s];ring))

end YM.Integration.FVA1Physical.Round2.Curvature
