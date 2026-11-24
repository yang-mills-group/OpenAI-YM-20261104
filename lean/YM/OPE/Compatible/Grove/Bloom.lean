import YM.OPE.Compatible.Grove.Yew
/-! Raw Earning and row operations. Accounts for any eventual dynamical story. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
-- purchased kernels. report only t-ray bounded INR. Preserve along Torus; any scribe from family.
structure Earn (r m:ℕ) (A:CoverConfig G→ℝ)(p:Script (Shade G) r) (x:ℝ):Prop where
    credit : soot m p x
    tandem : p.sorted
    fees (u:fieldX (Shade G))(hp:Quiet u 0) : ContDiff ℝ ∞ (fun t:ℝ=> A (lotU (t • u))) ∧ WardBin.leading r (fun t:ℝ=> A (lotU (t • u)))=wholeX p (fun _=>u)
lemma stamped (P:I→ Chant G n)(x:I→ℝ)(v:fieldX (Shade G))(h:saturate P x s U)(hp:Quiet v 0)(hs:0<s)(hv:∀ i, moderateX (P i) D)(he:0≤D):
    ContDiff ℝ ∞ (fun t:ℝ=> rhythm P x (lotU (t • v))):=by
    obtain ⟨z,hz,g⟩:=staffQ v hp; choose c hc H using fun j=> cashBill G n _ _ _ hs hz he j; let f(i:I)(t:ℝ):= x i*verseX (P i) (lotU (t • v))
    have ht(i): ContDiff ℝ ∞ (f i):=contDiff_const.mul ((cash_smooth (P i) v).of_le le_top)
    exact contDiff_tsum ht (fun k _=> h.2.1.mul_left (c k)) fun k i t _=>by
        rw [show iteratedFDeriv ℝ k (f i) t=x i • iteratedFDeriv ℝ k (fun y:ℝ=>verseX (P i) (lotU (y • v))) t from by change iteratedFDeriv ℝ k (x i • fun y:ℝ=>verseX (P i) (lotU (y • v))) t=_; exact iteratedFDeriv_const_smul_apply ((cash_smooth (P i) v).contDiffAt.of_le le_top),norm_smul,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact (mul_le_mul_of_nonneg_left (H k _ _ (hv i) (fun j _=>g j) t) (norm_nonneg _)).trans_eq (by ring)
lemma sphereTurns (G:Gauge)(D s:ℝ)(hv:0 ≤ D)(hs:0<s)(m r n:ℕ):∃ A:ℝ,0 ≤ A∧∀ (P:I→Chant G n)(x:I→ℝ)(U:ℝ), saturate P x s U→(∀ i,moderateX (P i) D)→ Earn r m (rhythm P x) (timbre P x r) (A*U):=by
     obtain ⟨A,ha,H⟩:= totalBudget (I:=I) G m r n s D hs hv; exact ⟨A,ha,fun p x U hx h=>⟨H p x U hx h,timbreT p x r,fun v hp=> ⟨stamped p x v hx hp hs h hv,rimline hx hs h hv r hp⟩⟩⟩
lemma pricerise {c:ℝ}{A:CoverConfig G→ℝ}{p:Script (Shade G) r}(h:Earn r m A p c)(hp:c≤ U): Earn r m A p U:= {h with credit := h.credit.tips hp}
lemma safeEarn {A:CoverConfig G→ℝ}{p:Script (Shade G) r}(h:Earn r m A p U): Summable p:= sootS h.credit
variable {A C:CoverConfig G→ℝ}{p q:Script (Shade G) r}
lemma earnSum (h:Earn r m A p U)(hx:Earn r m C q b): Earn r m (A+C) (p+q) (U+b):=by
    refine ⟨h.credit.splits hx.credit (fun i=> zero_le_one.trans (payer m _)),fun i=>by rw [show swing i (p+q)= swing i p+swing i q from rfl,h.tandem,hx.tandem],fun v hp=>?_⟩
    obtain ⟨hs,hB⟩:= h.fees _ hp; obtain ⟨hv,hQ⟩:= hx.fees _ hp; refine ⟨hs.add hv,?_⟩
    rw [manyX (k:=fun _=>0) h.credit hx.credit (fun _=>hp) (by simp),← hB,← hQ]; unfold WardBin.leading; rw [← smul_add]; congr 1; exact iteratedDeriv_add (hs.of_le (show _ from (WithTop.coe_le_coe.mpr le_top))|>.contDiffAt) (hv.of_le (show _ from (WithTop.coe_le_coe.mpr le_top))|>.contDiffAt) -- change
lemma earnScale (h:Earn r m A p U) (k:ℝ):Earn r m (k • A) (k • p) (‖k‖*U):=by
   refine ⟨h.credit.scale_line k,fun i=>show _=_ from congr_arg (fun v=> k • v) (h.tandem i),fun v hp=>?_⟩
   obtain ⟨hb,H⟩:=h.fees _ hp; refine ⟨hb.const_smul k,?_⟩; rw [scaleX,← H]; unfold WardBin.leading; let y(t:ℝ):=A (lotU (t • v)); rw [show (fun t:ℝ=> (k • A) _)=k • y from rfl, iteratedDeriv_const_smul ((show ContDiff ℝ (r: WithTop ℕ∞) y from hb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]; exact smul_comm ..
lemma earnSet (f:Finset I)(F:I→CoverConfig G→ℝ)(p:I→Script (Shade G) r)(X:I→ℝ)(h:∀ i∈f,Earn r m (F i) (p i) (X i)): Earn r m (∑ i∈f,F i) (∑ i∈f,p i) (∑ i∈f,X i):=by
   induction f using Finset.induction_on with
   | empty=>
      rw [sum_empty,sum_empty,sum_empty]; refine ⟨Sack.zero le_rfl _,fun _=>rfl,fun v _=>⟨contDiff_const,?_⟩⟩; simp [WardBin.leading,wholeX]
   | insert i f hi ih=> rw [sum_insert hi,sum_insert hi,sum_insert hi]; exact earnSum (h _ (mem_insert_self ..)) (ih (fun j hj=> h _ (mem_insert_of_mem hj)))
end Script
end YM.OPE.Flume
