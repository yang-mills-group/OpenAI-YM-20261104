import YM.Qlocal.Parabola.Seal
import YM.Qlocal.Printed
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Parabola
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Bank Push.AbsoluteSums MergeProof
open scoped Topology ContDiff BigOperators Classical
open Publishing
variable {G:Gauge}{n:Side}{t:ℝ}{P:BudgetPoint}{ι Ω V:Type}[DecidableEq V]{R:Census V}
    {A:Activities G n} {s:V→Support n}{X Y:Support n}{N: ℝ}{p q: Poly R}
set_option quotPrecheck false
-- angular as Budget.Domain.Unfold.limited.Local.CP.Ge.Research keep however many stencil addresses.
structure Articles (X:Support n)(f:Config G n→Poly R) (s:V→Support n)(t:ℝ): Prop where
   travel : UsesFinal t X f
   visible (v:R.Mode): Measurable (fun U=> (f U).part v)
   worth : GaugeInvariant f
   owns (U) : Publishing.lives (f U) X s -- ν.Size true
lemma lives_zero (X:Support n)(s:V→Support n): lives (0:Poly R) X s:= fun _ hi=> False.elim (hi rfl)
lemma lives_add (h:lives p X s)(he:lives q X s): lives (p+q) X s:= by
 intro v hv; by_cases hp:p.part v=0; swap; · exact h v hp
 rw [Poly.part_plus,hp,zero_add] at hv; exact he v hv
namespace Articles
variable {f g:Config G n→Poly R}
protected lemma zero (X:Support n)(s:V→Support n)(t:ℝ): Articles X (0: Config G n→Poly R) s t := ⟨fun _ _ _ _=>rfl,fun _=>measurable_const,fun _ _=>rfl, fun _=> lives_zero X s⟩
protected lemma one (X:Support n)(s:V→Support n)(t:ℝ): Articles X (1: Config G n→Poly R) s t := ⟨fun _ _ _ _=>rfl,fun _=>measurable_const,fun _ _=>rfl, fun _=> LivesOne X s⟩
protected lemma add (h0:Articles X f s t)(h1: Articles X g s t):Articles X (f+g) s t:= ⟨fun _ _ hs ht=> congr_arg₂ (·+·) (h0.travel _ _ hs ht) (h1.travel _ _ hs ht),fun i=>(h0.visible i).add (h1.visible i), fun k U=> congr_arg₂ (·+·) (h0.worth k U) (h1.worth k U), fun U=> lives_add (h0.owns _) (h1.owns _)⟩
protected lemma mul (h0:Articles X f s t)(h1:Articles X g s t): Articles X (f*g) s t:= by
 refine ⟨fun i U hs ht=> congr_arg₂ (·*·) (h0.travel _ _ hs ht) (h1.travel _ _ hs ht),fun i=>?_,fun k U=> congr_arg₂ (·*·) (h0.worth k U) (h1.worth k U),fun U=> lives_times (h0.owns U) (h1.owns U)⟩
 simp_rw [Pi.mul_apply,Poly.part_mul]; refine Finset.measurable_fun_sum _ fun i _=> Finset.measurable_fun_sum _ fun j _=> ?_; split; exact (h0.visible _).mul (h1.visible _); exact measurable_const
protected lemma prod {F: ι→ Config G n→ Poly R}(s':Finset ι)(h:∀ i∈s',Articles X (F i) s t):Articles X (∏ i∈s',F i) s t:= by
 induction s' using Finset.cons_induction with
 | empty => rw [Finset.prod_empty]; exact Articles.one ..
 | cons a s' hp ih => rw [Finset.prod_cons]; exact (h a (by simp)).mul (ih fun i hi=> h _ (Finset.mem_cons.mpr (Or.inr hi)))
lemma enlarging (h:Articles X f s t)(he:X⊆Y): Articles Y f s t:= ⟨Work.H03.reads_larger he h.travel,h.visible,h.worth,fun U=>(h.owns U).one he⟩
lemma territory (p:Config G n → Prop)(hp: UsesFinal t X p)(h0:GaugeInvariant p)(he:MeasurableSet {U|p U})(h:Articles X f s t): Articles X (fun U=> if p U then f U else 0) s t:=by
 refine ⟨fun i j hs ht=> if_congr ((congr_arg id (hp i j hs ht)).to_iff) (h.travel i j hs ht) rfl, ?_,fun k U=> if_congr ((h0 k U).to_iff) (h.worth k U) rfl,fun U=>?_ ⟩
 · intro x; simp_rw [apply_ite (fun v:Poly R=> v.part x)]; exact Measurable.ite he (h.visible x) measurable_const
 split; exact h.owns U; exact lives_zero X s
end Articles
-- ancillary mask match entrances.K.Ens
variable {K I: Ω→ℕ→ Config G n→Poly R}{S : Corrections G n}
  (hK:∀ x i,Articles ((A.forced i).support) (K x i) s P.threshold)
  (hI:∀ x i,Articles (S.region i) (I x i) s P.threshold)
  (hp: A.ForcedFamily P)
local notation "L"=> Bank.lifted (A:=A) S P
include hp hK hI
lemma canopy (x:Ω)(i:ℕ): Articles (page A S i).support (L (K x) (I x) i) s P.threshold := by
 let T:= page A S i; let F' := Sum.elim (K x) (I x); have hh i' : Articles (S.area A i') (F' i') s P.threshold:= by cases i'; exact hK _ _; exact hI _ _
 let f(U:Config G n)(j):= F' j U; have he (U:Config G n): Sum.elim ((K x) · U) ((I x) · U)=f U:= by ext1 i; cases i <;> rfl
 have hX: L (K x) (I x) i = (fun U=> if T.eligible P.threshold U then (∏ j∈parts A S i,F' j) U else 0):= by funext U; unfold lifted outKey; rw [he,Finset.prod_apply] -- syntax
 have hr(u:Site n→G.El)(U:Config G n): T.extraTest (Lattice.gauge u U) ↔ T.extraTest U:= by change (∀ j∈(parts A S i).toLeft, _) ↔ (∀ j∈(parts A S i).toLeft,_); simp_rw [hp.symtest]
 have hd : UsesFinal P.threshold T.support T.extraTest:= by intro U V he hk; exact propext ⟨fun H j hj=> (Work.H03.reads_larger (sub_cover_old A S hj) (hp.reads_test _) _ _ he hk) ▸ H j hj, fun H j hj=>(Work.H03.reads_larger (sub_cover_old A S hj) (hp.reads_test _) _ _ he hk).symm ▸ H j hj⟩
 have hB : MeasurableSet {U|T.extraTest U}:= by
   change MeasurableSet {U:Config G n| ∀ j ∈ (parts A S i).toLeft, (A.forced j).extraTest U}; simp only [Set.setOf_forall]; exact MeasurableSet.biInter (Set.to_countable _) fun j _=> hp.meas_test j
 rw [hX]; exact Articles.territory _ (Work.H03.eligible_reads P.threshold T hd) (fun u U=> propext (Work.H03.eligible_gauge P.threshold _ u U (hr u U))) (Work.H03.eligible_measurable _ _ hB) (Articles.prod _ fun j hj=> (hh j).enlarging (subset_biUnion_of_mem (S.area A) hj))
omit hp
variable [Fintype V]
  (he:∀ x i U,(K x i U).part R.quiet=(A.K i U:ℂ))
  (ht:∀ x i U,K x i U≠0→ (A.forced i).eligible P.threshold U)
  (hψ:∀ x i U,(I x i U).part R.quiet=0)
  (C: Bank A P.threshold)
include hp he ht hψ
local notation "f[" i "]"=> C.store S P (K i) (I i)
lemma equipped (x:Ω)(i:ℕ): Articles (A.forced i).support (f[x] i) s P.threshold ∧ ∀ U, (f[x] i U).part R.quiet= (A.K i U:ℂ)∧ (f[x] i U≠0→ (A.forced i).eligible P.threshold U) := by
 let F:= L (K x) (I x); let J:= C.fresh S F; have h : (f[x] i)=K x i+J i:= rfl
 rw [h]; by_cases h:∃ j, Bank.opened (A:=A) S j ∧ C.reticket S j=i; swap; · rw [show J i=0 from Bank.invalid C _ _ h,add_zero]; exact ⟨hK ..,fun U=>⟨he x i U,ht x i U⟩⟩ -- hK implicit applications? Articles structure Prop
 obtain ⟨j,hj,rfl⟩:=h; rw [show J _=F j from C.valid _ _ hj]; refine ⟨(hK ..).add ?_,fun U=>⟨?_,?_⟩⟩
 · rw [Bank.reticket_area]; exact canopy hK hI hp x j -- order
 · rw [Pi.add_apply, Poly.part_plus,he,add_eq_left]; unfold F lifted outKey; split; swap; · exact Poly.part_nil _
   rw [MergeProof.Accent.shockProd₀]; obtain ⟨k,hk⟩:=hj; exact Finset.prod_eq_zero (Finset.mem_toRight.mp hk) (hψ x k U)
 intro hz; by_contra hx; have hp := not_not.mp (mt (ht x (C.reticket S j) U) hx); apply hz; rw [Pi.add_apply,hp,zero_add]; exact if_neg (fun he=> hx (C.reticket_eligible S he))
end YM.Qlocal.Parabola
