import YM.RGComparison.Core16.Silk.Cord
/-!
# A hierarchical spatial comparison operator for the Silk recurrence

This proves 'defect activates only at coincidence' equation for the generated `Roll` family,
iterated at arbitrary finite degrees in same germ, entirely on coeff arrays (post pointwise proof
with common λ cost already supplied from Lens). No contact normals inferred; use within seams.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D L : Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L]
variable {X:Shelf G A D} (P:Planet X S ι k T)(H:P.Steady) (i:Wire G ι)

variable (p:Stuff G ι L)(ψ:(L→ G.Color)→ℝ)
    (R U: Rail G ι→Roll)

omit [Fintype ι] in
lemma night_sub w n: night p ψ (R-U) w n = night p ψ R w n-night p ψ U w n:=by simp [night,smul_sub,sum_sub_distrib]
omit [Fintype ι] in
lemma night_mul (C : Roll) w n: night p ψ (fun u=> R u * C) w n= night p ψ R w n * C := by unfold night; rw [sum_mul]; exact sum_congr rfl (fun i _=> (smul_mul_assoc ..).symm)
lemma day_sub (V W:ℕ→Roll)(w:ℕ):day (fun i=> V i-W i) w =day V w-day W w:= by ext; unfold day dawn shiftFront; simp [nth,mul_sub,sum_sub_distrib]
lemma day_mul (V:ℕ→Roll)(w:ℕ)(C:Roll):day (fun i=> V i * C) w = day V w * C:= by
   ext n; change nth n _= nth n _; rw [vogue (t:=n) (w:=w) (Nat.le_add_left ..)] -- nth abbrev issue
   have h:dawn (fun i=>V i*C) w n=dawn V w n*C:= by unfold dawn shiftFront; rw [sum_mul]; exact sum_congr rfl (fun i _=> (mul_assoc ..).symm)
   rw [h]; simp only [nth,PowerSeries.coeff_mul]; refine sum_congr rfl (fun i hi=>?_); have he:= mem_antidiagonal.mp hi; exact congr_arg (fun z=>z*PowerSeries.coeff _ C) (vogue (show i.1≤w+n by omega)).symm

omit [Fintype T] [Fintype D] [Fintype A] in
lemma subtracting w : stepLaw P i (R-U) w=stepLaw P i R w-stepLaw P i U w:=by simp only [stepLaw,Pi.sub_apply,smul_sub,sum_sub_distrib]
omit [Fintype ι] [Fintype T] [Fintype A] in
lemma task_sub w: taskBill P i (R-U) w =taskBill P i R w-taskBill P i U w := by
    unfold taskBill windDown wingK due cheaper; have he {p:Stuff G ι Unit} (ψ:(Unit→G.Color)→ℝ) (u:Rail G ι): night p ψ (R-U) u=fun i=>night p ψ R u i-night p ψ U u i:=funext fun i=> night_sub p ψ R U u i
    simp_rw [he,night_sub,day_sub]; simp only [sum_sub_distrib,Pi.sub_apply,smul_sub]; abel

omit [Fintype T] [Fintype D] [Fintype A] in
lemma products (C: Roll)(w): stepLaw P i (fun v=> R v*C) w = stepLaw P i R w*C:= by
    unfold stepLaw; rw [sum_mul]; exact sum_congr rfl (fun i _=> (smul_mul_assoc ..).symm)

omit [Fintype ι] [Fintype T] [Fintype A] in
lemma consign (C:Roll)(w) : taskBill P i (fun v=> R v*C) w=taskBill P i R w*C:=by
    unfold taskBill windDown wingK due cheaper; have he {p:Stuff G ι Unit} (ψ:(Unit→G.Color)→ℝ) (u:Rail G ι): night p ψ (fun v=>R v *C) u=fun i=>night p ψ R u i*C:=funext fun i=> night_mul p ψ R C u i
    simp_rw [he,night_mul,day_mul]; simp only [←smul_mul_assoc,sub_mul,sum_mul]

-- Sacramental relation for retaining appended stationary words across budgets
-- (zero Gap W.T in Vir order uses this!) 

omit [Fintype ι] in
lemma night_move (u w:Rail G ι)(n:ℕ): night p ψ (fun v=> R (v++w)) u n=night p ψ R (u++w) n:=by unfold night; simp_rw [List.append_assoc]

omit [Fintype ι] in
lemma wing_lost {i j: Wire G ι} (h:i.1≠j.1)(u) : wingK R u i j=0:=by
     unfold wingK scorecard; rw [if_neg h,show night (guide i) (wing G none) R u=0 from funext fun y=> nap (L:=Unit) y _ _ _,day_zero]

section list
-- abstract to avoid proof relevance in fins
variable {E : Type*} {F: Type*} [AddCommMonoid F]
private def winds (A:List E)(B:E→ List E→F):= ∑ k:Fin A.length,B A[k] (A.eraseIdx k)
private lemma winds_mix (B:E→List E→F) (u w:List E):
    winds (u++w) B = winds u (fun i v=> B i (v++w)) + winds w (fun i v=> B i (u++v)) := by
   let W:=u++w; let h:W.length=u.length+w.length:= List.length_append
   let e := finCongr h
   let f (k:Fin W.length):= B W[k] (W.eraseIdx k); have hh: winds W B=∑ i, f (e.symm i) := by
      refine (sum_equiv e ?_ ?_); · simp
      intro i _; change f i=f _; rw [e.symm_apply_apply]
   rw [show u++w=W from rfl,hh,Fin.sum_univ_add]; refine congr_arg₂ (·+·) (sum_congr rfl ?_) (sum_congr rfl ?_)
   · intro x _; unfold f
     have ht : (e.symm (Fin.castAdd w.length x)).val=x.val:=rfl
     have he : W[(e.symm (Fin.castAdd w.length x))]=u[x]:= (show (u++w)[x.val]' (by rw [List.length_append]; omega)=u[x.val] from List.getElem_append_left x.isLt)
     rw [he,ht,show W=u++w from rfl,List.eraseIdx_append_of_lt_length x.isLt]
   intro j _; unfold f
   have ht : (e.symm (Fin.natAdd u.length j)).val=u.length+j.val:=rfl
   have hv:u.length ≤ u.length+j.val:=Nat.le_add_right ..
   have he : W[(e.symm (Fin.natAdd u.length j))]=w[j]:=by
       change (u++w)[u.length+j.val]=w[j.val]
       rw [List.getElem_append_right hv]; congr; omega
   rw [he,ht,show W=u++w from rfl,List.eraseIdx_append_of_length_le hv]; rw [Nat.add_sub_cancel_left]
end list
omit [Fintype ι] in
lemma expires (w:Rail G ι)(he: ∀ j∈w, i.1≠j.1) (u:Rail G ι):
    windDown R i (u++w) = windDown (fun v=>R (v++w)) i u:=by
   unfold windDown; change winds (u++w) (fun j u=> wingK R u i j) = _ -- fill
   rw [winds_mix (fun j u=> wingK R u i j) u w]; unfold winds; rw [sum_eq_zero (f:=fun k:Fin w.length=> wingK R (u++ w.eraseIdx k) i w[k]),add_zero]
   · refine sum_congr rfl (fun i _=>?_); unfold wingK; exact congr_arg (day · 0) (funext fun n=> (night_move (guide _) _ R _ _ n).symm)
   intro k _; exact wing_lost R (he w[k] (List.getElem_mem ..)) _

-- physical TRUE uncut moment covariance formal counterpart. Field templates may depend on any Θ
-- support at their attached step. Restriction on directions at call of equation only non-overlap.
variable {R U}
def gap (w u:Rail G ι): Roll:=price P (u++w)-price P u*price P w
include H
lemma absent_wick (w:Rail G ι) (he : ∀ j∈w,i.1≠j.1) (u:Rail G ι):
   stepLaw P i (gap P w) u=taskBill P i (gap P w) u:=by
    let R v:= price P (v++w); let Q v:= price P v*price P w; rw [show gap P w= R-Q from rfl, subtracting,task_sub]; apply congr_arg₂ (·-·)
    · rw [show stepLaw P i R u= stepLaw P i (price P) (u++w) from rfl, settled P H]; unfold taskBill; rw [expires i (price P) w he]; unfold due cheaper R; simp_rw [night_move]
    unfold Q; rw [products,consign, settled P H]
end YM.RGComparison.Core16.Silk
