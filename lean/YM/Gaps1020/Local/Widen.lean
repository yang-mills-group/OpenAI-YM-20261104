import YM.Gaps1020.Local.Expressed
set_option autoImplicit false
noncomputable section
namespace YM.Overlay.GapsLocal
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Push Next.Foundations AbsoluteSums GridApprox.Nil
open MergeProof Merge Accent Extra.Iteration
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n m:Side}{V:Type}[Fintype V][DecidableEq V]{B:Marker.Census V}{R: RG.Rep G n}{u s c k z h:ℝ}{p d q:ℕ}(a:Bands B R)(w w':V→ℝ)
-- Pay true shipping and inflation. No resetting marker charges when
-- pushing, all summation statements uniform in (Vol of lattice). Loss of
-- precision for re-expression uses only degree of unpriced exponent mode.
omit [Fintype V]
def shade (w:V→ℝ)(z:ℝ):= fun i=>z*w i
omit [DecidableEq V] in
lemma shade_pos (hw:∀ i,0<w i)(hz:0<z) i: 0<shade w z i:= mul_pos hz (hw _)
lemma shady (v:ℝ)(i:B.Mode): Poly.toll (shade w v) i=v^i.val.card * Poly.toll w i:=by simp only [shade,Poly.toll,prod_mul_distrib,prod_const]
lemma usual (v:B.Mode)(hv:v.val.Nonempty)(hw:∀ i,0<w i)(hp:0 ≤ z)(hr:z≤1): Poly.toll (shade w z) v ≤ z * Poly.toll w v:=by
   rw [shady]; exact mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one hp hr (n:=v.val.card) (m:=1) (card_pos.mpr hv)).trans_eq (pow_one _)) (Poly.worth hw v).le
lemma curveCost (v:B.Mode)(hw:∀ i,0<w i)(he:v.val.card ≤ p)(hr:1 ≤ z): Poly.toll w v ≤ z^p * Poly.toll (shade w z⁻¹) v:=by
   have hz:0<z:=zero_lt_one.trans_le hr
   rw [shady,←mul_assoc]; apply le_mul_of_one_le_left (Poly.worth hw v).le; rw [inv_pow,← div_eq_mul_inv,le_div_iff₀ (by positivity),one_mul]; exact pow_le_pow_right₀ hr he
section budget
variable {w w'}
lemma shiftBill (hw:∀ i,0<w' i)(e:ℝ)(he0:0≤e)(he:a.Radial w u s c z)(hU:∀ i,w' i*‖a.units i‖ ≤ k)(hy:∀ i:B.Mode,Poly.toll w' i≤ e*Poly.toll w i){U₀ W₀:ℝ}(hY:e*s≤ U₀)(hP:e*c≤W₀): a.Radial w' k U₀ W₀ z:=by
   obtain ⟨v,hv,h0⟩ := he.bulk; obtain ⟨r,hr,r0⟩:= he.hits
   have hh {T S :ℝ} {ι:Type} (F:ι→B.Mode)(g:ι→ℝ)(k:V)(hg:∀ i,0≤g i)(hf:SumBudget (fun i=>if k∈(F i).val then Poly.toll w (F i)*g i else 0) T)(h:e*T≤ S): SumBudget (fun i=>if k∈(F i).val then Poly.toll w' (F i)*g i else 0) S:=by
      refine budget_loosen (budget_mono (budget_scale ‹0≤e› hf) (fun i=>?_) (fun i=>?_)) h
      · split; exact mul_nonneg (Poly.worth hw _).le (hg i); rfl
      split; next h=> rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hy _) (hg i)
      next=> rw [mul_zero]
   exact ⟨hw,hU,he.factor,⟨v,hv,fun i=> hh _ _ i (fun j=>le_trans (hv j).1 (R.p.loMass _ _ (hv j).1)) (h0 i) hY⟩,⟨r,hr,fun i=> hh (fun j:ℕ × ℕ=>a.marks j.1 j.2) _ i (fun j=> (hr ..).1.trans (R.p.loMass _ _ (hr j.1 j.2).1)) (r0 i) ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hP he.factor.le))⟩⟩
variable {ι:Type}(q':ι→Menu.Hat B R) {o: V→Site n}
open Menu
lemma offerPrice (hw:∀ i,0 < w i)(he:Offer o q' w d c z)(ht:0<u)(hi:u≤1) (hh:u*z≤ s):Menu.Offer o q' (shade w u) d c s:=by
   refine ⟨he.sites,fun i => budget_loosen (budget_mono (budget_scale ht.le (he.budget i)) (fun i=>?_) (fun j=>?_)) hh⟩
   · split; exact mul_nonneg (Crew _ (shade_pos _ hw ht)) (Real.exp_pos _).le; exact le_rfl
   split; next h=> unfold Menu.fare Menu.sumFee; simp only [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (usual w (q' j).s (q' j).shiny hw ht.le hi) (norm_nonneg _)) (q' j).M.profit
   next=>rw [mul_zero]
end budget
end YM.Overlay.GapsLocal
