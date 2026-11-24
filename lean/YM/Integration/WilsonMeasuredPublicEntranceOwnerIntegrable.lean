import YM.Integration.WilsonMeasuredPublicEntranceOwnerSale
import YM.Integration.WilsonMeasuredPublicEntranceOrder

/-! Original integrability on the actual held fibre. The qualitative bounds
below are used only to distribute the native conditional integral. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwnerIntegrable
open Function Finset Set MeasureTheory Lattice Wilson RG Source Labels Marker Extra.Histories
open Push.Local PhysicalNext PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceOwnerGas WilsonMeasuredPublicEntranceOrder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]{J:Census V}{f N p:ℕ}
local notation "P" => R.family.path.rep N p f
local notation "field" => Config G (R.family.side f p)

omit [Fintype V] in
theorem local_rows (o:V→Site (R.family.side f p))(φ:V → field→ℂ)
    (c:V → Poly J)(M:V → Support (R.family.side f p) → field → Poly J)
    (w:V→ℝ){e:ℝ}{m:V→ℝ}
    (entry:∀v Z,Burns o Z (M v Z) (P).p.threshold)(fee:∀v,Towed w id (M v) (P).p.B e (m v))
    (split:∀v U,Poly.send (J.fire v) (φ v U)=c v+∑Z,M v Z U)(v:V):
    BoundedAt R.family (φ v):=by
  classical
  obtain ⟨_,_,_,spent⟩:=fee v
  choose a _ bounds _ using spent
  have seen(U):φ v U=(c v).part (J.fire v)+∑Z,(M v Z U).part (J.fire v):=by
    have eq:=congrArg (fun z:Poly J=>z.part (J.fire v)) (split v U)
    simpa only [Poly.part_send,if_pos rfl,if_true,Poly.part_plus,Poly.part_sum] using eq
  refine ⟨?_,‖(c v).part (J.fire v)‖+∑Z,a Z (J.fire v),?_⟩
  · rw [funext seen]
    exact (measurable_const.add (Finset.measurable_fun_sum _ (fun Z _=>(entry v Z).me _))).aestronglyMeasurable
  · intro U
    rw [seen]
    exact (norm_add_le ..).trans (add_le_add (le_refl _) ((norm_sum_le ..).trans (sum_le_sum (fun Z _=>bounds Z U (J.fire v)))))

theorem account_at (live:f≤N){d:ℕ}(q:Coefficient (R.family.labels.level d) (R.family.side f p))
    (o:Site (R.family.side f p)){κ M:ℝ}(legal:q.Format o R.family.params (P))(fee:q.remBound o (P) κ M):
    BoundedAt R.family (account q (P)):=by
  let S:=R.family.localSection d
  have leaf:=WilsonMeasuredOnlyHard.original q (P) (P) rfl rfl rfl S R.family.params o κ M legal fee
  have law:=(R.makes.wilson.represents N p f live).good
  have full:=Coefficient.envelope S law fee legal
  have saved:=Coefficient.envelope S law leaf.2.1 leaf.1
  obtain ⟨A,a⟩:=full.cost
  obtain ⟨B,b⟩:=saved.cost
  have seen(U):account q (P) U=q.density o S (P) U-(WilsonPhysicalMarkedDefect.RegularProjection.soft q).density o S (P) U:=by
    rw [leaf.2.2.1 U];ring
  refine ⟨?_,A+B,fun U=>?_⟩
  · rw [funext seen];exact (full.meas.sub saved.meas).aestronglyMeasurable
  · rw [seen];exact (norm_sub_le ..).trans (add_le_add (a U) (b U))

theorem together (live:f≤N) (φ:V → field→ℂ)(host:∀v,BoundedAt R.family (φ v))
    {d:ℕ}(q:Coefficient (R.family.labels.level d) (R.family.side f p)){i:V}
    (o:Site (R.family.side f p)){κ M:ℝ}(legal:q.Format o R.family.params (P))(fee:q.remBound o (P) κ M)
    (s:J.Mode)(inside:i∈s.val):
    Integrable (fun U=>(restore (B:=J) (P) φ (selected (P) q i) 0 0 U).part s) (prior G _) ∧
    Integrable (fun U=>((P).eval U:ℂ)*(∏v∈s.val,φ v U)) (prior G _):=by
  classical
  have qual(t:Finset V):BoundedAt R.family (fun U=>∏v∈t,φ v U):=by
    induction t using Finset.induction_on with
    | empty=>simpa only [Finset.prod_empty] using (one R.family (K:=f) (p:=p))
    | @insert v t hv ih=>simpa only [Finset.prod_insert,hv,not_false_eq_true] using times R.family (host v) ih
  have simple:=WilsonMeasuredPublicEntranceOrder.integrable R.family R.makes live (qual s.val)
  simp only [Complex.real_smul] at simple
  have h:=times R.family (account_at R live q o legal fee) (qual (s.val.erase i))
  have charged : Integrable (fun U=>account q (P) U*∏v∈s.val.erase i,φ v U) (prior G _):=by
    obtain ⟨me,b,paid⟩:=h
    exact Integrable.of_bound me b (ae_of_all _ paid)
  have valid:=(R.makes.wilson.represents N p f live).good.labels
  have value(U): (restore (B:=J) (P) φ (selected (P) q i) 0 0 U).part s=
      ((P).eval U:ℂ)*(∏v∈s.val,φ v U)+account q (P) U*(∏v∈s.val.erase i,φ v U):=by
    have exactAt:=WilsonMeasuredPublicEntranceOwnerSale.fieldwise (P) φ q i valid fee s inside U
    linear_combination exactAt
  exact ⟨by rw [funext value];exact simple.add charged,simple⟩

end YM.Integration.WilsonMeasuredPublicEntranceOwnerIntegrable
end
