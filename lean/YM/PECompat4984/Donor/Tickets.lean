import YM.Extra.SOURCE_HISTORIES.Tickets
import YM.Extra.SOURCE_HISTORIES.Drift
import YM.PECompat4984.Donor.Drift

/-! Exact seed helper restoration; retained definitions are imported unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Drift
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable (t : Site n) {R : Rep G n} (H : R.activities.Moves 1 t)

lemma move_eligible (i) (U : Config G n) : (R.activities.forced (H.kp i)).eligible R.p.threshold U ↔
    (R.activities.forced i).eligible R.p.threshold (translate t U) := by
  rw [← pull_one]; exact Work.H03.eligible_send 1 t R.p.threshold U _ _ (H.forced_support i) (H.forced_inventory i)
    (H.forced_tests i U)

lemma ticket_erase (x : Finset ℕ) (i : ℕ) : (ticket t H x).erase (H.kp i)=ticket t H (x.erase i) := by
  ext j; obtain ⟨j,rfl⟩ := H.kp.surjective j
  simp only [Finset.mem_erase,← ticket_mem,H.kp.injective.ne_iff]

lemma coat_send (b : Finset ℕ) (i) (U) : coat R (H.kp i) (ticket t H b) U=coat R i b (translate t U) := by
  classical
  unfold coat
  simp_rw [seats,← ticket_mem, ticket_erase,ticket_image,Finset.prod_image H.kp.injective.injOn]; simp only [move_K]

theorem stamp_format (P : Coefficient F n) {o : Site n} {A : Hol G} (h : P.Format o A R) :
    (stamp t H P).Format (o+t) A R := by
  refine ⟨fun i => regular_kept t (h.smooth i),fun i => (through ..).mp (h.origin i), ?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    change P.regular i (translate t 1)=0
    exact h.identity_null i
  · intro i ht J
    have hx (r : ℝ) : (stamp t H P).regular i (A.testLinks d (o+t) J r) = P.regular i (A.testLinks d o J r) :=
      congr_arg _ (test_translate t A ..)
    simp_rw [hx]
    exact h.projects i (nonwrap t ht) J
  · intro i U ht
    obtain ⟨i,rfl⟩ := H.kp.surjective i
    simp only [stamp,H.kp.symm_apply_apply,comp_apply] at ht
    exact (move_eligible ..).mpr (h.forcing _ _ ht)
  · intro i hi
    obtain ⟨i,rfl⟩ := H.kp.surjective i
    rw [move_support]
    exact (through ..).1 (h.carried i fun he => hi (by rw [stamp]; simp only [H.kp.symm_apply_apply,he]; rfl))
  · intro i; exact gauge_kept t (h.invariant _)
  · intro i
    obtain ⟨i,rfl⟩ := H.kp.surjective i
    rw [move_support]; simp only [stamp,H.kp.symm_apply_apply]; exact final_kept t (h.supported i)
  intro i; exact (h.borel _).comp (translate_cont t).measurable

theorem stamp_rem (P : Coefficient F n) {o : Site n} {u v : ℝ} (h : P.remBound o R u v) :
    (stamp t H P).remBound (o+t) R u v := by
  obtain ⟨a,b,ha,hb,hk,hv,⟨p,hp,hC⟩,q,hq,hQ⟩ := h
  refine ⟨a,b,ha,hb,hk,hv,⟨p,?_,fun i => bounds_kept t (hC i)⟩,fun i => q (H.kp.symm i),?_,
    fun i => ⟨(hQ _).1,fun U => (hQ _).2 (translate t U)⟩⟩
  · simpa only [stamp, BudgetPoint.mass,area] using hp
  let f (x : ℕ) := R.p.mass (R.activities.forced x).support (q x)
  have ht (i : ℕ) : R.p.mass (R.activities.forced i).support (q (H.kp.symm i))= f (H.kp.symm i) := by
    obtain ⟨i,rfl⟩ := H.kp.surjective i
    unfold f; rw [move_support]; simp only [BudgetPoint.mass,area,H.kp.symm_apply_apply]
  simp_rw [ht]
  exact ⟨fun i => hq.1 _, hq.2.1.comp_injective H.kp.symm.injective,(H.kp.symm.tsum_eq f).trans_le hq.2.2⟩

theorem stamped (he : ∀ U, R.eval U=R.eval (translate t U)) (hq : ∀ U, R.eval U≠0) (P : Coefficient F n)
    (B : SectionData F) (o : Site n) (U) :
    (stamp t H P).density (o+t) B R U = P.density o B R (translate t U) := by
  have hx : Real.exp (R.exponent U)=Real.exp (R.exponent (translate t U)) := by
    apply mul_right_cancel₀ (b:=R.activities.gas R.p U)
    · exact fun hz => hq _ (by rw [Rep.eval,hz,mul_zero])
    conv_rhs => rw [gases t H U]
    exact he U
  let Q := stamp t H P
  have ha (i) : Q.maskedTerm R i U = P.maskedTerm R i (translate t U) := by
    unfold Coefficient.maskedTerm
    by_cases hu : Healthy R.p.threshold (P.support i) (translate t U) <;> simp [Q,stamp,hu, clean t R.p]
  have ht : Q.exponentialEntry (o+t) B R U = P.exponentialEntry o B R (translate t U) := by
    unfold Coefficient.exponentialEntry
    simp_rw [ha, show Q.x=P.x from rfl, ← reloc_foot]
    by_cases hu : Healthy R.p.threshold (B.footprint o) (translate t U) <;> simp [clean t R.p,hu]
  have hd (b) : Q.marked R (ticket t H b) U=P.marked R b (translate t U) := by
    rw [marked_as,marked_as,← H.kp.tsum_eq (fun i => Q.forced i U*coat R i (ticket t H b) U)]
    simp_rw [coat_send, Q,stamp,H.kp.symm_apply_apply,comp_apply]
  change Q.density .. = _
  unfold Coefficient.density; rw [ht, he, hx,← (ticket t H).tsum_eq (fun b => Q.marked R b U),show
    ∑' b : Finset ℕ, Q.marked R (ticket t H b) U = _ from tsum_congr hd]

end YM.Extra.Histories.Drift
end
