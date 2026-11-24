import YM.Integration.WilsonMeasuredOwnerPicture

/-! One charged coefficient on its own original hard inventory, tested by all
ordinary regular peers on the same physical field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionMount
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Overlay QuadraticLocal QuadraticLocal.Earn Ac
open Push.Corrected Push.AbsoluteSums QuadraticLocal.Fusion.Attached MergeProof.Accent
open WilsonPhysicalMarkedDefect WilsonMeasuredCoefficientTransport WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {V T : Type} [DecidableEq V] {J : Census V}
private def narrow (v:V)(a:Poly J):Prop:=∀s, ¬ s.val⊆{v} → a.part s=0

private theorem closed (v:V) {a b:Poly J} (ha:narrow v a)(hb:narrow v b):narrow v (a*b):=by
  intro s hs
  rw [Poly.part_mul]
  apply sum_eq_zero
  intro u _
  apply sum_eq_zero
  intro t _
  split
  next h =>
    by_cases yes:u.val⊆{v}
    · have no:¬t.val⊆{v}:=fun ht=>hs (h.2 ▸ union_subset yes ht)
      rw [hb _ no,mul_zero]
    · rw [ha _ yes,zero_mul]
  next => rfl

private theorem one (v:V):narrow v (1:Poly J):=by
  intro s hs
  have ne:s≠J.quiet:=fun e=>hs (e ▸ empty_subset _)
  simp only [Poly.one_part,if_neg ne]

private theorem only (v:V)(c b:ℂ):narrow v (Poly.bead J c+Poly.send (J.fire v) b):=by
  intro s hs
  have quiet:s≠J.quiet:=fun e=>hs (e ▸ empty_subset _)
  have hot:s≠J.fire v:=fun e=>hs (e ▸ Subset.rfl)
  change (Poly.send J.quiet c + Poly.send (J.fire v) b).part s=0
  simp only [Poly.part_plus,Poly.part_send,if_neg quiet,if_neg hot,add_zero]

variable [Fintype V]
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {A : Hol G}
  {W : Rep G n} {o:V→Site n} {k κ B:ℝ}
  (rent:Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent k)
  (v:V)(h:Coefficient F n)(legal:h.Format (o v) A W)(t:T→ℂ)
local notation "old" => (Hard.rent rent : Hard T W.p W.activities.forced W.activities.K o J)
local notation "added" => joined (old) v h legal t

theorem gas (w:V→ℝ)(positive:∀i,0<w i)(bound:∀x,‖t x‖≤1)
    (paid:h.remBound (o v) W κ B)(x:T)(U:Config G n):
    (∑' b,packet W.activities W.p ((added).hard x) U b) =
      (∑' b,packet W.activities W.p ((old).hard x) U b) +
        Poly.send (J.fire v) (t x*∑' b,h.marked W b U) :=by
  let P := packet W.activities W.p ((added).hard x) U
  have cost := Hard.leasing (w:=w) rent (o:=o) (R:=J) (α:=T)
  have upper := WilsonOriginalDepositedHard.paid (old) v h legal t w positive cost bound paid
  have funded := Hard.packet_summing (added) upper W.p.exponent_pos.le positive x U
  have base : (∑' b,packet W.activities W.p ((old).hard x) U b)=Poly.bead J (W.activities.gas W.p U) := model_input_gas (A:=Passport.point o) (Γ:=J) rent positive x U
  have confined (I:Finset ℕ): narrow v (P I):=by
    dsimp only [P]
    unfold packet
    split
    next action =>
      clear action
      induction I using Finset.induction_on with
      | empty => simpa only [prod_empty] using one (J:=J) v
      | @insert i I absent ih =>
        rw [prod_insert absent]
        exact closed v (only v _ _) ih
    next => exact fun _ _=>rfl
  ext1 s
  rw [Poly.part_plus,Poly.part_send]
  by_cases fired:s=J.fire v
  · subst s
    rw [if_pos rfl]
    exact (sub_eq_iff_eq_add'.mp (WilsonOriginalDepositedHardTable.full (old) v h legal t w positive cost bound paid x U))
  rw [if_neg fired,add_zero]
  by_cases quiet:s=J.quiet
  · subst s
    rw [Hard.packet_of_quiet (added) x U funded,Hard.packet_of_quiet (old) x U
      (Hard.packet_summing (old) cost W.p.exponent_pos.le positive x U)]
  · have distant:¬s.val⊆{v}:=by
      intro hsub
      rcases subset_singleton_iff.mp hsub with hq|hf
      · exact quiet (Subtype.ext hq)
      · exact fired (Subtype.ext hf)
    rw [base]
    change (∑' b,P b).part s=(Poly.send J.quiet _).part s
    rw [Poly.share funded,Poly.part_send,if_neg quiet]
    exact (tsum_congr (fun b : Finset ℕ=>confined b s distant)).trans tsum_zero

/-- The ordinary peer film may contain every approved proper mixed word. -/
theorem field {ι:Type} (E:Lamps T ι G W.p o J)(w:V→ℝ)(positive:∀i,0<w i)(bound:∀x,‖t x‖≤1)
    (paid:h.remBound (o v) W κ B)(x:T)(U:Config G n):
    (⟨E,(added)⟩:Gallery T ι o W J).density x U-(⟨E,(old)⟩:Gallery T ι o W J).density x U=
      Poly.pass (E.log x U) * Poly.send (J.fire v) (t x*account h W U):=by
  unfold Gallery.density Gallery.gas
  rw [gas rent v h legal t w positive bound paid x U,mul_add,smul_add,add_sub_cancel_left]
  rw [←mul_smul_comm]
  congr 1
  ext1 s
  simp only [Poly.part_smul,Poly.part_send]
  split <;> simp_all [account,mul_left_comm,mul_comm]

end YM.Integration.WilsonMeasuredCompanionMount
