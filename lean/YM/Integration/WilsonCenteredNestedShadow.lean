import YM.Integration.WilsonCenteredNestedLedger
import YM.Integration.WilsonThermometerWeakPairPins

/-! The whole public packet through h against a single coherent raw
prescription, using every honest fixed detector sheet in that prescription.
This sharp local comparison applies to every lower component at once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedShadow
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

private lemma room (e:Exterior C.book):∃δ:ℝ,0<δ ∧ ClearOf 0 (bearing e) δ:=by
  have hc:=beside_distinct.mp (bearing_clear e)
  have away (i:Fin e.n):0<‖(0:E4)-bearing e i‖:=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hc.2.2 () i))
  have sep(i j:Fin e.n)(h:i≠j):0<‖bearing e i-bearing e j‖:=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hc.2.1.ne h))
  have lo:∀ᶠ δ in 𝓝[>] (0:ℝ),∀i:Fin e.n,δ≤‖(0:E4)-bearing e i‖:=
    eventually_all.mpr fun i=>(ge_mem_nhds (away i)).filter_mono nhdsWithin_le_nhds
  have mid:∀ᶠ δ in 𝓝[>] (0:ℝ),∀i j:Fin e.n,∀h:i≠j,δ≤‖bearing e i-bearing e j‖:=
    eventually_all.mpr fun i=>eventually_all.mpr fun j=>eventually_all.mpr fun h=>
      (ge_mem_nhds (sep i j h)).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ,hp,h,hh⟩:=((show ∀ᶠ δ:ℝ in 𝓝[>]0,0<δ from self_mem_nhdsWithin).and (lo.and mid)).exists
  exact ⟨δ,hp,h,hh⟩

def tax (P : Prescription F.sector.derivatives) (h : ℕ) : ℝ :=
  ∑ i∈bands F.sector.derivatives h,(∑ e∈(P.sheet i).support,‖(P.sheet i) e‖)*‖P.loaded i h‖

/-- Fixing the same raw prescription P for *all* these rows leaves
exactly the cost of the next discarded degree, even for the grade zero
component of the through-h field at the actual parent centre. -/
theorem rooted {P : Prescription F.sector.derivatives} (hp : P.Coherent)
    (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (v : Labels S d) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(k : ℕ)(B : ℝ),0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ x:I→E4,WithinRoom r M η x 0 →
      ‖shadowOld P h x 0 v - Q.packet h x v 0‖ ≤ B * shell r^k * r^((h:ℝ)+1-weight d) := by
  let T := Σ i : ↥(bands F.sector.derivatives h), ↥((P.sheet i.val).support)
  let observed (t : T) (k : ℕ) (B : ℝ) := ∀ᶠ r:ℝ in 𝓝[>]0,∀x:I→E4,WithinRoom r M η x 0 →
    Injective (beside x (bearing t.2.val)) ∧ ‖discrepancy S h x 0 v (Q.packet h x v 0)
      (bearing t.2.val) (fields S t.2.val)‖ ≤ wage k B r * r^((h:ℝ)+1-weight d)
  have expand (t : T) (k : ℕ) (B : ℝ) (j : ℕ) (E : ℝ) (kj : k ≤ j) (Bn : 0 ≤ B)
      (BE : B ≤ E) (src : observed t k B) : observed t j E := by
    filter_upwards [src,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r atR rp x fit
    have obs := atR x fit
    exact ⟨obs.1,obs.2.trans (mul_le_mul_of_nonneg_right (wage_le kj Bn BE) (Real.rpow_nonneg rp.le _))⟩
  have offered (t : T) : ∃k B,0 ≤ B ∧ observed t k B := by
    let e := t.2.val
    obtain ⟨δ,dp,clear⟩ := room e
    obtain ⟨k,B,Bp,paid⟩ := WilsonMacroscopicSharpPacket.on_ticket F Q fac foundation lo ticket h v (fields S e) Mn ηp dp
    refine ⟨k,B,Bp.le,?_⟩
    have little : ∀ᶠr:ℝ in 𝓝[>]0,r<δ/(M+1) := (gt_mem_nhds (div_pos dp (by linarith : 0 < M+1))).filter_mono nhdsWithin_le_nhds
    filter_upwards [paid,little,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin),
      mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r row small rp r1 x fit
    have gap : M*r < δ := by have hr := (lt_div_iff₀ (by linarith : 0 < M+1)).mp small;nlinarith
    constructor
    · apply beside_distinct.mpr
      refine ⟨?_,(beside_distinct.mp (bearing_clear e)).2.1,?_⟩
      · intro a b he
        by_contra diff
        have pos := fit.spaced a b diff
        rw [he,sub_self,norm_zero] at pos
        exact (not_lt_of_ge pos) (mul_pos ηp rp)
      · intro i j equal
        have hi := fit.span i
        have hj := clear.openSpace j
        rw [equal,sub_zero] at hi
        rw [zero_sub,norm_neg] at hj
        linarith
    · have take := (row x 0 (bearing e) fit clear).2 (none : Viewers F)
      have badge_eq : badge r = shell r := by unfold badge OPE.run shell;rw [abs_of_nonpos (Real.log_nonpos rp.le r1)]
      change ‖discrepancy S h x 0 v (Q.packet h x v 0) (bearing e) (fields S e)‖ ≤ B * badge r ^ k * _ at take
      rw [badge_eq] at take
      exact take
  obtain ⟨k,B,Bn,paid⟩ := pool observed expand offered
  have wealth : 0 ≤ tax F P h := Finset.sum_nonneg (fun i _=>mul_nonneg
    (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (norm_nonneg _))
  refine ⟨k,tax F P h*B,mul_nonneg wealth Bn,?_⟩
  filter_upwards [eventually_all.mpr paid] with r survey x fit
  have close := WilsonThermometerWeakPairPins.tomography F hp h x v (Q.packet h x v 0)
    (wage k B r * r^((h:ℝ)+1-weight d)) (fun i hi e he=>survey ⟨⟨i,hi⟩,⟨e,he⟩⟩ x fit)
  change _ ≤ tax F P h * (wage k B r * _) at close
  exact close.trans_eq (by unfold wage;ring)

end YM.Integration.WilsonCenteredNestedShadow
