import YM.Integration.WilsonThermometerUnitFilingFeed
import YM.UVNext.COUPLING_RESET.Probe

/-! The original horizon-zero filing can be read on a second presentation of
the same deposited density and vacuum without transporting hard addresses. -/
set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCourse

open Function Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal RG12 Bid
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)

private theorem the_page {n : Side} (F : Frame G 0) (A : Hol G) {P : Rep G n}
    {o : Site n} {Q : Coefficient F n} (fmt : Q.Format o A P) (θ : ℝ) :
    Germ.projection F A θ o Q = Q.x := by
  have empty (i : ℕ) : Germ.vector F A θ o (Q.regular i)=0 := by
    have paid := Germ.computed (d:=0) A (fmt.smooth i) o (Nat.zero_le _)
    have hz : A.PiVanish 0 o (Q.regular i) := by
      intro J
      refine ⟨(paid J).1,?_⟩
      intro k hk
      obtain rfl := Nat.eq_zero_of_le_zero hk
      simpa only [iteratedDeriv_zero,Next.Foundations.test_one] using fmt.identity_null i
    have exactJet := JetTest.unique paid ((jetTest_zero_iff A o (Q.regular i) 0).mpr hz)
    simp [Germ.vector,exactJet]
  simp [Germ.projection,empty]

local notation "F" => R.family.labels.level 0
include simple in
private theorem flat {n : Side} (P : Rep G n) {o : Site n} (D : SectionData (F))
    (Q : Coefficient (F) n) {A : Hol G} (fmt : Q.Format o A P) :
    (P.eval (1:Config G n):ℂ)⁻¹ * Q.density o D P 1 = Q.x 0 := by
  have clear := UVNext.CouplingReset.flags_one (n:=n) (G:=G) P.p
  have h : P.eval (1:Config G n) = Real.exp (P.exponent 1) := by
    rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  have positive : (P.eval (1:Config G n):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (h ▸ (Real.exp_pos _).ne')
  have quiet (i : ℕ) : Q.maskedTerm P i 1 = 0 := by
    rw [Coefficient.maskedTerm,masked_eq _ _ _ _ (one_healthy _ _ P.p.threshold_pos.le),fmt.identity_null]
  have hard (b : Finset ℕ) : Q.marked P b 1=0 := by
    unfold Coefficient.marked
    split
    next live =>
      have empty : b=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        obtain ⟨x,hx⟩:=(P.activities.forced j).inventory_ne
        have occupied : x∈flags P.p.threshold (1:Config G n) :=
          live.2 ▸ Finset.mem_biUnion.mpr ⟨j,hj,hx⟩
        rw [clear] at occupied
        exact Finset.notMem_empty x occupied
      simp [empty]
    rfl
  have unit : (F).core Q.x=0 := by
    obtain ⟨z,hz⟩ := RG12.unit_spans simple R.family 0 0 (by decide) Q.x
    rw [hz,map_smul]
    have hcore : (F).core (unitVec (F) R.family.path 0)=0 := by
      funext i
      by_cases hi : i=0 <;> simp [Labels.Frame.core,unitVec,Labels.Frame.e0,Function.update,hi]
    rw [hcore,smul_zero]
  have light : Q.exponentialEntry o D P 1=Q.x 0 := by
    simp only [Coefficient.exponentialEntry,unit,map_zero,quiet,tsum_zero,add_zero]
    rw [show D.places 0 o=0 from funext fun i=>congr_fun (map_zero (IsLinearMap.mk' D.evaluate D.eval_linear)) _]
    rw [masked_eq _ _ _ _ (one_healthy _ _ P.p.threshold_pos.le)]
    simp
  simp [Coefficient.density,hard,light,positive]

include simple in
/-- The recorded unit coordinate of a genuinely enrolled whole source is its
whole unnormalized deposit evaluated at flat output over its own flat vacuum.
The fine configurations and tag histories have already been integrated here. -/
theorem filed {N p i : ℕ} (Y : Cut R.family N p) (opened : Opened R.family 0 i p)
    (live : i≤N) (book : Booked R.family N p 0 Y i live) :
    WilsonThermometerUnitFilingFeed.report R Y i =
      ((R.family.path.rep N p i).eval (1:Config G (R.family.side i p)):ℂ)⁻¹ *
      credit R.family N p 0 Y i live 1 := by
  obtain ⟨r,hr,fee⟩ := book.sheet
  let q := sheet R.family N p 0 Y i live
  have read : readPage R.family N p 0 Y i live=q.x :=
    the_page (F) R.family.params (Q:=q) hr.1 _
  let T := fitting (C:=R.family) 0 N p i R.makes opened live
  have moved := WilsonThermometerUnitFilingFeed.transfer R simple opened live
    (T.symm (readPage R.family N p 0 Y i live))
  change T (T.symm _) = _ at moved
  rw [LinearEquiv.apply_symm_apply] at moved
  rw [WilsonThermometerUnitFilingFeed.report,dif_pos ⟨opened,live⟩,
    WilsonThermometerUnitFilingFeed.terminal R simple (opened.post.trans live)]
  change (T.symm _) 0=_
  rw [←moved,read,fee]
  exact (flat R simple _ _ q hr.1).symm

include simple in
/-- A second original course carrying the same all-field numerator and
vacuum gives the identical filed unit, regardless of its roster of owners. -/
theorem on_course {N p i : ℕ} (Y : Cut R.family N p) (opened : Opened R.family 0 i p)
    (live : i≤N) (book : Booked R.family N p 0 Y i live)
    (P : Rep G (R.family.side i p)) (o : Site (R.family.side i p)) (D : SectionData (F))
    (Q : Coefficient (F) (R.family.side i p)) (shape : Q.Format o R.family.params P)
    (vac : P.eval=(R.family.path.rep N p i).eval)
    (posted : Q.density o D P = credit R.family N p 0 Y i live) :
    WilsonThermometerUnitFilingFeed.report R Y i = Q.x 0 := by
  rw [filed R simple Y opened live book,←vac,←posted]
  exact flat R simple P D Q shape

end YM.Integration.WilsonThermometerUnitFilingCourse
end
