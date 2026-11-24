import YM.Integration.WilsonMSDictionarySpatialRows
import YM.Integration.WilsonMacroscopicOutputCoordinates

/-! Fixed original engineering prices and the independently measured change of basis
 recover the ordinary output on the same positioned hierarchy. The half power of r
 left after the output inverse buys every fixed coupling order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMSDictionarySpatial
open Function Filter Set MeasureTheory Extraction Table Lattice Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonMacroscopicDetector WilsonPositionHomogeneousFrame
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
  (fac : Facilities R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (lead : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
  (paid : ∀ k, ∀ᶠ r in trail, Frame.obedient F A (J r) k) {n : ℕ}
  (d : Fin n → ℕ) (v : (i : Fin n)→Free R.family (d i)) (h : ℕ) (ψ : Test n)
local notation "D" => homogeneous F J Z

include fac in
/-- All originally issued detector rows are collapsed before the radius-dependent output inverse. -/
private theorem recovered (grades : GradePrice Q d (fun r i=>D r (d i) (v i)) (fun _=>0)) :
    ∀ᶠ r in trail,
      let u : Labels S d := fun i=>D r (d i) (v i)
      ‖fromProducts F h u r ψ-basket Q h u r ψ‖ ≤ fee F h*r^((h:ℝ)+1-1/4)*(∫ x : Points n, ‖ψ x‖) := by
  let m (X : probes F h) := ∫ z : Points (X.val.n+1), ‖X.val.test z‖
  have mp (X : probes F h) : 0 ≤ m X := integral_nonneg fun _=>norm_nonneg _
  let mass := ∫ z : Points n, ‖ψ z‖
  have massp : 0 ≤ mass := integral_nonneg fun _=>norm_nonneg _
  have obs := eventually_all.mpr fun X : probes F h => WilsonMSDictionarySpatialRows.original F Q fac.toServices d
    (fun r i=>D r (d i) (v i)) grades h ψ X.val (δ:=1/4) (by norm_num)
  filter_upwards [obs,RG17.positiveLength] with r signed rp
  let power := r^((h:ℝ)+1-1/4)
  have pp : 0 ≤ power := Real.rpow_nonneg rp.le _
  let u : Labels S d := fun i=>D r (d i) (v i)
  let packet := basket Q h u r ψ
  let xs := fun X : probes F h=>RG17.appeared F u X.val r ψ
  have price : ‖xs-read F h packet‖ ≤ (∑ X : probes F h,m X)*(power*mass) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun X _=>mp X) (mul_nonneg pp massp))).mpr
    intro X
    have row : ‖xs X-(read F h packet) X‖ ≤ power*m X*mass := signed X
    calc _ ≤ power*m X*mass := row
         _ = m X*(power*mass) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun z _=>mp z) (Finset.mem_univ X)) (mul_nonneg pp massp)
  have eq : fromProducts F h u r ψ-packet = restore F h (xs-read F h packet) := by rw [map_sub,exact_read]; rfl
  change ‖fromProducts F h u r ψ-packet‖ ≤ fee F h*power*mass
  rw [eq]
  exact ((restore F h).le_opNorm _).trans ((mul_le_mul_of_nonneg_left price (norm_nonneg _)).trans_eq (by
    dsimp only [fee,m]; ring))

include lead paid fac in
/-- The original leading and alignment receipts are used on J. Its actual conversion on every
 measured r pays the same deterministic half spatial power, in all perturbative orders. -/
theorem original {C : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R C) {b : ℝ}
    (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) {g : ℝ→ℝ} (hg : Coupling G g) (q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in trail,
      let u : Labels S d := fun i=>D r (d i) (v i)
      ‖(D r h).symm (fromProducts F h u r ψ)-(D r h).symm (basket Q h u r ψ)‖ ≤ ε*(g r)^q := by
  have old (k : ℕ) (x : Free R.family k) (j : ℕ) :
      RateLE RG17.home OPE.run (fun r=>Q.cutTest j k (J r k x)) (-(j:ℝ)) := by
    have bill := WilsonMacroscopicPrescribedInputs.grades hG W source pace hB F fac Q J lead paid
      (fun _ : Unit=>k) (fun _=>x) () j
    simpa only [add_zero] using bill
  have grades := WilsonMSDictionaryPositionCost.grades F J Z lead paid hG Q old d v
  obtain ⟨c,cp,inv⟩ := WilsonMacroscopicOutputCoordinates.inverse F J lead h (θ:=1/4) (by norm_num)
  have move := WilsonMSDictionaryPositionCost.inverse F J Z lead paid hG h
  let mass := ∫ x : Points n, ‖ψ x‖
  let cost := 2*c*fee F h*mass
  have buy := PhysMS.subpower_payment hg hG cost (1/2) (by norm_num) ε he q
  filter_upwards [recovered F J Z fac Q d v h ψ grades,move,inv,buy,RG17.positiveLength] with r data frame base price rp
  let u : Labels S d := fun i=>D r (d i) (v i)
  let w := fromProducts F h u r ψ-basket Q h u r ψ
  have powers : r^(-(h:ℝ)-1/4)*r^((h:ℝ)+1-1/4)=r^(1/2:ℝ) := by
    rw [←Real.rpow_add rp]; congr 1; ring
  change ‖(D r h).symm _-(D r h).symm _‖ ≤ _
  rw [←map_sub]
  calc
    ‖(D r h).symm w‖ ≤ 2*‖(J r h).symm w‖ := frame w
    _ ≤ 2*(c*r^(-(h:ℝ)-1/4)*‖w‖) := by exact mul_le_mul_of_nonneg_left (base w) (by norm_num)
    _ ≤ 2*(c*r^(-(h:ℝ)-1/4)*(fee F h*r^((h:ℝ)+1-1/4)*mass)) := by gcongr
    _ = cost*(r^(-(h:ℝ)-1/4)*r^((h:ℝ)+1-1/4)) := by dsimp only [cost]; ring
    _ ≤ ε*(g r)^q := by rw [powers]; exact price

end YM.Integration.WilsonMSDictionarySpatial
