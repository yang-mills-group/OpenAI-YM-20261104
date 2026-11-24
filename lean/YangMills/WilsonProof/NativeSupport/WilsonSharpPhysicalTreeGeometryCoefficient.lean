import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryAverages
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryPrices
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryRecursive
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeEdgeTelescope
import YM.Integration.WilsonSharpPhysicalTreeContractionFlat

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open Function Filter Finset Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Arboreal
open OPE.Nesting OPE.Nesting.Atom OPE.Log YangMills.Hierarchy MeasureTheory
open WilsonCenteredNestedPairHaar WilsonCenteredNestedLoggedRow WilsonSharpPhysicalTreeEdgePowers
open scoped Classical BigOperators Topology
attribute [local instance] measO borelO YM.Work.A15.compact_ortho

variable {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (t : FusionTree)
local notation "T" => YangMills.hierarchy F Q

/-- At one rotation and reality branch, the raw projection bought by the ticket is exactly
 the complete physical contraction to which the edge estimates apply. -/
theorem contracted_eq_projected (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (m : ℕ) (c : Q.channels m) (x : Fin t.leaves → E4) (z : t.Vertex → E4) (k : Ortho) (b : Bool) :
    WilsonSharpPhysicalTreeEdgeTelescope.contracted F Q t a x z D m c k b =
      WilsonSharpPhysicalTreeEdgeTickets.projected F Q (rawTree t) (degrees (allTags t a))
        (voices (allTags t a)) (rawCutoff t D) m c (rawPosition t x z) k b := by
  have labels : names (fun i => WilsonCenteredNestedTerminalOrbit.into F
      (degrees (allTags t a) i) k b (voices (allTags t a) i)) =
      WilsonSharpPhysicalTreeContractionFlat.leafNames F t a k b := by
    funext i
    cases i with
    | inl v =>
      change quoteTag (⟨0,WilsonCenteredNestedTerminalOrbit.into F 0 k b 0⟩ : S.Tag) = quoteTag ⟨0,0⟩
      cases b <;> simp [WilsonCenteredNestedTerminalOrbit.into]
    | inr i => rfl
  calc
    _ = ∑ u : WilsonSharpPhysicalTreeContractionFusion.Selection F Q t D, ∏ v : t.Vertex,
        WilsonSharpPhysicalTreeContractionFusion.vertex F Q t a D m c (rawPosition t x z) k b u v := by
      apply sum_congr rfl
      intro u _
      apply prod_congr rfl
      intro v _
      have points : WilsonSharpPhysicalTreeContractionFusion.points t (rawPosition t x z) v = t.positions (v := v) x z :=
        WilsonSharpPhysicalTreeContractionFusion.publicPoints t x z v
      have fields : WilsonSharpPhysicalTreeContractionFusion.childTags F Q t a D u v = t.childField T a u (v := v) :=
        WilsonSharpPhysicalTreeContractionFusion.publicTags F Q t a D u v
      unfold WilsonSharpPhysicalTreeContractionFusion.vertex
      rw [points,fields]; rfl
    _ = _ := by
      unfold WilsonSharpPhysicalTreeEdgeTickets.projected
      rw [labels]
      exact WilsonSharpPhysicalTreeContractionFlat.factorization F Q t a D m c (rawPosition t x z) k b

private theorem at_smaller_scales {P : ℝ → Prop} (paid : ∀ᶠ r : ℝ in 𝓝[>]0, P r) :
    ∀ᶠ r : ℝ in 𝓝[>]0, ∀ s, 0 < s → s ≤ r → P s := by
  obtain ⟨e,ep,fit⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp paid
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ge_mem_nhds ep)] with r re s sp sr
  exact fit ⟨sp,sr.trans re⟩

/-- Both coefficient estimates on the public tree, with one cap, constant and log exponent
 chosen before the radii, positions, and independently varying ratios. -/
theorem coefficient_expansion (fac : Facilities C f S) (foundation : Foundation F Q)
    {l : Filter (ℕ × ℕ)} [l.NeBot] (lo : l ≤ f.fuse)
    (ticket : MatrixTicket (C := C) S F.sector.derivatives l)
    (t : FusionTree) (a : Fin t.leaves → S.Tag) (D : Fin t.branches → ℕ)
    (m : ℕ) (c : Q.channels m) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (o : E4) :
    ∃ β ∈ Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0,
      ∀ s x z, t.Admissible r β M η s x z → z 0 = o →
        ‖(YangMills.hierarchy F Q).coefficient a m c x o‖ ≤ A * t.bound T (m : ℝ) a s k ∧
        ‖(YangMills.hierarchy F Q).coefficient a m c x o - t.iterated T a x z D m c‖ ≤ A * t.bound T (m : ℝ) a s k * t.cutoffGain D s := by
  let tree := rawTree t
  let V := allTags t a
  let p := names (voices V)
  let d := rawCutoff t D
  obtain ⟨_,β,_,hβ,converted⟩ := simultaneous t hM hη
  obtain ⟨A,hA,power,raw⟩ := WilsonSharpPhysicalTreeEdgeTickets.original F Q tree (degrees V)
    fac lo ticket (voices V) d m c hM (half_pos hη)
  obtain ⟨j,B,hB,edges⟩ := WilsonSharpPhysicalTreeEdgeTelescope.original F Q t fac foundation lo ticket a D m c hM hη
  let k := max power j
  have banks := leaf_margin F Q (tickets_suffice F fac lo ticket Q.spans) tree p d m hM (half_pos hη)
  have childBanks := eventually_all.mpr (fun v : t.Vertex => Orbits.admissible_separated (I := t.Child v) F Q hM hη
    (WilsonSharpPhysicalTreeEdgeTelescope.cap t m D v))
  refine ⟨β,hβ,A+B+1,by linarith,k,?_⟩
  filter_upwards [raw,edges,banks,at_smaller_scales childBanks,Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)]
    with r pay edge live childLive smallRoot
  intro s x z admissible center
  have court : ImmediateCourt t r β M η s x z := admissible.2
  subst o
  let X := rawPosition t x z
  let R := rawScale t s
  have geom : tree.Convoy M (η/2) R X := (converted r s x z court).1
  have under (v : t.Vertex) : s v ≤ r := (geom.sizes.bound (tree.closure (.inl v)) (zone_inl t v)).trans_eq court.1
  have small (v : t.Vertex) : 0 < s v ∧ s v ≤ 1 := ⟨court.2.1 v,(under v).trans smallRoot.2.le⟩
  let P := t.bound T (m:ℝ) a s k
  let gain := t.cutoffGain D s
  have price : tree.listPrice p R m k = P := listPrice_eq t T p a (allTags_grade t a) m k s small
  have grace : tree.grace R d = gain := grace_eq t D s
  have rent : attachedBase T t a s m = t.bound T (m:ℝ) a s 0 :=
    attachedBase_eq_bound t T p a (allTags_grade t a) m s geom.sizes
  have basePos : 0 ≤ attachedBase T t a s m := by
    unfold attachedBase
    exact div_nonneg (pow_nonneg (small 0).1.le _) (prod_nonneg (fun i _ => pow_nonneg (small _).1.le _))
  have shellPrice : attachedBase T t a s m * (∏ v, shell (s v)^k) = P := by
    rw [rent]; simp [P,FusionTree.bound,shell]
  have nonneg : 0 ≤ P := by
    rw [←shellPrice]
    exact mul_nonneg basePos (prod_nonneg (fun v _ => pow_nonneg (zero_le_one.trans (shell_one _)) _))
  have gainPos : 0 ≤ gain := sum_nonneg (fun i _ => pow_nonneg (div_nonneg (small i.succ).1.le (small _).1.le) _)
  let W := WilsonSharpPhysicalTreeEdgeTickets.direct F Q tree (degrees V) (voices V) m c X
  let U := WilsonSharpPhysicalTreeEdgeTelescope.contracted F Q t a x z D m c
  have enter := live X R court.1 geom
  have opened (v : t.Vertex) : orbitMargin Q.port (WilsonSharpPhysicalTreeEdgeTelescope.cap t m D v)
      (t.positions (v := v) x z) (z v) :=
    childLive (s v) (small v).1 (under v) v _ _ ⟨(court.2.2.2 v).1,(court.2.2.2 v).2⟩ _ le_rfl
  have bill (K : Ortho) (b : Bool) : ‖W K b‖ ≤ A*P ∧ ‖W K b - U K b‖ ≤ A*(P*gain) := by
    have paid := pay X R court.1 geom k (le_max_left _ _) K b
    rw [price,grace] at paid
    exact ⟨paid.1,by simpa only [U,contracted_eq_projected] using paid.2⟩
  have intW (b : Bool) : Integrable (fun K => W K b) haar := direct_integrable F Q t a m c X enter b
  have pub : (YangMills.hierarchy F Q).coefficient a m c x (z 0) = mean W := direct_mean F Q t a m c x z enter
  have signed : ‖mean W - mean U‖ ≤ A*(P*gain) := by
    rw [norm_sub_rev]
    apply difference U W (fun K b => by rw [norm_sub_rev]; exact (bill K b).2)
      (WilsonSharpPhysicalTreeEdgeTelescope.measurable_contracted F Q t a x z D m c opened) intW
  have settle := (edge β hβ.2.le s x z admissible).2
  have larger : (∏ v : t.Vertex, shell (s v)^j) ≤ ∏ v : t.Vertex, shell (s v)^k :=
    prod_le_prod (fun v _ => pow_nonneg (zero_le_one.trans (shell_one _)) _)
      (fun v _ => pow_le_pow_right₀ (shell_one _) (le_max_right _ _))
  have edgeCost : ‖mean U - t.iterated T a x z D m c‖ ≤ B*P*gain := by
    apply settle.trans
    apply mul_le_mul_of_nonneg_right _ gainPos
    rw [←shellPrice,←mul_assoc]
    exact mul_le_mul_of_nonneg_left larger (mul_nonneg hB basePos)
  rw [pub]
  constructor
  · exact (mean_norm W (fun K b => (bill K b).1) intW).trans (mul_le_mul_of_nonneg_right (by linarith) nonneg)
  calc
    ‖mean W - t.iterated T a x z D m c‖ = ‖(mean W - mean U) + (mean U - t.iterated T a x z D m c)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖mean W - mean U‖ + ‖mean U - t.iterated T a x z D m c‖ := norm_add_le ..
    _ ≤ A*(P*gain) + B*P*gain := add_le_add signed edgeCost
    _ ≤ (A+B+1)*P*gain := by nlinarith [mul_nonneg nonneg gainPos]

end YM.Integration.WilsonSharpPhysicalTreeGeometry
