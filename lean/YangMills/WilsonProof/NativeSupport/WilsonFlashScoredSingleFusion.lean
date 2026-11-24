import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryElection
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryReader
import YM.Integration.WilsonMacroscopicSharpPacket

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonFlashScoredSingleFusion
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Filter Extraction Spec Table
open Answer.ContinuumLimit Answer.ContinuumLimit.PreElectedPublication WilsonGraphPaperPublication
open scoped Classical Topology BigOperators
open private grouped_eq from YangMills.WilsonProof.NativeSupport.HierarchyBridge

private theorem onTicket {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities C f S) (foundation : Foundation F Q) {l : Filter (ℕ × ℕ)} [l.NeBot]
    (under : l ≤ f.fuse) (ticket : MatrixTicket (C := C) S F.sector.derivatives l) :
    YangMills.Hierarchy.SeparatedPowerLog (YangMills.hierarchy F Q) := by
  have logs := first_log F fac under ticket Q.spans
  constructor
  · intro I inst a m c o M η hM hη
    change Q.channels m at c
    let v : Labels S (fun i => (a i).1) := fun i => (a i).2
    obtain ⟨k,B,hB,paid⟩ := WilsonMacroscopicLoggedRow.original F Q v fac.toServices hM hη m
      (WilsonMacroscopicLoggedRow.issued F Q v logs hM hη m)
    let D := Q.stratum m
    let read : S.Field m →L[ℂ] ℂ :=
      (((Q.basis m).coord c).comp D.subtype.leftInverse).toContinuousLinearMap
    obtain ⟨K,hK,bound⟩ := read.bound
    refine ⟨K*B,mul_pos hK hB,k,?_⟩
    filter_upwards [paid,(show ∀ᶠ r : ℝ in 𝓝[>]0, 0 < r from self_mem_nhdsWithin),
      mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r atR hr h1 x hx
    have sheet := atR x o ⟨hx.1,hx.2⟩
    have same : badge r = 1+|Real.log r| := by
      unfold badge OPE.run
      rw [abs_of_nonpos (Real.log_nonpos hr.le h1)]
    let z : D := ⟨Q.fresh m x o v,Q.fresh_mem m x o v⟩
    have seen := bound z.val
    change ‖(Q.basis m).coord c (D.subtype.leftInverse z.val)‖ ≤ _ at seen
    have back : D.subtype.leftInverse z.val = z := LinearMap.leftInverse_apply_of_inj D.ker_subtype z
    rw [back] at seen
    change ‖(Q.basis m).coord c z‖ ≤ K*B * r^((m:ℝ)-weight (fun i => (a i).1)) *
      (1+|Real.log r|)^k
    rw [same] at sheet
    exact seen.trans ((mul_le_mul_of_nonneg_left sheet hK.le).trans_eq (by ring))
  · intro I J instI instJ a b h o M η c hM hη hc K _ clear
    let v : Labels S (fun i => (a i).1) := fun i => (a i).2
    let w : Labels S (fun j => (b j).1) := fun j => (b j).2
    obtain ⟨k,A,hA,paid⟩ := WilsonMacroscopicSharpPacket.on_ticket F Q fac foundation under ticket h v w hM hη hc
    refine ⟨A,hA,k,?_⟩
    filter_upwards [paid,(show ∀ᶠ r : ℝ in 𝓝[>]0, 0 < r from self_mem_nhdsWithin),
      mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r atR hr h1 x hx y hy s
    have cy : ClearOf o y c := ⟨(clear y hy).1,(clear y hy).2⟩
    have distinct : Function.Injective (beside (sole o) y) := by
      refine beside_distinct.mpr ⟨fun _ _ _ => Subsingleton.elim _ _,?_,?_⟩
      · intro j t eq
        by_contra ne
        have clash := cy.spread j t ne
        rw [eq,sub_self,norm_zero] at clash
        exact (not_le_of_gt hc) clash
      · intro z j eq
        have clash := cy.openSpace j
        change o = y j at eq
        rw [eq,sub_self,norm_zero] at clash
        exact (not_le_of_gt hc) clash
    have row := (atR x o y ⟨hx.1,hx.2⟩ cy).2 s
    rw [packet_read F Q x o v y w s h distinct] at row
    rw [grouped_eq,WilsonSharpPhysicalTreeGeometry.public_truncation]
    have same : badge r = 1+|Real.log r| := by
      unfold badge OPE.run
      rw [abs_of_nonpos (Real.log_nonpos hr.le h1)]
    rw [same] at row
    exact row.trans_eq (mul_right_comm ..)

theorem original (g : YangMills.GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p) :
    YangMills.Hierarchy.SeparatedPowerLog ((((issued.{u}).runs g hg).refine p hp).hierarchy) := by
  have receipts := WilsonSharpPhysicalTreeGeometryElection.retained.{u} g hg p hp
  rw [receipts.1]
  exact onTicket _ _ receipts.2.2.1 receipts.2.2.2.1 receipts.2.2.2.2.1 receipts.2.2.2.2.2.1

end YM.Integration.WilsonFlashScoredSingleFusion
