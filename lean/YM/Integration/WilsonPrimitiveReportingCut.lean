import YM.Integration.WilsonMasterReportingWords
import YM.OPE.Cards.Literal
import YM.OPE.ElementaryLog

/-! Finite Wilson reporters and their signed errors on the original
configuration, using the replica purchase at its actual lattice separation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPrimitiveReportingCut
open Filter Function Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open RG16 RG16.Literal Trace.Physical.GermGraph Trace.Pilot
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] [Nonempty I] (d : I → ℕ)

/-- One actual stop and one expense curve issue the full replica coefficient
and its signed local detector bound for every subsequent cutoff and period.
The normalized input coordinates may depend on both regulators. -/
theorem purchased (gauge : G.Simple) (H : C.Makes) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (h top stop : ℕ) (starts : Stock.Tabs.opens C.path.levels 1 top stop)
    (openStop : ∀ p, Opened C h stop p)
    (Gm : ℕ → ℝ) (paid : RateIs atTop C.S.scale Gm 0)
    (η M B : ℝ) (hη : 0 < η) (hM : 0 < M) (hB : 20 < B) :
    ∃ E rem : ℕ → ℝ, RateIs atTop C.S.scale E (-h) ∧ RateIs atTop C.S.scale rem (-h) ∧
      ∀ᶠ m : ℕ in atTop, let b := port C (8*M) B (mul_pos (by norm_num) hM) m
        ∃ (hs : stop ≤ b) (hb : b+1 < m), ∀ p,
          ∃ op : ∀ i, Opened C (d i) m p, ∀ N (hm : m < N) (x : I → Cover)
            (v : (i : I) → C.label (d i)),
          WithinRoom (WilsonReportingLength.radius C B m) M η (C.S.gridPoint m ∘ x) 0 →
          (∀ i, (C.labels.level (d i)).coeffSize (v i) ≤ Gm m) →
          let Y := Words C H d p N m v x hm.le op
          ∃ z Q, Funds C H p N b h top stop (E m) (rem m) (weight C h m)
            Y starts.1 hs ((Nat.le_succ b).trans (hb.le.trans hm.le)) (openStop p) z Q ∧
            PaidAt C.S N p top (C.beta N p) (2*(stakes C top stop / weight C h m))
              (Y-C.O N p z 0) := by
  obtain ⟨_,_,_,L⟩ := fac.costlier
  obtain ⟨E,rem,he,hr,h⟩ := expenses C gauge L.toPackage H d h top stop Gm paid η M B hη hM hB
    pace starts openStop
  refine ⟨E,rem,he,hr,?_⟩
  filter_upwards [h] with m h_m
  obtain ⟨hs,hb,allp⟩ := h_m
  refine ⟨hs,hb,fun p => ?_⟩
  obtain ⟨op,words⟩ := allp p
  refine ⟨op,fun N hm x v room invoice => ?_⟩
  obtain ⟨z,Q,sale⟩ := words N hm _ x v (WilsonMasterReportingWords.layout m B M η x room) invoice
  exact ⟨z,Q,sale,starts.1.trans (hs.trans ((Nat.le_succ _).trans (hb.le.trans hm.le))),
    sale.inview,sale.packing⟩

end YM.Integration.WilsonPrimitiveReportingCut

