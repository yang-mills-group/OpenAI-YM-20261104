import YM.Integration.WilsonFundedReportingBranch
import YM.Next.UV_STRESS.Layout

/-! Signed assembly: each original issued coefficient and its full
regulator data are kept while the cell norm prices their complete sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingProductInvoice
open Function Set Filter Lattice Cells Wilson RG MergeProof OPE OPE.Orbits OPE.Cards Spec PhysMS
open RG16 RG16.Literal Trace.Physical.GermGraph WilsonMasterReportingWords
open PhysicalNext.Repeat.Legato MergeProof.Accent FilteredIntrinsicGramReadout
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

theorem signed_sum {K : Type} [Fintype K] (H : C.Makes) (N p top : ℕ) (ht : top ≤ N)
    (Z : K → Config G (C.side N p) → ℂ) (fee : K → ℝ)
    (U : ∀ k, PaidAt C.S N p top (C.beta N p) (fee k) (Z k)) :
    PaidAt C.S N p top (C.beta N p) (∑ k, fee k) (∑ k, Z k) := by
  let tile := center C.S p ht 0
  have bill := Next.UVStress.root_sum tile (C.beta N p) Finset.univ Z
    (fun _ => (1:ℂ)) (fun k _ => (U k).ticket) (seamless H N p)
  simp only [one_smul,norm_one,one_mul] at bill
  exact ⟨ht,bill.1,bill.2.trans (Finset.sum_le_sum fun k _ => (U k).mark)⟩

variable {I : Type} [Fintype I] [Nonempty I] {d : I → ℕ}

def source (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i)) (r : ℝ)
    (m N p : ℕ) (x : I → Cover) (g : Grades d) : Config G (C.side N p) → ℂ :=
  ∏ i, C.O N p (component F R J v g r i) (location C.S m N p (x i))

theorem purchased (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (h top stop : ℕ) (starts : Stock.Tabs.opens C.path.levels 1 top stop)
    (openStop : ∀ p, Opened C h stop p)
    (η M B : ℝ) (hη : 0 < η) (hM : 0 < M) (hB : 20 < B) :
    ∃ E rem : Grades d → ℕ → ℝ,
      (∀ g, RateIs atTop C.S.scale (E g) (-h) ∧ RateIs atTop C.S.scale (rem g) (-h)) ∧
      ∀ᶠ m : ℕ in atTop, let b := port C (8*M) B (mul_pos (by norm_num) hM) m
        ∃ (hs : stop ≤ b) (hb : b+1 < m), ∀ N p (hm : m < N) (ρ : ℝ) (x : I → Cover)
          (v : (i : I) → (Climb.Bel C.book).Field (d i)), Tuple C M η B m ρ x →
          (∀ i, ‖v i‖ ≤ 1) → let r := C.S.a m*ρ
          ∃ z : Grades d → C.label h,
          (∀ g, ∃ Q, Funds C F.room.cutoff p N b h top stop (E g m) (rem g m) (weight C h m)
             (source F R J v r m N p x g) starts.1 hs ((Nat.le_succ b).trans (hb.le.trans hm.le))
             (openStop p) (z g) Q) ∧
          PaidAt C.S N p top (C.beta N p)
            ((Fintype.card (Grades d):ℝ)*(2*(stakes C top stop / weight C h m)))
            (FilteredWilsonProduct.field F R J v r m x (N,p) - C.O N p (∑ g, z g) 0) := by
  choose E rem Er rr buy using fun g : Grades d =>
    WilsonFundedReportingBranch.purchased F R J H fac pace (levels g)
      (fun i => Nat.le_of_lt_succ (g i).isLt) h top stop starts openStop η M B hη hM hB
  refine ⟨E,rem,fun g => ⟨Er g,rr g⟩,?_⟩
  filter_upwards [eventually_all.mpr buy] with m bank
  obtain ⟨hs,hb,_⟩ := bank (fun _ => 0)
  refine ⟨hs,hb,fun N p hm ρ x v pos unit => ?_⟩
  let r := C.S.a m*ρ
  let Y (g : Grades d) := source F R J v r m N p x g
  let b := port C (8*M) B (mul_pos (by norm_num) hM) m
  have entries (g : Grades d) : ∃ z Q, Funds C F.room.cutoff p N b h top stop
      (E g m) (rem g m) (weight C h m) (Y g) starts.1 hs
      ((Nat.le_succ b).trans (hb.le.trans hm.le)) (openStop p) z Q ∧
      PaidAt C.S N p top (C.beta N p) (2*(stakes C top stop / weight C h m))
        (Y g - C.O N p z 0) := by
    obtain ⟨_,_,all⟩ := bank g
    obtain ⟨_,step⟩ := all p
    exact step N hm ρ x v pos unit
  choose z Q invoice root using entries
  refine ⟨z,fun g => ⟨Q g,invoice g⟩,?_⟩
  let L := (C.linearO N p h 0).mk' _
  have field : FilteredWilsonProduct.field F R J v r m x (N,p) = ∑ g, Y g := by
    rw [FilteredWilsonProduct.field_expansion]
    rfl
  have story : FilteredWilsonProduct.field F R J v r m x (N,p) - C.O N p (∑ g, z g) 0 =
      ∑ g, (Y g - C.O N p (z g) 0) := by
    rw [field,Finset.sum_sub_distrib]
    exact congrArg (fun y => (∑ g, Y g) - y) (map_sum L z Finset.univ)
  rw [story]
  have total := signed_sum F.room.cutoff N p top
    (starts.1.trans (hs.trans ((Nat.le_succ _).trans (hb.le.trans hm.le))))
    (fun g => Y g - C.O N p (z g) 0) (fun _ => 2*(stakes C top stop / weight C h m)) root
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using total

end YM.Integration.WilsonReportingProductInvoice
