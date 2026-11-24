import YM.Integration.WilsonCanonicalReportingBranch
import YM.Integration.WilsonSignedReportSum

/-! Complete measured reporting coefficient of the filtered physical input,
with a common cutoff threshold and its signed finite Wilson error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredReportingProduct
open Function Set Filter Lattice Cells Wilson RG MergeProof OPE OPE.Orbits OPE.Cards Spec PhysMS
open RG16 RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat.Legato MergeProof.Accent
open FilteredIntrinsicGramReadout
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] [Nonempty I] {d : I → ℕ}

theorem measured (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (h top stop : ℕ) (T : RG16.Literal.Stop C h top stop) (η M B : ℝ)
    (hη : 0 < η) (hM : 0 < M) (hB : 20 < B) :
    ∀ s : ℝ, 0 ≤ s → s < 1/16 → ∀ᶠ m : ℕ in atTop,
      ∃ (hs : stop ≤ m), ∀ p, ∃ (op : Opened C h m p), ∀ N (hm : m < N)
      (ρ : ℝ) (x : I → Cover) (v : (i : I) → (Climb.Bel C.book).Field (d i)),
      Tuple C M η B m ρ x → (∀ i, ‖v i‖ ≤ 1) →
      let Y := FilteredWilsonProduct.field F R J v (C.S.a m*ρ) m x (N,p)
      Booked C N p h Y stop (hs.trans hm.le) ∧
      PaidAt C.S N p top (C.beta N p)
        ((Fintype.card (Grades d):ℝ)*((C.S.a m)^h * Real.exp (-s*C.S.scale m)))
        (Y - C.O N p (master C N p h F.room.cutoff m op hm.le
          (receipt C N p h F.room.cutoff stop m (T.doors p) op hs hm.le Y)) 0) := by
  choose E rem rc rr bank using fun g : Grades d =>
    WilsonCanonicalReportingBranch.measured F R J H fac pace (levels g)
      (fun i => Nat.le_of_lt_succ (g i).isLt) h top stop T η M B hη hM hB
  intro s hs₀ hs₁
  filter_upwards [eventually_all.mpr (fun g => bank g s hs₀ hs₁)] with m obtained
  obtain ⟨hs,hb,offers⟩ := obtained (fun _ => 0)
  let live := hs.trans ((Nat.le_succ _).trans hb.le)
  refine ⟨live,fun p => ?_⟩
  obtain ⟨op,_⟩ := offers p
  refine ⟨op,fun N hm ρ x v layout unit => ?_⟩
  let Y (g : Grades d) := WilsonReportingProductInvoice.source F R J v (C.S.a m*ρ) m N p x g
  let charge := (C.S.a m)^h * Real.exp (-s*C.S.scale m)
  have entries (g : Grades d) :
      Booked C N p h (Y g) stop (live.trans hm.le) ∧
      PaidAt C.S N p top (C.beta N p) charge
        (Y g-C.O N p (FilteredWilsonProduct.label (w:=(N,p)) F.room.cutoff
          (T.doors p) (live.trans hm.le) (Y g)) 0) := by
    obtain ⟨_,_,menu⟩ := obtained g
    obtain ⟨_,ticket⟩ := menu p
    obtain ⟨⟨z,Q,full⟩,paid⟩ := ticket N hm ρ x v layout unit
    refine ⟨full.works stop le_rfl hs,?_⟩
    unfold receipt at paid
    rw [dress_inverse] at paid
    exact paid
  have continuous (g : Grades d) : Continuous (Y g) := by
    change Continuous (∏ i, C.O N p (component F R J v g (C.S.a m*ρ) i)
      (location C.S m N p (x i)))
    rw [show (∏ i, C.O N p (component F R J v g (C.S.a m*ρ) i)
      (location C.S m N p (x i))) = fun U => ∏ i, C.O N p
      (component F R J v g (C.S.a m*ρ) i) (location C.S m N p (x i)) U
      from funext fun _ => Finset.prod_apply ..]
    exact continuous_finsetProd _ fun _ _ => C.continuousO ..
  have joined := WilsonSignedReportSum.assembled F.room.cutoff N p h stop m (T.doors p) op
    live hm.le top (T.live.1.trans (live.trans hm.le)) Y (fun _ => charge) continuous
    (fun g => (entries g).1) (fun g => (entries g).2)
  have exactField : FilteredWilsonProduct.field F R J v (C.S.a m*ρ) m x (N,p) =
      ∑ g, Y g := by
    rw [FilteredWilsonProduct.field_expansion]
    rfl
  rw [← exactField] at joined
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using joined

end YM.Integration.WilsonMeasuredReportingProduct
