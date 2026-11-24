import YM.Integration.WilsonFundedReportingBranch
import YM.RG16.Unmasked.Exit

/-! The signed error is measured against the intrinsic Wilson report of the
same physical branch at the same cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCanonicalReportingBranch
open Function Set Filter Lattice Wilson RG MergeProof OPE OPE.Orbits OPE.Cards Spec PhysMS
open RG16 RG16.Literal Trace.Physical.GermGraph WilsonMasterReportingWords
open PhysicalNext.Repeat.Legato MergeProof.Accent
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] [Nonempty I] {d : I → ℕ}

theorem measured (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (e : I → ℕ) (leGrade : ∀ i, e i ≤ d i) (h top stop : ℕ)
    (T : RG16.Literal.Stop C h top stop) (η M B : ℝ)
    (hη : 0 < η) (hM : 0 < M) (hB : 20 < B) :
    ∃ E rem : ℕ → ℝ, RateIs atTop C.S.scale E (-h) ∧ RateIs atTop C.S.scale rem (-h) ∧
      ∀ s : ℝ, 0 ≤ s → s < 1/16 → ∀ᶠ m : ℕ in atTop,
      let b := port C (8*M) B (mul_pos (by norm_num) hM) m
      ∃ (hs : stop ≤ b) (hb : b+1 < m), ∀ p, ∃ (op : Opened C h m p),
        ∀ N (hm : m < N) (ρ : ℝ) (x : I → Cover)
          (v : (i : I) → (Climb.Bel C.book).Field (d i)),
          Tuple C M η B m ρ x → (∀ i, ‖v i‖ ≤ 1) →
          let r := C.S.a m*ρ
          let Y := ∏ i, C.O N p (S.representative _ (R.cutTest (e i) (d i)
            (J r _ (v i)))) (Cells.location C.S m N p (x i))
          let live := hs.trans ((Nat.le_succ b).trans hb.le)
          (∃ z Q, Funds C F.room.cutoff p N b h top stop (E m) (rem m) (weight C h m)
            Y T.live.1 hs ((Nat.le_succ b).trans (hb.le.trans hm.le)) (T.doors p) z Q) ∧
          PaidAt C.S N p top (C.beta N p) ((C.S.a m)^h * Real.exp (-s*C.S.scale m))
            (Y - C.O N p (master C N p h F.room.cutoff m op hm.le
              (receipt C N p h F.room.cutoff stop m (T.doors p) op live hm.le Y)) 0) := by
  obtain ⟨A,Arate,room⟩ := WilsonFundedReportingBranch.joint F R J H fac.simpleGate e leGrade (B+1)
  obtain ⟨_,_,_,L⟩ := fac.costlier
  obtain ⟨E,rem,Ecost,remCost,purchase⟩ := finesse C fac.simpleGate L.toPackage F.room.cutoff
    e h top stop A Arate η M B hη hM hB pace T
  refine ⟨E,rem,Ecost,remCost,fun s hs₀ hs₁ => ?_⟩
  filter_upwards [room,purchase s hs₀ hs₁] with m credit offered
  obtain ⟨hs,hb,menu⟩ := offered
  refine ⟨hs,hb,fun p => ?_⟩
  obtain ⟨op,out,step⟩ := menu p
  refine ⟨out,fun N hm ρ x v layout unit => ?_⟩
  let r := C.S.a m*ρ
  have valid : r ∈ Icc (C.S.a m) (WilsonReportingLength.radius C (B+1) m) := by
    have one := Real.one_le_rpow (one_le_two.trans (lambda_up C m).le) (show 0 ≤ B by linarith)
    exact ⟨le_mul_of_one_le_right (C.S.a_pos m).le (one.trans layout.lo),
      mul_le_mul_of_nonneg_left layout.hi (C.S.a_pos m).le⟩
  let y (i : I) := S.representative (e i) (R.cutTest (e i) (d i) (J r _ (v i)))
  let w i := coordinates F.room.cutoff N p (e i) m (op i) hm.le (y i)
  have cost := step N hm ρ x w layout (credit r valid N p hm op v unit)
  have placed := replica F.room.cutoff N p m hm.le op x y
  change Words C F.room.cutoff e p N m w x hm.le op = _ at placed
  rw [placed] at cost
  have marked := cost.2.2
  rw [cost.2.1] at marked
  exact ⟨cost.1,T.live.1.trans (hs.trans ((Nat.le_succ _).trans (hb.le.trans hm.le))),
    marked.1,marked.2⟩

end YM.Integration.WilsonCanonicalReportingBranch
