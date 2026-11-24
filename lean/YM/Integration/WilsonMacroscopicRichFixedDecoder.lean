import YM.Integration.WilsonMacroscopicRichCompensatedSlate
import YM.MergeProof.West.News

/-! Read the canonical difference against a whole signed slate of original physical fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFixedDecoder
open Function Filter Set Lattice Wilson Cells Extraction OPE OPE.Cards PhysMS Spec
open RG MergeProof OPE.Orbits RG16 RG16.Literal Trace.Physical.GermGraph MergeProof.Accent
open FilteredIntrinsicGramReadout PhysicalNext.Repeat.Legato Next.UVStress
open WilsonMacroscopicRichCompensatedSlate
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I A : Type} [Fintype I] [Nonempty I] [Fintype A] {d : I → ℕ}

theorem original (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (h : ℕ) (η M B : ℝ) (hη : 0 < η) (hM : 0 < M) (hB : 20 < B) (W : A → Watch C) :
    ∃ top u : ℕ, ∃ T : Stop C h top u, ∃ K : A → ℝ, (∀ i,0 ≤ K i) ∧
      ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 16 → ∀ᶠ m : ℕ in atTop, ∃ (hu : u ≤ m),
      ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ (hm : m < w.1),
      ∀ (ρ : ℝ) (x : I → Cover) (v : (i : I) → (Climb.Bel C.book).Field (d i)),
        Tuple C M η B m ρ x → (∀ i, ‖v i‖ ≤ 1) →
        let Y := FilteredWilsonProduct.field F R J v (C.S.a m * ρ) m x w
        let Δ := gap F R J h u m w (T.doors w.2) (hu.trans hm.le) ρ x v
        let fee := (Fintype.card (Grades d):ℝ) * ((C.S.a m)^h * Real.exp (-σ * C.S.scale m))
        Booked C w.1 w.2 h Y u (hu.trans hm.le) ∧
        PaidAt C.S w.1 w.2 top (C.beta w.1 w.2) fee Δ ∧
        ∀ z : A → ℂ, ‖∑ i, z i * moment (C.beta w.1 w.2) (fun U => Δ U * (W i).plot w.1 w.2 U)‖ ≤
          fee * ∑ i, ‖z i‖ * K i := by
  classical
  let q := Finset.univ.sup (fun i : A => (W i).t)
  obtain ⟨_,_,_,L⟩ := fac.costlier
  obtain ⟨top,⟨⟨u,assayed⟩,big⟩⟩ := ((forStop C fac.simpleGate L.toPackage h).and (eventually_ge_atTop q)).exists
  let T := assayed h le_rfl
  have placed (i : A) : (W i).t ≤ top := (Finset.le_sup (s:=Finset.univ) (f:=fun j : A => (W j).t) (Finset.mem_univ i)).trans big
  choose K posK sale using fun i : A => Ribbons.acorns (W i) F.room.cutoff F.room.copies top (placed i)
  refine ⟨top,u,T,K,posK,?_⟩
  intro σ hσ small
  filter_upwards [WilsonMeasuredReportingProduct.measured (d:=d) F R J H fac pace h top u T η M B hη hM hB σ hσ small] with m hm
  obtain ⟨hu,hcash⟩ := hm
  refine ⟨hu,?_⟩
  filter_upwards [(largeMesh f).eventually_ge_atTop (m+1),eventually_all.mpr sale] with w live tested
  obtain ⟨op,P⟩ := hcash w.2
  refine ⟨live,?_⟩
  intro ρ x v geometry cap
  let Δ := gap F R J h u m w (T.doors w.2) (hu.trans (Nat.le_of_lt live)) ρ x v
  let fee := (Fintype.card (Grades d):ℝ) * ((C.S.a m)^h * Real.exp (-σ * C.S.scale m))
  obtain ⟨book,paid⟩ := P w.1 live ρ x v geometry cap
  simp only [receipt,dress_inverse] at paid
  have ticket : PaidAt C.S w.1 w.2 top (C.beta w.1 w.2) fee Δ := paid
  refine ⟨book,ticket,fun z => ?_⟩
  have each (i : A) : ‖moment (C.beta w.1 w.2) (fun U => Δ U * (W i).plot w.1 w.2 U)‖ ≤ fee * K i := by
    obtain ⟨_,hr⟩ := tested i
    exact (hr Δ ticket.ticket).trans (mul_le_mul_of_nonneg_right ticket.mark (posK i))
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by rw [norm_mul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (each i) (norm_nonneg _)

end YM.Integration.WilsonMacroscopicRichFixedDecoder
