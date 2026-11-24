import YM.Integration.MSExteriorDilation
import YM.Integration.OPETreeTests

/-! Uniform compact separation for the independent MS far residual and its
integral on an actual compact smooth complex test. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSExteriorCompactTests
open Function Set Filter MeasureTheory Real MS MS.Land MS.Rake MS.Menus MS.Tone
open Pert.Position MSExteriorDilation
open scoped BigOperators Topology Classical

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {Q : Booked B} {n m H : ℕ}

/-- The collision inequalities between the moving inner configuration and the exterior. -/
def room : Set (ℝ × ((Fin n → QP) × (Fin m → QP))) :=
  {a | ∀ i j, a.1 • a.2.1 i ≠ a.2.2 j}

theorem room_open : IsOpen (room (n := n) (m := m)) := by
  unfold room
  simp only [setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_ne_fun (continuous_fst.smul ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
    ((continuous_apply j).comp (continuous_snd.comp continuous_snd))

theorem compact_separation (K : Set (Fin n → QP)) (Z : Set (Fin m → QP))
    (hk : IsCompact K) (hz : IsCompact Z) (hi : ∀ x ∈ K, Injective x)
    (he : ∀ y ∈ Z, Injective (origin y)) :
    ∀ᶠ s : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ Z, Injective (contracted s x y) := by
  have zero : ({0} : Set ℝ) ×ˢ (K ×ˢ Z) ⊆ room := by
    rintro ⟨r,x,y⟩ ⟨hr,hx,hy⟩
    have hr0 : r = 0 := hr
    subst r
    intro i j
    rw [zero_smul]
    exact (Fin.append_injective_iff.mp (he y hy)).2.2 (0 : Fin 1) j
  obtain ⟨U,V,hU,_,h0,hV,hroom⟩ := generalized_tube_lemma isCompact_singleton (hk.prod hz) room_open zero
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero (hU.mem_nhds (h0 (Set.mem_singleton 0)))
  filter_upwards [ht] with s hs x hx y hy
  refine Fin.append_injective_iff.mpr ⟨?_,(Fin.append_injective_iff.mp (he y hy)).2.1,?_⟩
  · intro i j h
    apply hi x hx
    simpa only [stretch,smul_smul,← Real.exp_add,add_neg_cancel,exp_zero,one_smul] using
      congrArg (fun z : QP => exp s • z) h
  · exact hroom (show (exp (-s),(x,y)) ∈ U ×ˢ V from ⟨hs,hV ⟨hx,hy⟩⟩)

/-- The coordinate map used by the original `Fountain.score` and `MS.Dial.tour`. -/
abbrev positions (x : Points n) : Fin n → QP := fun a => Theater.out (x a)

theorem continuous_positions : Continuous (positions (n := n)) := by
  apply continuous_pi
  intro i
  exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
    ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)).continuous)

variable (M : MS_Data G Q) (R : Fin n → Label B) (L : Fin m → Label B)

/-- A common bound for every test point and the entire compact exterior family
integrates against the original profile, with exactly its L¹ norm as cost. -/
theorem tested (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (Z : Set (Fin m → QP))
    (hz : IsCompact Z) (he : ∀ y ∈ Z, Injective (origin y)) (μ : ℝ) (k : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (j : ℕ)
    (hf : ∀ᶠ s : ℝ in atTop, ∀ x ∈ tsupport f, ∀ y ∈ Z, ∀ v : ℝ,
      ‖far M R L (C x) v (receding s (positions x) y) (origin (stretch s y)) k‖ ≤
        K * (((1+|v|)*(1+s))^j * exp (-((H:ℝ)+1+weight L)*s))) :
    ∀ᶠ s : ℝ in atTop, ∀ y ∈ Z,
      ‖f.applyTo (fun x => near M R L (C x) μ s (contracted s (positions x) y) (origin y) k)‖ ≤
        (∫ x, ‖f x‖) * ((K*(1+|μ|)^j) * (exp (((weight R : ℝ)-H-1)*s) * (1+|s|)^(2*j))) := by
  let I := ↥(tsupport f) × ↥Z
  obtain hsep := compact_separation (positions '' tsupport f) Z (f.hasCompactSupport.image continuous_positions) hz
    (fun _ ⟨x,hx,e⟩ => e ▸ Theater.out.injective.comp (f.tsupport_subset hx)) he
  have hu : ∀ᶠ s : ℝ in atTop,∀ i : I,Injective (contracted s (positions i.1.val) i.2.val) :=
    hsep.mono fun s hs i => hs _ ⟨_,i.1.property,rfl⟩ _ i.2.property
  have hp := all_exteriors M R L (fun i : I => C i.1.val) (fun i : I => positions i.1.val)
    (fun i : I => i.2.val) μ k hu (fun i => he _ i.2.property) hK j
    (hf.mono fun s hs i v => hs _ i.1.property _ i.2.property v)
  filter_upwards [hp] with s hs y hy
  exact OPETreeTests.bound f _ _ (fun x hx => hs (⟨⟨x,hx⟩,⟨y,hy⟩⟩ : I))

end YM.Integration.MSExteriorCompactTests
