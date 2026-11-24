import YM.Comparison.RG02.Laplace.Habit
/-!
# Select good neighborhoods for one finite-order assertion

This is **regulator-by-regulator gauge/chart invariance**: enough for the *polynomial*
 identity on whichever tag is used. No powers of Λ_N or topology of actual estimates.
 Can simultaneously announce the entire finite collection. Port for *analytic model only*;
 gauges & holding haven't changed. Ingredients conditional on branch/gap as exported.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F H : Forest S.ratio) (g c₀:ℝ)
  (W : Bulk.Colors R G f) (x : fieldDir G c 1)
variable (D : BudgetPoint) (r : ℕ)

-- returns Trial AT δ; implies trial at every smaller order of same coefficients in that aperture.
def Serves (A : Set (F.Slice G)) (t : S.Choices) (s : R.Mode): Prop :=
     ∀ B, B ⊆ A → MeasurableSet B → B∈𝓝 (1:F.Slice G) → (∀ᶠ g in along, B⊆Integral.zone K D F g x) ∧ Trial (detail (Bulk.Fk K F t W x r) s) (fun g=> (portal K F t c₀ W x (fun _=> B) g).part s) r
lemma smaller (t : S.Choices) (s : R.Mode) (A : Set (F.Slice G)) (B : Set (F.Slice G)) (h : B⊆A)
    (H : Serves K F c₀ W x D r A t s) : Serves K F c₀ W x D r B t s:= fun q hq=> H q (hq.trans h)

variable (hW : Bulk.Well W)
include hW
lemma one_look (t : S.Choices) (s : R.Mode) : ∃ A∈𝓝 (1:F.Slice G), IsOpen A ∧ Serves K F c₀ W x D r A t s := by
    obtain ⟨δ,h,H⟩:= denote K F t c₀ W x r s hW
    obtain ⟨A,ha,ht,he⟩:= aperture K F x D h
    refine ⟨A,ha,ht,fun B hb H' hq =>?_⟩
    obtain ⟨hp,hl⟩:= he _ hb H'
    exact ⟨hl,H _ hp (earns K F x B hq) (hl.mono fun t' he=> Integral.limited K F D t' x t B he H')⟩
lemma find : ∃ A : Set (F.Slice G), A∈𝓝 1 ∧ IsOpen A ∧ ∀ (t : S.Choices) (s:R.Mode), Serves K F c₀ W x D r A t s := by
    choose A hA HA H using one_look K F c₀ W x D r hW
    let U (s : S.Choices × R.Mode):= A s.1 s.2
    have hs (t): IsOpen (U t):=HA ..
    have hh : IsOpen (⋂ t:S.Choices × R.Mode, U t) := isOpen_iInter_of_finite hs
    refine ⟨_,hh.mem_nhds (Set.mem_iInter.mpr (fun i=>mem_of_mem_nhds (hA ..))),hh,fun t s=>?_⟩
    exact smaller K F c₀ W x D r t s _ _ (Set.iInter_subset U (t,s)) (H t s)

-- from common frame obtain two windows by physical rerouting. Model gauge ⇒ IDENTICAL.
omit hW in
private lemma reroute_origin : Profiles.reroute F H G 1=1 := by rw [← Work.F05.exposure_zero F]; exact Work.F05.reroute_exposure_zero ..
lemma both : ∃ A : Set (F.Slice G), A∈𝓝 1 ∧ IsOpen A ∧
    let B := Profiles.reroute F H G '' A; B∈𝓝 1 ∧ IsOpen B ∧ ∀ (t : S.Choices) (s:R.Mode), Serves K F c₀ W x D r A t s ∧ Serves K H c₀ W x D r B t s := by
   obtain ⟨U,hU,hA,ht⟩:=find K F c₀ W x D r hW; obtain ⟨Z,hZ,hB,he⟩:=find K H c₀ W x D r hW
   let ζ := Profiles.reroute F H G
   let A:= U ∩ ζ ⁻¹' Z
   have h₀: ζ 1=1:= reroute_origin ..
   have ha : IsOpen A := hA.inter (hB.preimage ζ.continuous)
   have hb : (1:F.Slice G)∈A := ⟨mem_of_mem_nhds hU,Set.mem_preimage.mpr (h₀.symm ▸ (mem_of_mem_nhds hZ))⟩
   have hv:= ζ.isOpenMap A ha
   exact ⟨A,ha.mem_nhds hb,ha,hv.mem_nhds ⟨_,hb,h₀⟩, hv, fun t s=> ⟨smaller K F c₀ W x D r t s U _ (Set.inter_subset_left) (ht t s), smaller K H c₀ W x D r t s Z _ (Set.image_subset_iff.mpr Set.inter_subset_right) (he t s)⟩⟩

lemma redirects (A : Set (F.Slice G)) (t : S.Choices) (hg : 0<g) :
   Complex.ofReal (wage K F t g c₀ x) • portal K F t c₀ W x (fun _=> A) g = Complex.ofReal (wage K H t g c₀ x) • portal K H t c₀ W x (fun _=>Profiles.reroute F H G '' A) g := by
    have hp (T : Forest S.ratio) : (↑(wage K T t g c₀ x) : ℂ) ≠ 0 := by exact_mod_cast (wage_pos K T t g c₀ x hg).ne' -- .. mid?
    unfold portal; rw [smul_smul,smul_smul,mul_inv_cancel₀ (hp F),one_smul, mul_inv_cancel₀ (hp H),one_smul]
    let Z := Actual.stack t (sample g x) (temperature g) (model g c₀ W K)
    let n := Profiles.reroute F H G
    let M:= n '' A
    have hm : A.indicator (Z∘F.drape)= M.indicator (Z∘H.drape) ∘ n := by
       funext i; by_cases h:i∈A; swap
       · exact Eq.trans (Set.indicator_of_notMem h _) (Set.indicator_of_notMem (show n i∉M from by rintro ⟨b,hb,e⟩; exact h ((n.injective e) ▸ hb)) _).symm
       rw [Function.comp_apply,Set.indicator_of_mem (Set.mem_image_of_mem _ h), Set.indicator_of_mem h]; symm
       change Z (H.drape (Precision.Profiles.wick H (F.drape i)))=_
       rw [Profiles.wears]; exact stack_rooted _ _ _ K.branches _ (fun y=> H.fold_root (F.drape i) y) (model_gauge K g c₀ W hW) _
    ext v; rw [components,components]
    change (∫ i : F.Slice G,(A.indicator (Z∘F.drape) i).part v∂F.order G) =_
    rw [hm]; exact (Profiles.spending F H G).integral_comp n.measurableEmbedding (atMark v (M.indicator (Z ∘ H.drape)))
end YM.Comparison.RG02.Laplace
