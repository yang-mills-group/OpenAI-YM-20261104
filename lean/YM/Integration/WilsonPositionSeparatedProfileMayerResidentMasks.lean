import YM.Integration.WilsonPositionSeparatedProfileMayerLeading

/-! Exact admissible old heads of the original Taylor prescription, before every Gaussian or thermal estimate. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerResidentMasks
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

theorem eligible (A:Team R) {p:Molecule S} (legal:authorized H p)
    (relative:Mayer.Start (p \ A.signs S)):Mayer.Start p:=by
  classical
  have noSeed:p.toLeft=∅:=by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨z,hz⟩
    have inside:Sum.inl z∈p:=Finset.mem_toLeft.mp hz
    by_cases placed:Sum.inl z∈A.signs S
    · obtain ⟨a,_,eq⟩:=Finset.mem_image.mp placed
      cases ht:a.turn <;> simp only [ht,Wing.badge] at eq <;> cases eq
    · obtain ⟨i,eq⟩:=relative _ (Finset.mem_sdiff.mpr ⟨inside,placed⟩)
      cases eq
  intro i hi
  by_cases placed:i∈A.signs S
  · obtain ⟨a,_,eq⟩:=Finset.mem_image.mp placed
    rw [←eq]
    cases ht:a.turn with
    | logKey v => exact ⟨.inl (.inl v),rfl⟩
    | gasKey v =>
      exfalso
      have hit:v∈Matter.own p:=(Matter.literal p v).mpr (by simpa only [←eq,ht,Wing.badge] using hi)
      obtain ⟨z,witness⟩:=(R.activities.forced v).inventory_ne
      obtain ⟨o,record,_⟩:=legal.2.2.2 _ hit _ witness
      unfold roster Packets.store at record
      rw [noSeed] at record
      simp at record
  · exact relative i (Finset.mem_sdiff.mpr ⟨hi,placed⟩)

theorem minimal (A:Team R) (legal:authorized H (A.signs S)):Mayer.Start (A.signs S):=by
  apply eligible A legal
  intro i hi
  simp at hi

theorem outside (A:Team R) (p:Molecule S) (u:Orders M) (regular:u.val≠M+1)
    (V:Config G c) (absent:¬authorized H p ∨ ¬Mayer.Start p):
    Laminate.column A p H (χ:=χ) M u V=0:=by
  classical
  by_cases inc:A.signs S⊆p
  · simp only [Laminate.column,if_pos inc,if_neg regular,Laminate.scopeM]
    by_cases start:Mayer.Start p
    · rw [if_pos start]
      unfold Mayer.coefficient
      apply Finset.sum_eq_zero
      intro dec _
      exact Insert.onLog_of_forbidden (absent.resolve_right (not_not.mpr start)) _ _
    · rw [if_neg start];rfl
  · simp [Laminate.column,inc]

end YM.Integration.WilsonPositionSeparatedProfileMayerResidentMasks
