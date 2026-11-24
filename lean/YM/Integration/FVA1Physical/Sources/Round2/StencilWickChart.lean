import YM.Integration.FVA1Physical.Sources.Round2.StencilWickRows
import YM.FVA2.ReindexLaplace

/-! The same finite mixed source polynomial occurs in both the live
conditional Schur integrand and the independently seeded FVA2 history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop RGComparison.Core16 RGComparison.Core16.Spool
open RGComparison.Core16.Lumen PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial
open FVA2.CityHistory MSbar MSbar.Whisk MSbar.Heath MSbar.Heath.Cottage MSbar.Bakery MSbar.Bakery.Film
open MSbar.Cacao YM.Integration.FVA1Physical.Wilson Next.SectorChange
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)
variable {c f : Side} (S : StepData c f) (F : Forest S.ratio) (o : ι → Site f)

def activeSlots := univ.filter (fun l : Slice J => legs J o l ∉ F.trunks)
def slotEdge (l : ↥(activeSlots J S F o)) : F.Free :=
  ⟨legs J o l.val,(mem_filter.mp l.property).2⟩

def slotPrices (X : Support f) (h : ∀ i,slotEdge J S F o i∈board F X)
    (j : Wire G ↥(activeSlots J S F o)) : Lake F X G := (⟨slotEdge J S F o j.1,h j.1⟩,j.2)

def slotCollect : (Future G S F × Pins G c) →L[ℝ] (↥(activeSlots J S F o)→G.Color) :=
  ContinuousLinearMap.pi fun i=> (ContinuousLinearMap.proj (R:=ℝ) (slotEdge J S F o i)).comp
    (ContinuousLinearMap.fst ℝ _ _)

theorem draped_is_shape (b : Bool) (v : Future G S F × Pins G c) :
    look b (Spool.column J o (F.drape (expLinks G _ v.1))) =
      lampShape J b (activeSlots J S F o) (slotCollect J S F o v) := by
  unfold Spool.column lampShape
  rw [←exhibition J o]
  apply congrArg (fun h=>look b (exhibit J h))
  funext l
  by_cases e : legs J o l∈F.trunks
  · have he : l ∉ activeSlots J S F o:= by simp [activeSlots,e]
    simp only [selectLinks,dif_neg he,G.mat_lieExp_zero]
    exact F.on_tree _ ⟨_,e⟩
  have he : l∈activeSlots J S F o:=by simp [activeSlots,e]
  simp only [selectLinks,dif_pos he]
  exact F.off_tree _ ⟨_,e⟩

theorem read_seed_row (b : Bool) (n : ℕ) (v : Future G S F × Pins G c) :
    PowerSeries.coeff n (Stack.read v (Stack.rise (stencilSignal S F J o b))) =
      MvPolynomial.eval (fun i : Wire G ↥(activeSlots J S F o)=> v.1 (slotEdge J S F o i.1) i.2)
        (lampRow J b (activeSlots J S F o) n) := by
  rw [group_stencil_ticket S F J o b,Stack.read_rise,lampRow_eval]
  rw [show (fun w : Future G S F × Pins G c=>look b (Spool.column J o (F.drape (expLinks G _ w.1))))=
    lampShape J b (activeSlots J S F o) ∘ slotCollect J S F o from funext (draped_is_shape J S F o b)]
  exact FVA2.GermLaplace.jet_pull _ _ (lampShape_hot J b _|>.of_le le_top) v n

theorem drawn_is_shape (X : Support f) (h : ∀ i,slotEdge J S F o i∈board F X)
    (V : Config G f) (m w : SpaceP F X G) (g : ℝ) (b : Bool) :
    look b (tally J o (draw F X V m g w)) =
      lampShape J b (activeSlots J S F o) (Lumen.vector (fun i=>(m+g•w) (slotPrices J S F o X h i))) := by
  let U:=draw F X V m g w
  have turn : tally J o U=tally J o (canoe (S:=S) F U):=(tally_invariant J o (F.foldAt U) U).symm
  unfold lampShape
  change look b (tally J o U)=_
  rw [turn,←exhibition J o]
  apply congrArg (fun s=>look b (exhibit J s))
  funext i
  by_cases e : legs J o i∈F.trunks
  · have he : i∉activeSlots J S F o:=by simp [activeSlots,e]
    rw [selectLinks,dif_neg he,G.mat_lieExp_zero]
    exact F.compress U _ e
  have he : i∈activeSlots J S F o:=by simp [activeSlots,e]
  rw [selectLinks,dif_pos he]
  exact tape_it F X V m g w ⟨slotEdge J S F o ⟨i,he⟩,h _⟩

/-- One genuine portal numerator insertion before averaging. The estimate applies on
every sample of the Schur measure meeting the field-size condition. The same stencil
Taylor rows seed FVA2 by `read_seed_row`. Constants are chosen before the forest. -/
theorem drawn_remainder (b : Bool) (n : ℕ) :
    ∃ δ C:ℝ, 0<δ ∧ 0≤C ∧ ∀ {c f : Side} (S : StepData c f) (F : Forest S.ratio)
      (o : ι → Site f) (X : Support f) (h : ∀ i,slotEdge J S F o i∈board F X)
      (V : Config G f) (m w : SpaceP F X G) (g : ℝ), 0<g →
      let A:=activeSlots J S F o;let s:=slotPrices J S F o X h
      let v:=fun i=>(g⁻¹*m (s i)+ w (s i))
      g*‖Lumen.vector v‖≤δ →
      ‖look b (tally J o (draw F X V m g w)) -
        ∑ j∈Finset.range (n+1),g^j*MvPolynomial.eval v (lampRow J b A j)‖
          ≤ C*‖Lumen.vector v‖^(n+1)*g^(n+1) := by
  choose δ C hδ hC paid using fun A : Finset (Slice J)=>lampRows_remainder J b A n
  let z:=Finset.univ.inf' Finset.univ_nonempty δ
  let K:= ∑ A:Finset (Slice J), C A
  refine ⟨z,K,(Finset.lt_inf'_iff _).2 (fun i _=>hδ i),sum_nonneg (fun i _=>hC i),?_⟩
  intro c f S F o X live V m w g hg A s v room
  have δ₀ : z≤δ A:= Finset.inf'_le _ (mem_univ A)
  have C₀ : C A≤K:= single_le_sum (fun i _=>hC i) (mem_univ A)
  rw [drawn_is_shape J S F o X live V m w g b]
  have eq : Lumen.vector (fun i=>(m+g•w) (slotPrices J S F o X live i)) = g • Lumen.vector v := by
    funext i; apply PiLp.ext;intro k
    change m (s (i,k))+g*w (s (i,k))=g*(g⁻¹*m (s (i,k))+w (s (i,k)))
    rw [mul_add,←mul_assoc,mul_inv_cancel₀ hg.ne',one_mul]
  rw [eq]
  exact (paid A v g hg (room.trans δ₀)).trans (by gcongr)

end YM.Integration.FVA1Physical.Round2.Curvature
