import YM.Integration.WilsonOriginalForcedMarkerMerger

/-! Actual counted Wick/Mayer scenes are affine in the common amplitude of
any collection of incoming factors carrying a given square-zero label. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalForcedMarkerRows
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe WilsonOriginalHardOwnerReweight WilsonForcedMarkerLine
open scoped Topology BigOperators Classical

variable {V ι : Type} [DecidableEq V] {R : Marker.Census V} {v : V} {q:ℂ}

theorem scalar {a b c:Poly R} (z:ℂ) (A:Line v q a b c) :
    Line v q (z • a) (z • b) (z • c) := by
  simpa only [Poly.product_bead] using product (same (Poly.bead R z)) A

theorem rows {a b c:ι→Poly R} (A:∀ i,Line v q (a i) (b i) (c i))
    (ha:Summable a) (hc:Summable c) :
    Line v q (∑'i,a i) (∑'i,b i) (∑'i,c i) := by
  have hd := hc.sub ha
  constructor
  · intro m hm
    rw [←hc.tsum_sub ha,Poly.share hd]
    exact (tsum_congr (g:=fun _=>0) (fun i=>(A i).marked m hm)).trans tsum_zero
  · simp_rw [fun i=>(A i).value]
    rw [ha.tsum_add (hd.const_smul q),hd.tsum_const_smul q,hc.tsum_sub ha]

def omitOwner (use:ι→Prop) (i:ι):ℝ := if use i then 0 else 1

variable (use:ι→Prop) (z:ι→Poly R)
theorem word {θ:ℝ} {depth:ℕ} (h:∀ i,use i→pinned v (z i)) (t:Multiset ι) :
    let colored := Verse.controls Set.univ z t
    let quote := Real.exp (θ*depth)
    Line v ((quote:ℂ)⁻¹) (((t.map (omitOwner use)).prod:ℂ) • colored)
      colored (((t.map (raise use θ depth)).prod:ℂ) • colored) := by
  dsimp only
  have node i : Line v (↑(Real.exp (θ*depth)):ℂ)⁻¹
      ((omitOwner use i:ℂ) • z i) (z i) ((raise use θ depth i:ℂ) • z i) := by
    by_cases u:use i
    · simp only [omitOwner,raise,if_pos u,Complex.ofReal_zero,zero_smul]
      have positive := Complex.ofReal_ne_zero.mpr (Real.exp_pos (θ*depth)).ne'
      constructor
      · intro m hm
        simp only [sub_zero,Poly.part_smul,h i u m hm,mul_zero]
      · rw [sub_zero,zero_add,smul_smul,inv_mul_cancel₀ positive,one_smul]
    · simp only [omitOwner,raise,if_neg u,Complex.ofReal_one,one_smul]
      exact same _
  induction t using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero,Multiset.prod_zero,Complex.ofReal_one,one_smul]
      using same (v:=v) (q:=(↑(Real.exp (θ*depth)):ℂ)⁻¹) (Verse.controls Set.univ z 0)
  | cons i s ih =>
    have combine := product (node i) ih
    simp only [Verse.controls,Multiset.map_cons,Multiset.prod_cons,Set.mem_univ,if_true,
      Complex.ofReal_mul,smul_mul_smul_comm] at combine ⊢
    exact combine

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G}
    {T : Tube G S} {A : Rep G f} {W x μ C :ℝ} {Q : ConnectedActivityE6.Target G P}
    {o : ConnectedActivityE6.Target.Order G W} {α:Type*}
variable (H : Cash W x μ L Q o C T A) (χ : Chi) (M : ι → Portrait A α) (u:α)
    {A' : Rep G f} (H' : Cash W x μ L Q o C T A') (D : Match.Alliance H' H 1 0)
    (E : ℕ → RegularAddress c) (b : ℕ → Config G c → ℝ) [Countable ι]

local notation "stock" l:max => kettle H χ M u l Set.univ 0 H' D E b
local notation "quiet" => (fun _ : ι=> (1:ℝ))
theorem reprice (l:ι→ℝ) (y:α) (i:ℕ) (Z:Config G c) :
    (stock l).glow y i Z = (((stock quiet).score i).map l).prod * (stock quiet).glow y i Z := by
  let e:=funnel H M u H' D
  by_cases hin:i∈Set.range e
  · obtain ⟨p,rfl⟩:=hin
    unfold kettle; dsimp only
    rw [stuffed,stuffed,stuffed]
    have fixed (r:ι→ℝ) : sits Set.univ r 0 = r := by funext j; simp [sits,Verse.marked]
    rw [fixed,fixed,Flues.written H χ M u y p]
    simp [Verse.emit,Verse.stock]
  · unfold kettle; dsimp only
    rw [blank _ _ hin,blank _ _ hin,blank _ _ hin]
    simp

theorem signed {θ :ℝ} {depth:ℕ} (h:∀ i,use i→pinned v (z i)) (y:α) (i:ℕ) (Z:Config G c) :
    Line v (↑(Real.exp (θ*depth)):ℂ)⁻¹
      ((stock (omitOwner use)).song Set.univ z y Z i) ((stock quiet).song Set.univ z y Z i)
      ((stock (raise use θ depth)).song Set.univ z y Z i) := by
  let l := (stock quiet).score i
  have price (t:ι→ℝ) :
      (stock t).song Set.univ z y Z i =
      (↑((stock quiet).glow y i Z):ℂ) • (↑((l.map t).prod):ℂ) • Verse.controls Set.univ z l := by
    unfold Yard.song
    rw [reprice H χ M u H' D E b t y i Z,Complex.ofReal_mul,smul_smul,mul_comm]
    rfl
  rw [price,price,price]
  simpa [l] using scalar (↑((stock quiet).glow y i Z):ℂ) (word use z h l (θ:=θ) (depth:=depth))

end YM.Integration.WilsonOriginalForcedMarkerRows
end
