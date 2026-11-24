import YM.Integration.WilsonOriginalNullHouse
import YM.QuadraticLocal.Travel

/-! Exact marked numerator for several real source components at a single occupied address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullSource
open QuadraticLocal QuadraticLocal.Lanes
-- Use same M and data throughout. Countable ι handles address combinations per load.
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open GridRenewal.Rain
open Marker Mallow Ovens Progress.DirectedRecipe
variable {G : Gauge} {c n : Side} (S : StepData c n) {X : Rep G n}
variable {I V : Type} [Fintype I] [DecidableEq V]
variable (M : I → Lotus.Leaf X)

private def only (j : I) : Drums M S :=
  ⟨{j}, by simp [Merge.Draft]⟩

omit [Fintype I] in
private lemma faithful (key : ℕ) (hkey : ∀ j,(M j).turn=.logKey key) (j : I) (U : Config G n) :
    (Palette.team M (only S M j)).cicada U = (M j).ingredient U * X.eval U := by
  let T := Palette.team M (only S M j)
  have own : T.own = {M j} := by simp [T,Palette.team,only]
  have gas : T.gasDue = ∅ := by ext k; simp [own,hkey]
  have ingr : T.ingredients U = (M j).ingredient U := by simp [Team.ingredients,own]
  have pay (k : Finset ℕ) : T.bun k U = (M j).ingredient U * X.activities.gasOccurrence X.p k U := by
    by_cases h : X.activities.admissible X.p U k
    · simp [Team.bun,Team.bill,gas,ingr,RG.Activities.gasOccurrence,h]
    simp [Team.bun,RG.Activities.gasOccurrence,h]
  change Real.exp (X.exponent U) * (∑' k, T.bun k U) = _
  simp_rw [pay,tsum_mul_left]
  unfold RG.Rep.eval RG.Activities.gas; ring

theorem original {C : Marker.Census V} (key : ℕ) (hkey : ∀ j,(M j).turn=.logKey key)
    (l : I → ℝ) (σ : I → Poly C) (U : Config G n) :
    TuneR M Set.univ l 0 σ S U = Poly.bead C (X.eval U) +
      ∑ j, ((l j * (M j).ingredient U * X.eval U : ℝ) : ℂ) • σ j := by
  classical
  let no := Tickets.none (Palette.sign M S)
  let one := only S M
  have distinct : Injective one := by
    intro i j h; exact Finset.singleton_inj.mp (congr_arg Subtype.val h)
  have dis : no ∉ Finset.univ.image one := by
    intro h; obtain ⟨j,_,e⟩ := Finset.mem_image.mp h
    have bad : ({j}:Finset I) = ∅ := congr_arg Subtype.val e
    exact Finset.singleton_ne_empty j bad
  have list : (Finset.univ : Finset (Drums M S)) = insert no (Finset.univ.image one) := by
    ext t
    simp only [Finset.mem_univ,true_iff,Finset.mem_insert,Finset.mem_image, true_and]
    by_cases non : t.val.Nonempty
    · obtain ⟨j,hj⟩ := non; right; refine ⟨j,Subtype.ext ?_⟩
      ext i
      constructor
      · intro h; rw [Finset.mem_singleton.mp h]; exact hj
      intro hi; apply Finset.mem_singleton.mpr
      apply t.prop hi hj; simp [Palette.sign, hkey]
    left; exact Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp non)
  let price := fun j : Drums M S => (Mosaic.raw M j).paint Set.univ (Muse.sits Set.univ l 0) σ U
  have weights : Muse.sits Set.univ l 0=l := by funext i; simp [Muse.sits,Verse.marked]
  have blank : price no = Poly.bead C (X.eval U) := by
    have letters : (Mosaic.raw M no).letters = 0 := rfl
    have vacant : (Mosaic.raw M no).utter U = X.eval U := Canon.emptyWeight M no rfl U
    unfold price Verse.paint Verse.emit Verse.stock Verse.controls
    rw [letters, vacant]
    simp only [Multiset.map_zero,Multiset.prod_zero,one_mul]
    rw [← Poly.product_bead,mul_one]
  have chosen (j : I) : price (one j) = ((l j*(M j).ingredient U*X.eval U:ℝ):ℂ) • σ j := by
    have letters : (Mosaic.raw M (one j)).letters = {j} := rfl
    have value : (Mosaic.raw M (one j)).utter U = (M j).ingredient U * X.eval U :=
      faithful S M key hkey j U
    unfold price Verse.paint Verse.emit Verse.stock Verse.controls
    rw [letters,weights,value]
    simp [mul_assoc]
  change ∑' j,price j = _
  rw [tsum_fintype, list, Finset.sum_insert dis, Finset.sum_image (fun _ _ _ _ h => distinct h), blank]
  exact congr_arg (_ + ·) (Finset.sum_congr rfl fun j _ => chosen j)

end YM.Integration.WilsonOriginalNullSource
