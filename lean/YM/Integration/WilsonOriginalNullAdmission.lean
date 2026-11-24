import YM.Integration.WilsonOriginalNullWalk
import YM.Integration.WilsonOriginalNullSource
import YM.QuadraticLocal.Travel

/-! Purchase on the elected original house of the real components of a displaced atom. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullAdmission
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
variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq V] {α : Type*}
variable {G : Gauge} {c n L : Side} {S : StepData c n} {P : Teller G}
  {Tube₀ : Tube G S} {X : Rep G n} {w x μ C : ℝ}
  {Q : YM.ConnectedActivityE6.Target G P} {ord : YM.ConnectedActivityE6.Target.Order G w}
variable (H : Cash w x μ L Q ord C Tube₀ X) {Y : Rep G c} {e f r s ν A K τ : ℝ} {k : ℕ}
variable (eye : Travel.Eyes H Y e ν A K k)
def portraits (M : I → Lotus.Leaf X) (j : I) : Portrait X Unit :=
  ⟨(M j).turn,(M j).weight,fun _ => M j,fun _ => rfl,fun _ => rfl⟩

theorem registered (M : I → Lotus.Leaf X) (o : Site n) (D : Support n) (b : ℝ)
    (ho : o ∈ D) (hD : ∀ j,(M j).crest = D) (hb : ∀ j,(M j).weight = b)
    (hprice : 0 < X.p.mass D b) (seats : (Fintype.card I : ℝ) ≤ K) :
    Motto (brand (portraits M) ()) (fun _ => (X.p.mass D b)⁻¹) 0 H X.p.supportExponent K A eye.sight := by
  have book (j : I) : brand (portraits M) () j = M j := Typeface.photo (portraits M) () j
  have nonneg : 0 ≤ K := (Nat.cast_nonneg _).trans seats
  refine ⟨⟨Unit,inferInstance,fun _ => o,fun _ => {()},?_⟩, eye.grant,
    le_rfl, by simp, by simp⟩
  constructor
  · exact fun _ => (inv_pos.mpr hprice).le
  · intro j _
    exact ⟨(),Finset.mem_singleton_self _, by rw [book,hD]; exact ho⟩
  · intro u
    cases u
    have fee (j : I) : Real.exp (X.p.supportExponent * coverNumber X.p.B ((brand (portraits M) () j).crest)) *
        Palette.wages (brand (portraits M) ()) (fun _ => (X.p.mass D b)⁻¹) j = 1 := by
      simp only [Palette.wages,book,hD,hb]
      rw [mul_left_comm,← RG.BudgetPoint.mass,inv_mul_cancel₀ hprice.ne']
    apply budget_finite
    · intro j
      simp only [Finset.mem_singleton_self,if_true,fee]
      norm_num
    · simpa only [Finset.mem_singleton_self,if_true,fee,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using seats
  · exact nonneg
  · intro y
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (by
        have one : 0 < Fintype.card (Site S.ratio.count) := Fintype.card_pos
        simpa using (show 1 ≤ eye.sight from one.trans_le eye.count))

def letter (C₀ : Marker.Census Unit) (a : ℂ) : Poly C₀ := Poly.send (C₀.fire ()) a

omit [Fintype I] in
theorem tap (C₀ : Marker.Census Unit) (amplitude : I → ℂ) (bound : ∀ j,‖amplitude j‖ ≤ 1)
    (hk : 1 ≤ k) : Chorus C₀ (fun _ => 1) Set.univ (fun j => letter C₀ (amplitude j)) k := by
  apply Serif.production _ _ _ (fun _ => zero_lt_one)
  · intro j; ext m
    change (Poly.prod (Poly.send (C₀.fire ()) _) (Poly.send (C₀.fire ()) _)).part m = 0
    rw [Poly.cart,if_neg]; intro h
    exact (Finset.disjoint_left.mp h.1 (Finset.mem_singleton_self ()) (Finset.mem_singleton_self ()))
  · intro j _
    constructor
    · simpa [letter] using bound j
    · simp [letter,Poly.part_send,Ne.symm (C₀.fire_hot ())]
  · intro v
    exact (Finset.card_le_univ v.val).trans (by simpa using hk)

omit [Fintype I] in
theorem placed (M : I → Lotus.Leaf X) (o : Site n) (pin : ∀ j, o ∈ (M j).crest)
    (C₀ : Marker.Census Unit) (amplitude : I → ℂ) :
    ∀ j, Push.Corrected.Width.LocalCharge (G:=G) Y.p (fun _ => S.ratio.parent o)
      (Flues.candle (portraits M) () S j) (fun _ => letter C₀ (amplitude j)) := by
  intro j
  refine ⟨fun _ _ => rfl,measurable_const,fun _ _ _ _ => rfl,?_⟩
  intro _ m _ _ _
  exact Finset.mem_image_of_mem _ (pin j)

end YM.Integration.WilsonOriginalNullAdmission
