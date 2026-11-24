import YM.Integration.WilsonReceivedCompulsoryCancellation

/-! Two genuine accounted hard alternatives on one addressed physical gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryPairing
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger
open RemainderComparison.WickReps
open scoped Topology BigOperators Classical


open PhysicalNext.Repeat.Lotus

variable {G : Gauge} {n c : Side} {P : Rep G n} {S : StepData c n}
    {V I α : Type} [DecidableEq V] [Countable I] {R : Marker.Census V} {o : V → Site n}
variable (E : Lamps α I G P.p o R)
variable (A K : Hard α P.p P.activities.forced P.activities.K o R)

private def choose (A K : Hard α P.p P.activities.forced P.activities.K o R) :
    Hard (Bool × α) P.p P.activities.forced P.activities.K o R where
  hard := fun t => if t.1 then K.hard t.2 else A.hard t.2
  locality := by
    rintro ⟨b,t⟩ i
    cases b
    · exact A.locality t i
    · exact K.locality t i
  charged := by
    rintro ⟨b,t⟩ i U
    cases b
    · exact A.charged t i U
    · exact K.charged t i U
  quiet := by
    rintro ⟨b,t⟩ i U
    cases b
    · exact A.quiet t i U
    · exact K.quiet t i U

/-- Both branches use the same addresses, masks, vacuum and soft rows. -/
def gallery (E : Lamps α I G P.p o R) (A K : Hard α P.p P.activities.forced P.activities.K o R) : Gallery (Bool × α) I o P R :=
  ⟨E.pullback Prod.snd,choose A K⟩

variable (w : V → ℝ) (positive : ∀ v, 0 < w v) {b d₀ d₁ : ℝ}

omit [Countable I] in
include positive in
/-- The pathwise choice under one physical seal costs the two enrolled hard
wallets in sum. The complete soft budget stays on its original address. -/
theorem sealed (U : Travel.Seal (⟨E,A⟩ : Gallery α I o P R) w b d₀) (W : Travel.Seal (⟨E,K⟩ : Gallery α I o P R) w b d₁) :
    Nonempty (Travel.Seal (gallery E A K) w b (d₀+d₁)) := by
  let book := fun j => U.crown j+W.crown j
  refine ⟨⟨U.supE,book,U.perE,fun t i => U.coverage t.2 i,?_,?_,U.perE,?_⟩⟩
  · rintro j ⟨b,t⟩ F s
    have h₀ := U.looks j t F s
    have h₁ := W.looks j t F s
    change _ ≤ ((U.crown j+W.crown j).part s).re ∧ ((U.crown j+W.crown j).part s).im=0
    simp only [Poly.part_plus,Complex.add_re,Complex.add_im,h₀.2,h₁.2]
    refine ⟨?_,add_zero 0⟩
    cases b
    · exact h₀.1.trans (le_add_of_nonneg_right ((norm_nonneg _).trans h₁.1))
    · exact h₁.1.trans (le_add_of_nonneg_left ((norm_nonneg _).trans h₀.1))
  · exact U.payment.bright
  · intro root
    apply budget_mono (budget_plus (U.payment.dusk root) (W.payment.dusk root))
    · intro j
      split
      · exact mul_nonneg (Poly.nonnegative positive _) (Real.exp_pos _).le
      · exact le_rfl
    · intro j
      dsimp only
      split
      · rw [←add_mul]
        exact mul_le_mul_of_nonneg_right (Poly.addition positive _ _) (Real.exp_pos _).le
      · simp

variable {b' : ℝ} (U : Travel.Seal (gallery E A K) w b b') (slots : HasSlots P.p P.activities)

/-- Regular source leaves are literally equal at the two selections inside
the single purchased actor. -/
private abbrev listed (C : Gallery (Bool × α) I o P R) (w : V → ℝ)
    (positive : ∀ v, 0 < w v) (U : Travel.Seal C w b b') (slots : HasSlots P.p P.activities) :=
  Trigger.listCosts C w positive slots U.supE U.crown (Travel.sighting C w U) U.looks

theorem regular (t : α) (j : Trigger.Table (gallery E A K) × Bool) (k : ℕ)
    (h : ((listed (gallery E A K) w positive U slots) j).wing = Wing.logKey k) : brand (listed (gallery E A K) w positive U slots) (false,t) j = brand (listed (gallery E A K) w positive U slots) (true,t) j := by
  have leaf : ∀ (a b : Leaf P), a.turn=b.turn → a.ingredient=b.ingredient → a.weight=b.weight → a=b := by
    rintro ⟨a,b,c,d,e,f,g⟩ ⟨j,k,l,m,n,p,q⟩ rfl rfl rfl
    rfl
  rcases j with ⟨j | j,s⟩
  · exact leaf _ _ rfl rfl rfl
  · change Wing.gasKey j.val.1 = Wing.logKey k at h
    cases h

end YM.Integration.WilsonReceivedCompulsoryPairing
end
