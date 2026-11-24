import YM.Integration.WilsonSurveyedColorContact
import YM.MS.Dial.Slope

/-! Color transport for the actual MS scale-ordered correlation attached to
each separated labeled tuple. Both books have their own dimensionally filed
vacuum and singletons. The only analytic prices below are ordinary absolute
integrability of native contractions, before the color sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorContinuum
open Function Set Finset MeasureTheory
open MS
open Plane Koszul Heat Flux Landau Detect Tone City Latch Latch.Job Rake Arts Osc Snap
open Land Local.Physical Rake.Geo Tide Vane
open WilsonSurveyedColorQuotient WilsonSurveyedColorPilot WilsonSurveyedColorFlow
open WilsonSurveyedColorHearing
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
variable {I W : Type} [LinearOrder W]
local notation "Z" => constantP G I (PlanetD G)

theorem freeLine (s : ℝ) : (PlanetD G s).closed Landau.parity false := by
  intro a b q h
  rcases a with ⟨⟨a,i⟩,c⟩
  rcases b with ⟨⟨b,j⟩,d⟩
  cases a <;> cases b <;> cases i <;> cases j <;>
    first | rfl | exact False.elim (h (by change (if c=d then 0 else 0)=0; simp))

theorem propagates (μ : I → Measure QP) (F : Glade G I)
    (paid : ∀ i t, SatC (μ i) (PlanetD G t) (F i t) false) :
    filed U (sailP μ Z F) = sailP μ Z (filed U F) := by
  funext i t w
  have pick := (cent_arguments (μ i) ((pilot (D:=Axis) (P:=QP) U).sense.reaches w)
    (f:=fun q => (Landau.choir (Landau.line (Real.exp t)) id).trc q (F i t))
    (fun l => paid i t l (by simp [Course]))).2
  simp_rw [emits,WilsonSurveyedColorFlow.loop] at pick
  exact pick.symm

/- The two nonconserved internal momenta belong to the actual translated
sources. They have the original charged real measure and their own phase. -/
def Receives (μ : I → Measure QP) (x : Position W I) (X : Dance G I W) : Prop :=
  ∀ (s : Finset W), 2≤s.card → ∀ (k : ℕ) (a : I) (v : ℝ),
    SatC (μ a) (PlanetD G v) (X s k a v) false ∧
    ∀ z ∈ picks s, ∀ j ∈ antidiagonal k,
      let A := (rootX x z-rootX x s) a
      let F := X z j.1 a v
      let H := X (s\z) j.2 a v
      SatP (μ a) (PlanetD G v) F H A ∧ SatP (μ a) (PlanetD G v) (turn U F) (turn U H) A

theorem meeting {μ : I → Measure QP} {x : Position W I} {X : Dance G I W} {V : Site G I}
    (cost : Receives U μ x X) (s : Finset W) (hs : 2≤s.card) (k : ℕ) :
    filed U (multi μ x Z Z V (X s) X k s) =
      multi μ x Z Z (fun j => filed U (V j)) (fun j => filed U (X s j))
        (fun t q => filed U (X t q)) k s := by
  unfold multi lonely
  simp only [map_add,map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    funext i t
    exact connected U (Landau.line (Real.exp t)) _ _ (freeLine t)
  · refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun j hj => ?_
    funext i t
    obtain ⟨hf,hr⟩ := (cost s hs k i t).2 z hz j hj
    exact WilsonSurveyedColorContact.contact U _ (Landau.line (Real.exp t)) _ _ _ hf hr

variable {B B' : Deck G} {O : Booked B} {O' : Booked B'}
theorem continuum {A : MS_Data G O} {A' : MS_Data G O'} {u : W → Rake.Label B}
    {u' : W → Rake.Label B'} {x : W → QP} (hp : Injective x) (ν : ℝ)
    (vacuum : ∀ k, filed U (approach (frameF Unit ν) A k) = approach (frameF Unit ν) A' k)
    (inlet : ∀ w k, filed U (rowM (frameF Unit ν) A (u w) k) =
      rowM (frameF Unit ν) A' (u' w) k)
    (cost : Receives U (fun _ : Unit => planeF) (fun w _ => x w) (Dial.spine A u ν x)) :
    Dial.tour A u ν x = Dial.tour A' u' ν x := by
  have left := Dial.pin A u ν hp
  have right := Dial.pin A' u' ν hp
  apply ordinary U _ ()
  apply observed U left right inlet
  · exact fun s hs k => propagates U _ _ (fun i t => (cost s hs k i t).1)
  · intro s hs k
    have v := meeting U (V:=approach (frameF Unit ν) A) cost s hs k
    rw [funext vacuum] at v
    exact v

end YM.Integration.WilsonSurveyedColorContinuum
end
