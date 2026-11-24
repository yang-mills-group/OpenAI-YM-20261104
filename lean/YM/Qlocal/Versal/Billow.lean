import YM.Qlocal.Versal.Missed
import YM.Qlocal.Switch
import YM.RGComparison01.Marks.Emerson
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal
open Filter Function Lattice RG Wilson Finset MeasureTheory Matrix
open Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
  Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
  Animals Control Window Coat Footprint Pulse Itinerary Blaze Scroll Vine Polar Frond
  Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas
  Ursell Trees Height Sail PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RGComparison01 RGComparison01.Pledge Checks Foreman Baked Palette Pillow Resin Season March
variable {G : Gauge} {ι Ω : Type} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {R : RG.Rep G f}
    {W β μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {H : Cash W β μ L Q o C T R} {d r a e b kα δ : ℝ} {n j : ℕ} {χ : Chi}

-- A single physical layout of real (not complexified-coupling) tails.
variable {M : ι → Leaf R} {D : Ω → ι → Leaf R}
open RGComparison01 RGComparison01.Pledge Stowe Luggage
namespace Roster
variable (H) (h:Roster M D)
local notation "J"=> h.castLabel H
variable (R':Ribbon R n) (p:BudgetPoint)(x:Ω)(k m r:ℕ)[Fintype ι]
lemma omit'_iff (i:Cl M H): Luggage.miss (D x) H R' r k m (J x i) ↔ Luggage.miss M H R' r k m i:= Iff.and Iff.rfl (not_congr (h.file H (Drawing.cabinet H R') _ _ _ _ _))
set_option quotPrecheck false
local notation "n0"=> crop H h
lemma miss {g:ι→ℝ}(he: UniformRooted (origins M H) (crop H h g (Luggage.miss M H R' r k m) χ) p a d) : Rooted (origins (D x) H) (Checks.treat (Luggage.miss (D x) H R' r k m) (χ:=χ) (ρ:=g)) p a d := by
 obtain ⟨v,hv,hW⟩:= he.specializes x; refine ⟨v ∘ (J x).symm, fun i=>?_, fun i=>?_⟩
 · obtain ⟨i,rfl⟩:= (J x).surjective i; rw [Function.comp_apply,Equiv.symm_apply_apply,h.geometry,show Checks.treat (Luggage.miss (D x) H R' r k m) (χ:=χ) (ρ:=g) (J x i)=n0 g (Luggage.miss M H R' r k m) χ x i from ?_]; exact hv i
   unfold crop Checks.treat; exact if_congr (h.omit'_iff ..) rfl rfl
 convert budget_pull (castLabel H h x).symm (castLabel H h x).symm.injective (hW i) using 1; ext j; have hh:(origins M H ((J x).symm j)) = origins (D x) H j:= by rw [← h.geometry H x, Equiv.apply_symm_apply]
 rw [hh,Function.comp_apply]
open Primitive
lemma stance (g:ι→ℝ)(h0:UniformRooted (origins M H) (entry H h g χ) p a b) (hM:∀ x i,Pillow.pottery (D x) g χ (h.castLabel H x i) = masked p.threshold (origins M H i) (entry H h g χ x i)) : Lanes.Shed H (D x) g p χ:= by
 constructor
 · intro i; exact Rooted.viable (h.retag _ _ H _ _ h0) _ -- name
 intro i; obtain ⟨i,rfl⟩:= (h.castLabel H x).surjective i; exact hM ..
end Roster
end YM.Qlocal
