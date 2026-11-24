import YM.RGLocalTaylor.Mayer.Powers
import YM.RGLocalTaylor.Engine.Factor

/-!
# True local Mayer Taylor coefficients with the actual Haar fields

Identify each entry used on the retained graph and license its value and full
mixed-derivative bounds (`EstFactor`). This step does *not* erase the internal
variance regulators, E profile or other masks with each head. In particular we
aren't differentiating the possibly nonanalytic protected fields themselves in
the Taylor variable. `effect = .card` would miss already the *second and higher
Taylor orders of a single kernel*! Estimates here work with the held-variable
gauge convention and inventory, not just the unmarked vacuum ratio at V=1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

namespace Mayer

abbrev badge (S : StepData c f) (i : LogIndex c f) : Head S:= Sum.inr (.inr (.inl i))

def Exponential (p : Head S) : Prop := p ∈ Set.range (badge S)
lemma noBlaze {i : Head S} (he : Exponential i) : blaze ({i}:Molecule S)=∅:= by
  obtain ⟨i,rfl⟩:=he; ext j; simp [blaze,badge]

lemma tag_small (Ξ : Utopia H j v d r C' χ) {i : Head S} (h : Exponential i) : Ξ.tag i ≤ Q.goal L s := by
  obtain ⟨i,rfl⟩:= h
  exact Ξ.uses.atom (by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]) Q.usable.le (Sum.inr (Sum.inl i)) (exChart ..)

def kernelQuote (H : Cash W s μ L Q o C T R) (y : Finset ℕ) {M : ℕ} (p : Fin (M+1)) (i : Head S) : Insert T :=
  (leg H y i).mapSmooth (indexValue p)
lemma quote_fits (y : Finset ℕ) {M : ℕ} (p : Fin (M+1)) (i : Head S) : Fits H (kernelQuote H y p i) (H.supportP i) j :=
  (fits_leg H y i j).mapSmooth (smooth j p)

variable {Ξ : Utopia H j v d r C' χ}
    {M : ℕ} {e uJ vJ discount θ K : ℝ} (h : Awning H Ξ A b discount e uJ vJ k l)
    (he : Approved K θ j M) (ht : Q.goal L s ≤ K)

-- `ρ*Q.goal ≤ 1` will pay these *different orders inside the tuple* later!
include h he ht
lemma kernel_price (y : Finset ℕ) (x : Fin (M+1)) {i : Head S} (hv : Exponential i) :
    EstFactor Ξ i (kernelQuote H y x i) A (θ*(Ξ.tag i)^(x.val+1)) ((M+4:ℝ)*r) := by
  intro F X z hX hK hχ hM hh E _ _ _ V t hz hT
  have hz' : z∈X.catastrophe (o.ξ/2) R.beta (blaze ({i}:Molecule S)) := fun w hw=>
    False.elim (notMem_empty w ((noBlaze hv) ▸ hw))
  have hp := h.estimates_leg y i F X z hX hK hχ hM hh E V t hz hT
  rw [Set.indicator_of_mem hz'] at hp ⊢
  have hf:= he.estimated _ _ _ _ hp ((tag_small Ξ hv).trans ht) x
  exact hf.climb le_rfl (le_of_eq (Eq.symm (mul_assoc ..)))

variable (hv : 0 ≤ v) (y : Finset ℕ) (z : Air f G)
variable (i : LogIndex c f) (hX : X.x=s) (hK : X.width=o.K) (hχ : X.χ=χ) (hM:X.manifest)
    (hy : Healthy (Pressure.temp s) (H.supportP (badge S i)) X.V)

include hv hX hK hχ hM hy
-- At each use in an integrated regular piece the extension is on the actual
-- logarithm and the price was in terms of these actual kernel values, not
-- a fit to the pushed result. hχ from the actual choice of calendar Chi.
lemma realizes (p : Fin M) :
    let f:= X.farLog R o.a Q.table z i
    (kernelQuote H y p.castSucc (badge S i)).value X z = f^(p.val+1) / (p.val+1).factorial ∧
      atOrder p.val ((leg H y (badge S i)).value X z) =
        iteratedDeriv (p.val+1) (fun s:ℝ=> Real.exp (f*s) - 1) 0/(p.val+1).factorial := by
  intro f
  let x:= badge S i; have hexp: Exponential x := ⟨i,rfl⟩
  let g: ℝ → Config G c := fun _=> X.V
  have hMode : Mode g 0 j v:= ⟨hv,fun i=> a_oneB G _ hv⟩
  have h0 := (h.estimates_leg y x F X z hX hK hχ hM hy _ g 0 hMode rfl).bound
  rw [show g 0=X.V from rfl,Silica.home X h.chart z H.laws.intake.positive,noBlaze hexp,
    Set.indicator_of_mem (show z∈X.catastrophe (o.ξ/2) R.beta ∅ from fun w hw=> False.elim (notMem_empty w hw))] at h0
  change ‖(leg H y x).value X z‖≤_ at h0
  have hδ : Healthy (Pressure.temp X.x) (areas R T Q.halo X.B x) X.V := by unfold Coat.B; rw [hX]; exact hy
  have hp : Real.exp f-1=(leg H y x).value X z := whereBorn X o.a R W Q.table z y (hX.symm ▸ H.laws.data.room) hM Q.buys x hδ
  have h0 : |Real.exp f-1|≤1/4:= hp.symm ▸ h0.trans (((tag_small Ξ hexp).trans ht).trans he.small)
  change indexValue p.castSucc ((leg H y x).value X z)=_ ∧ _; unfold x at hp ⊢
  rw [← hp]; exact ⟨Mayer.index_interior p f h0,true_exponent_taylor p.val f h0⟩
end Mayer
end YM.RGLocalTaylor
