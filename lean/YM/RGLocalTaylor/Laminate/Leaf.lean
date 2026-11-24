import YM.RGLocalTaylor.Engine.Factor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Gnomon
import YM.RGLocalTaylor.Mayer.Wing
/-!
# Aperture at a marked `Leaf`: SAME integration ticket as for all log costs

`Laminate.power` enters the estimator as an `Insert`. In production scenes it is not
multiplied by any arbitrary background smoothing. Source may even be measurable
only: derivative estimation later still in the native output supported norm. Fits
proofs and estimates adapted from Lotus/{Spectrum,Class,Palette} & Daisy/Charm
& previous unmarked aperture. Does not require assuming mean-cost/Haar from
analysis on the birth.
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy

namespace Laminate

def power (_H : Cash W s μ L Q o C T R) (M : Leaf R) : Insert T :=
  { value := fun {_} X z=> M.paidU X o.a (worldZ X R.beta z) }
private lemma power_floret (M:Leaf R) (X : Coat T F) (y : Finset ℕ)(z : Air f G) :
    (power H M).value X z=M.floret X {M.turn.badge S} W o.a Q.table y Q.halo z := by
  rw [Leaf.floret,if_pos (mem_singleton_self _), erase_singleton, floating,Finset.prod_empty,mul_one]; rfl

lemma power_fit (H : Cash W s μ L Q o C T R) (M : Leaf R) (j : ℕ) : Fits H (power H M) (H.supportP (M.turn.badge S)) j := by
  let I : Molecule S:= {M.turn.badge S}
  constructor
  · intro F X X' hX hK Y z z' hh hB
    have hζ : Intake P T X.x R := hX.symm ▸ H.laws.intake; have ht:Room P S T X.x:= hX.symm ▸ H.laws.data.room
    rw [power_floret _ _ (∅),power_floret M X' (∅)]; apply M.census X I hζ ht Q.buys hB
    unfold I ground; rw [singleton_biUnion,show X.B=radiusB s from congr_arg _ hX]; exact hh
  · intro F X hX hK E _ V Z z hV hZ hz
    have hb : ShellAccess S G X.x W X.width o.γ := by rw [hX,hK]; exact H.laws.data.access
    have hζ:= M.drift_b X (k:=∅) (l:=Q.halo) (a:=o.a) I Z V z hb (hX.symm ▸ H.laws.intake) Q.table_exists hV hZ hz
    simp_rw [power_floret _ _ (∅)]; exact hζ
  · intro F X hX hK h z w
    have he : Intake P T X.x R := hX.symm ▸ H.laws.intake
    have hb : ShellAccess S G X.x W X.width o.γ := by rw [hX,hK]; exact H.laws.data.access
    dsimp only [power]; rw [Stained.flight X z he.ready hb]; unfold Leaf.paidU Leaf.fond; rw [Hues.banks X z _, M.glows]; exact congr_arg _ (show _=X.enforce _ _ _ from Hues.mandate X z (2*o.a) _ (X.plaza _))
  intro F X hX _ _ E _ _ _ V x A b hA ha hg
  let H' : Cash W X.x μ L Q o C T R := hX.symm ▸ H
  have hv: 8*o.a*Pressure.fiery G X.x S.patch.L ≤ A/2:= by rw [hX,H.laws.data.funds.length_eq]; exact ha
  refine (M.supple X I H' hg hA hv).congr (Eventually.of_forall fun i z=> (power_floret (H:=H) M _ (own I) _).symm)

abbrev wingEst (i:Wing) (S : StepData c f) := i.badge S
lemma wingSafe (M:Leaf R) : blaze ({M.turn.badge S}:Molecule S)=∅:= by
  cases M.turn <;> ext <;> simp [Wing.badge,blaze]

variable {Ξ : Utopia H j v d r C' χ} {discount e uJ vJ:ℝ}
set_option maxHeartbeats 320000 in
lemma afford (h : Awning H Ξ A b discount e uJ vJ k l) (M:Leaf R) : EstFactor Ξ (M.turn.badge S) (power H M) A M.weight vJ := by
  intro F X z hX hK hχ hM hh E _ _ _ V y hp ht
  obtain ⟨ht',_,hθ⟩:= h.course_prices F X z hX hK hχ hM E V y hp ht
  let u:= worldZ X R.beta z; let f t := steer X A u (V t); let i:= M.turn.badge S
  let g t:= M.fond (vary X (V t)) o.a (f t) (X.input u)
  have hV : ∀ᶠ t in 𝓝 y,(power H M).value (vary X (V t)) (course X A R.beta z (V t))=g t:= by
    filter_upwards [ht'.patch] with t hV; unfold g power; dsimp only; rw [ht'.moving]; exact M.canv (vary X (V t)) _ _ _ (plastic hV ht'.pulse)
  have he: z∈ X.catastrophe (o.ξ/2) R.beta (blaze ({M.turn.badge S}:Molecule S)):= by rw [wingSafe]; exact fun _ h=>False.elim (notMem_empty _ h)
  let p:= areas R T 0 X.B i; let q:=H.supportP i
  have hx : X.B=radiusB s:=congr_arg radiusB hX
  have hh':p⊆q:=by change areas R T 0 X.B (M.turn.badge S) ⊆ areas R T Q.halo (radiusB s) (M.turn.badge S); simp_rw [M.turn.badge_area,hx]; exact Corona.halo_mono (by simp) (Finset.Subset.refl _)
  rw [Set.indicator_of_mem he]; apply Brush.shimmy (f:=g) _ hV -- args check
  have h' := ((Brush.certified (d:=0) (x:=y) (k:=j) (le_refl 0) (M.ingredient (X.input u))).climb (M.earn _) (le_refl _)).paints (hθ p q hh')
  rw [mul_one,zero_add] at h'; refine h'.climb le_rfl (mul_le_mul_of_nonneg_left ?_ h.cSc)
  rw [hx]; unfold q i; rw [← Daisy.sparkPath]
  exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one)
end Laminate
end YM.RGLocalTaylor
