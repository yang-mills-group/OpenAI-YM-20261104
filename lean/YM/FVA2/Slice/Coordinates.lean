import YM.FVA2.Fourier.PositionRange
import YM.Pert.Lattice.Action

/-! # Field space of the Landau-gauge MS Wilson Wick contraction at finite mesh

We use the real LinkP geometry, already present for a Feynman tilt in `YM.Pert.Orb`. We do not
use the Feynman tilt. `divB` on that subspace is the full-torus condition.
In the `Pert.Orb` sign convention (`grad f(x,i)=f(x)-f(x+e_i)`), it is adjoint
to `grad`. See `by_parts` in `FVA2/Orbit/Land.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Finset Lattice
open MS MS.Plane MS.Koszul MS.City MS.Orbit MS.Landau MS.Tone
open Pert Orb
open scoped BigOperators Matrix
variable {G : Gauge} {n : Side}
local notation "E" => FixedMode G n
local notation "C" => G.ColorIndex
local notation "A" => MS.Landau.gauge

/-- The real Landau slice. -/
abbrev Transverse (G : Gauge) (n : Side) := ↥(LinearMap.ker (dLin (G:=G) (n:=n)))
/-- Mean-zero inversion-even infinitesimal site gauges. -/
abbrev SiteGhost (G : Gauge) (n : Side) := ↥(Mean G n)

/-- Boson, then antighost, ghost. This space is used for linear algebra; the last two coordinates
carry *odd* Wick-sector signs. -/
abbrev Directions (G : Gauge) (n : Side) := Transverse G n × SiteGhost G n × SiteGhost G n

local notation "L" => Transverse G n
local notation "Z" => SiteGhost G n

/-- Include the transverse bosons in full periodic link log-coordinates. -/
def includeA (G : Gauge) (n : Side) : Transverse G n →ₗ[ℝ] (Orb.Links n → G.Color) :=
  (LinkP G n).subtype.comp (LinearMap.ker dLin).subtype

def place (v : Directions G n) (i : E) : ℝ := match i with
  | (((some i,false),c),x) => v.1.val.val (x,i) c
  | (((some i,true),c),x) => (gM v.2.1).val (x,i) c
  | (((none,false),c),x) => v.2.2.val x c
  | (((none,true),_),_) => 0

def fieldDir (G : Gauge) (n : Side) : Directions G n →ₗ[ℝ] (FixedMode G n → ℝ) where
  toFun := place
  map_add' a b := by
    funext j; rcases j with ⟨⟨⟨_|i,x⟩,c⟩,p⟩
    all_goals cases x <;> simp [place, map_add]
  map_smul' c a := by
    funext j; rcases j with ⟨⟨⟨_|i,x⟩,u⟩,p⟩
    all_goals cases x <;> simp [place]

theorem div_none (v : L) : Pert.Orb.divB v.val.val = 0 :=
    congr_arg Subtype.val (show dLin v.val = 0 from v.property)
theorem formT (v : L) (x : Site n) (i : Axis) : v.val.val (-x-step i,i) = -v.val.val (x,i) := v.val.property (x,i)
theorem evenZ (v : Z) (x : Site n) : v.val (-x) = v.val x := (show v.val ∈ EvenSite G n ∧ _ from v.property).1 x
lemma sum_none (v : Z) (c : C) : ∑ x, v.val x c = 0 := by
  have h := congr_arg (fun y : G.Color => y c) (sumM v)
  simpa [WithLp.ofLp_sum, Finset.sum_apply] using h
variable (v : Directions G n)
theorem direction_A (x : Site n) (c : C) (i : Axis) : fieldDir G n v ((A i,c),x)= includeA G n v.1 (x,i) c:= rfl

theorem in_position : Fourier.Position (fieldDir G n v) where
  divergence c x := by
    have he := congr_arg (fun q : G.Color => q c) (congr_fun (div_none v.1) x)
    simp only [divB, WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply,Pi.zero_apply,PiLp.zero_apply] at he
    exact he
  one_form c x i := congr_arg (fun q : G.Color => q c) (formT v.1 x i)
  even_ghost c x := congr_arg (fun q : G.Color => q c) (evenZ v.2.2 x)
  mean_ghost c := sum_none v.2.2 c
  B _ _ := rfl
  exact_form c := ⟨fun x=> v.2.1.val x c, fun x=> congr_arg (fun q : G.Color => q c) (evenZ v.2.1 x), sum_none v.2.1 c, fun x i=> rfl⟩

lemma gM_injective : Injective (gM (n:=n) (G:=G)) := fun _ _ h => mean_inj (congr_arg (dLin (G:=G) (n:=n)) h)

lemma field_inj : Injective (fieldDir G n) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext; apply Subtype.ext; funext ⟨z,i⟩; apply PiLp.ext; intro c; exact congr_fun h ((A i,c),z)
  apply Prod.ext
  · apply gM_injective; apply Subtype.ext; funext ⟨z,i⟩; apply PiLp.ext; intro c; exact congr_fun h ((anti i,c),z)
  apply Subtype.ext; funext z; apply PiLp.ext; intro c; exact congr_fun h ((ghost,c),z)

/-- Construct a real site ghost from its components. -/
def toGhost (v : Site n→C→ℝ) (he : ∀ x c, v (-x) c = v x c) (hs : ∀ c, ∑ x, v x c=0) : Z := by
  refine ⟨ fun x => WithLp.toLp _ (v x), ⟨fun x=> ?_, ?_⟩⟩
  · exact congr_arg (WithLp.toLp _) (funext (he x))
  · change (∑ x:Site n, LinearMap.proj (φ:=fun _=>G.Color) (R:=ℝ) x) _ = 0
    rw [LinearMap.sum_apply]; apply PiLp.ext; intro c
    simp_rw [WithLp.ofLp_sum, Finset.sum_apply,LinearMap.proj_apply]; exact hs c

lemma position_real {y : E→ℝ} (h : Fourier.Position y) : ∃ v, fieldDir G n v = y := by
  let a (i : Edge (Site n)) : G.Color := WithLp.toLp _ fun c => y ((A i.2,c),i.1)
  let X : ↥(LinkP G n) := ⟨ a, fun x => by apply PiLp.ext; intro c; exact h.one_form c x.1 x.2 ⟩
  let l : Transverse G n := ⟨ X, by
    rw [LinearMap.mem_ker]; apply Subtype.ext; funext p; apply PiLp.ext; intro c
    change divB a p c=0; unfold divB
    rw [WithLp.ofLp_sum, Finset.sum_apply]; exact h.divergence c p ⟩
  let k := toGhost (fun x c => y ((ghost,c),x)) (fun x c=> h.even_ghost c x) h.mean_ghost
  choose f hf hc hx using h.exact_form
  let j := toGhost (fun x c => f c x) (fun x c=> hf c x) hc
  refine ⟨ (l,j,k),?_⟩
  funext i; rcases i with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> (first | rfl | exact (h.B c p).symm | exact (hx c p i).symm)
end YM.FVA2.Slice
