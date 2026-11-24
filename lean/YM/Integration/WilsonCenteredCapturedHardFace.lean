import YM.Integration.WilsonCenteredCaptureSlots
import YM.Integration.WilsonCenteredCaptureOwnerTariff
import YM.QuadraticLocal.Shelter.Picnic

/-! The actual regular–hard crossed face of the signed product, enrolled
as one original one-source forced array before choosing fields or tests. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCapturedHardFace
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Push.Corrected Push.Local Planned.GuardedAtom
open WilsonCenteredCaptureSlots
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}
    (D : Lamps X ι G P.p o R) (A : Gallery X μ o P R)
    (a b : V) (Z : Support n)

def query (z : ι × ℕ) := D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support
def owners (z : ι × ℕ) : Finset ℕ := {z.2}

theorem attachment (x : X) (z : ι × ℕ) :
    Attaches P.p.threshold (query D Z z)
      (fun U => WilsonCenteredCompulsoryCollection.joint D A a b x U z.1 z.2) := by
  let F := fun U => D.frame z.1 x U
  let H := A.K.hard x z.2
  have reg : Width.LocalCharge P.p o (query D Z z) F :=
    (Shelter.Deck.locality (L:=D) x z.1).widen ((Finset.subset_union_left).trans Finset.subset_union_left)
  have rare : Width.LocalCharge P.p o (query D Z z) H :=
    (A.K.locality x z.2).widen Finset.subset_union_right
  change Attaches _ _ (fun U => (F U).part (R.fire a)*(H U).part (R.fire b) +
      (H U).part (R.fire a)*(F U).part (R.fire b))
  refine ⟨fun U V hg hf => ?_,fun g U => ?_,?_,fun U good => ?_⟩
  · rw [reg.reads U V hg hf,rare.reads U V hg hf]
  · rw [reg.gauge g U,rare.gauge g U]
  · exact (((Poly.part_cont _).measurable.comp reg.borel).mul ((Poly.part_cont _).measurable.comp rare.borel)).add
        (((Poly.part_cont _).measurable.comp rare.borel).mul ((Poly.part_cont _).measurable.comp reg.borel))
  have h0 : H U = 0 := by
    by_contra nz
    have choose := (A.K.charged x z.2 U nz).1
    have dis : Disjoint (P.activities.forced z.2).support (flags P.p.threshold U) :=
      good.mono_left Finset.subset_union_right
    rw [Finset.disjoint_iff_inter_eq_empty.mp dis] at choose
    exact (P.activities.forced z.2).inventory_ne.ne_empty choose.symm
  rw [h0];change _ * 0 + 0 * _ = 0;ring

variable (K : Guard.Keeper P.p P.activities) (serial : (ι × ℕ) × Finset ℕ ↪ ℕ)

def row (x : X) : ℕ → Config G n → ℂ :=
  entered P K (query D Z) owners serial
    (fun z U => WilsonCenteredCompulsoryCollection.joint D A a b x U z.1 z.2)

theorem formed (x : X) (y : Site n) (atCenter : y ∈ Z) (law : P.activities.ForcedFamily P.p) :
    ForceFormat P.p P.activities y (row D A a b Z K serial x) :=
  WilsonCenteredCaptureSlots.formed P K (query D Z) owners serial _ y law
    (fun z => mem_union_left _ (mem_union_right (D.ground z.1) atCenter))
    (attachment D A a b Z x)

end YM.Integration.WilsonCenteredCapturedHardFace
