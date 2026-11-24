import YM.Gaps1020.Local.Manifest
import YM.MergeProof.Tanger
import YM.Integration.ActualRunSpring

/-! Every actual active radial marked band on the selected physical history
has a complete finite original regular-and-forced menu at its true price. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedBandMenu
open Function Finset Lattice Wilson RG Marker MergeProof Overlay
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Progress.DirectedRecipe Extra.Trajectories
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G)

def cost (seeds k : ℕ) (ordinary hard κ : ℝ) : ℝ :=
  let H := Overlay.GapsLocal.perStep seeds (R.family.path.levels.budget k).B
  2*(H*ordinary)+2*(H*(hard*κ))

section invoice
variable {n : Side} {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {Γ : Census V}
    {A : Rep G n} (x : Overlay.Bands Γ A) (w : V→ℝ)

structure Purchase (limit : ℝ) where
  rows : Type
  finite : Fintype rows
  hats : rows→MergeProof.Menu.Hat Γ A
  billed : letI : Fintype rows := finite; Overlay.GapsLocal.Shard x hats w limit

private theorem buy {u c d κ δ τ limit : ℝ} (live : x.Active) (paid : x.Radial w u c d κ)
    (labels : A.activities.Valid A.p δ τ) (stock : MergeProof.Menu.Arsenal A)
    (fee : 2*(Overlay.GapsLocal.perStep (Fintype.card V) A.p.B*c)+
      2*(Overlay.GapsLocal.perStep (Fintype.card V) A.p.B*(d*κ))≤limit) : Nonempty (Purchase x w limit) := by
  have sites : Extra.Multi.Occupancy x.origins (Fintype.card V) := fun _=>Finset.card_le_univ _
  obtain ⟨I,fi,q,h⟩ := Overlay.GapsLocal.bait (D:=x) live paid sites labels stock fee
  exact ⟨⟨I,fi,q,h⟩⟩

end invoice

variable {N p m : ℕ} (hm : m<N)
local notation "fine" => R.family.path.rep N p (m+1)

include hm in
theorem arsenal : MergeProof.Menu.Arsenal (fine) :=
  Mallow.Many.sharp (A:=R.alloy) (m:=m) (n:=p) (Q:=fun _=>(fine))
    (ActualRunSpring.selected R N p m hm).point (RunPhysicalMarks.actual_hasSlots R N p (m+1) hm)

theorem complete {upper period level : ℕ} (below : level<upper)
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {Γ : Census V}
    (x : Overlay.Bands Γ (R.family.path.rep upper period (level+1))) (w : V → ℝ)
    {u c d κ : ℝ} (live : x.Active) (paid : x.Radial w u c d κ) :
    Nonempty (Purchase x w (cost R (Fintype.card V) (level+1) c d κ)) := by
  let incoming := R.family.path.rep upper period (level+1)
  have checked := R.makes.wilson.represents upper period (level+1) below
  have profile : incoming.p=R.family.path.levels.budget (level+1) := checked.vac
  have fee : 2*(Overlay.GapsLocal.perStep (Fintype.card V) incoming.p.B*c)+
      2*(Overlay.GapsLocal.perStep (Fintype.card V) incoming.p.B*(d*κ)) ≤
      cost R (Fintype.card V) (level+1) c d κ := by
    rw [profile]
    exact le_rfl
  exact buy x w live paid checked.good.labels (arsenal R (p:=period) below) fee

end YM.Integration.OriginalMarkedBandMenu
end
