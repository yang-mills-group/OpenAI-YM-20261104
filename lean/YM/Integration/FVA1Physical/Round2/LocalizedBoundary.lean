import YM.Integration.FVA1Physical.Wilson.BoundaryJetBlocks
import YM.Integration.FVA1Physical.Round2.PacketPrice

/-! Separate local boundary insertions in the actual conditional Haar law.
Only the bonds carrying a kick enter the joint product; the remaining
configuration is free to be an arbitrary inherited exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16 Pressure
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato Integration.FVA1Physical.Wilson
open scoped Classical Topology ContDiff

variable {G : Gauge} {c : Side}

def physicalBond (i : Primary c G) : Bond c := (i.1.1, axisEquiv.symm i.1.2)

theorem physicalBond_primary (e : Bond c) (a : G.ColorIndex) :
    physicalBond (primary e a) = e := by
  change (e.1,axisEquiv.symm (axisEquiv e.2))=e
  rw [axisEquiv.symm_apply_apply]

def bondLocked (B : Finset (Bond c)) (base x : Positions (Primary c G)) : Prop :=
  ∀ i, physicalBond i ∉ B → x i = base i

theorem bondLocked.move {B : Finset (Bond c)} {base x : Positions (Primary c G)}
    (locked : bondLocked B base x) (i : Primary c G) (inside : physicalBond i∈B) (v : ℝ) :
    bondLocked B base (x+v • bolt i) := by
  intro j outside
  have ne : j≠i := fun eq=>outside (eq ▸ inside)
  simp [bolt,ne,locked j outside]

theorem bondLocked.vary {B : Finset (Bond c)} {base x : Positions (Primary c G)}
    (locked : bondLocked B base x) (g : ℝ) :
    varyBonds B (palace (g • base)) (palace (g • x)) = palace (g • x) := by
  funext e
  by_cases he : e∈B
  · simp [varyBonds,he]
  · rw [varyBonds,if_neg he]
    have equal : panel G c base e = panel G c x e := by
      ext a
      change base (primary e a)=x (primary e a)
      exact (locked _ (by simpa only [physicalBond_primary] using he)).symm
    unfold palace
    rw [map_smul,map_smul]
    change G.lieExp (g • panel G c base e) * 1 = G.lieExp (g • panel G c x e) * 1
    rw [equal]

variable {C : Family G} (L : Bulk.Chain C.path) {N n j r : ℕ}
    (S : Scene C.path.levels n r) (T : Slices C.path.levels n) (hj : j < N)
    (room : (traversal T hj.le).Room G) (tag : (traversal T hj.le).Tags)
local notation "X" => Positions (Primary (C.side j n) G)

theorem block_error_locked (sel : C.path.Selected) {ι : Type} [DecidableEq ι]
    (A : Finset ι) (K : ι→Finset (Bond (C.side j n)))
    (he : ∀ i∈A,∀ j∈A,i≠j→Disjoint (K i) (K j))
    (p : ℕ) (g : ℝ) (base x : X) (quiet : bondLocked (A.biUnion K) base x) :
    blockError L S T hj room tag A K p g base x =
      sceneVacuumError L S T hj.le room tag p g x - sceneVacuumError L S T hj.le room tag p g base := by
  have cut : blockRead (traversal T hj.le) (line C.path n j N) A K (palace (g • base)) (palace (g • x)) =
      boundaryRead (traversal T hj.le) (line C.path n j N) (palace (g • base)) (palace (g • x)) := by
    rw [traversal_push T hj,block_read_eq (T j) (traversal T hj) _ A K he,quiet.vary]
  change _ = (fun y=>sceneVacuumError L S T hj.le room tag p g y - sceneVacuumError L S T hj.le room tag p g base) x
  rw [←centered_boundary_error L S T hj.le room tag sel p g base]
  unfold blockError connectedBoundaryError
  rw [cut]

private theorem rectangle_locked_congr {B : Finset (Bond c)} (v : Primary c G→ℝ)
    (moves : List (Primary c G)) (active : ∀ i∈moves,physicalBond i∈B)
    {F H : Positions (Primary c G)→ℝ} {base : Positions (Primary c G)}
    (eqn : ∀ x,bondLocked B base x→F x=H x) (x : Positions (Primary c G)) (locked : bondLocked B base x) :
    rectangle v moves F x = rectangle v moves H x := by
  induction moves generalizing x with
  | nil => exact eqn x locked
  | cons i tail ih =>
    have rest : ∀ a∈tail,physicalBond a∈B := fun a ha=>active a (List.mem_cons_of_mem _ ha)
    rw [rectangle,rectangle,ih rest _ (locked.move i (active i (by simp)) _),ih rest _ locked]

private theorem rectangle_sub_constant {σ : Type} [Fintype σ] (v : σ→ℝ) (F : Positions σ→ℝ)
    (moves : List σ) (C : ℝ) (x : Positions σ) :
    rectangle v moves (fun y=>F y-C) x = rectangle v moves F x - (if moves=[] then C else 0) := by
  induction moves generalizing x with
  | nil => rfl
  | cons i tail ih => simp only [rectangle,ih,List.cons_ne_nil,if_false,sub_zero]; abel

/-- Every nonempty mixed change of the logarithm of a product of disjoint
physical boundary factors minus the independent normalized Wilson prediction is
the very same mixed change of the non-bare scene error. No covering by the
marked bonds is required, and the denominator is the actual common vacuum. -/
theorem block_rectangle_local (sel : C.path.Selected) {ι : Type} [DecidableEq ι]
    (A : Finset ι) (K : ι→Finset (Bond (C.side j n))) (he : ∀ i∈A,∀ j∈A,i≠j→Disjoint (K i) (K j))
    (p : ℕ) (g : ℝ) (base x : X) (quiet : bondLocked (A.biUnion K) base x)
    (v : Primary (C.side j n) G → ℝ) (moves : List (Primary (C.side j n) G)) (nonempty : moves≠[])
    (active : ∀ i∈moves,physicalBond i∈A.biUnion K) :
    rectangle v moves (blockError L S T hj room tag A K p g base) x =
      rectangle v moves (sceneVacuumError L S T hj.le room tag p g) x := by
  rw [rectangle_locked_congr v moves active (fun y hy=>block_error_locked L S T hj room tag sel A K he p g base y hy) x quiet,
    rectangle_sub_constant,if_neg nonempty,sub_zero]

end YM.Integration.FVA1Physical.Round2
