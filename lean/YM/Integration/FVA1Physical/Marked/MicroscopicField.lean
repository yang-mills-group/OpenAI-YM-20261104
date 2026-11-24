import YM.Integration.FVA1Physical.Marked.StencilAlbum

/-! Evaluate the exact C18 prescribed microscopic source in one fixed list
of legal native Quipu operands, for all coefficient choices, signed motions,
positions and periods. The engineering and coupling factors are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Source Next.Foundations Marker Qlocal Qlocal.Quipu Qlocal.Quipu.Sonnet
open Extra.Trajectories Extra.Histories LocalLTE.Sail MergeProof
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {K I : Type} [DecidableEq K] {B : Census K} {G : Gauge}
def nativeBasis (s : Senses B) (d : ℕ) (i : ((Labels.frames G).level d).Index) : List (FieldOperand s G) :=
  (basis_album s d i).choose

theorem microscopic_source_album (s : Senses B) (X : Run G) {N n : ℕ} (Y : Batch X.family.path N n I)
    (j : I) (q : ℕ) (v : Config G (X.family.side N n)) :
    let d := Y.demand j
    let a := (X.family.S.a N:ℂ)^d
    let w := ((Labels.frames G).level d).scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j)
    let u := pull (Y.motion j).1 (Y.origin N j) v
    Y.wavelengths j v = a * Motion.scalar (Y.motion j) (a⁻¹ *
      ∑ i : ((Labels.frames G).level d).Index,
        w i * ((nativeBasis s d i).map (fun e=>e.factor*((e.code.read 0 q u:ℝ):ℂ))).sum) := by
  intro d a w u
  rw [physical_wavelength X Y j v]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact ((square_basis_spec d i).2.2 _ 0 u).symm.trans ((basis_album s d i).choose_spec _ 0 q u)

end YM.Integration.FVA1Physical.Marked
