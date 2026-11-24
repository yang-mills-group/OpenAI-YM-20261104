import YM.Integration.WilsonRegisteredSealedArray
import YM.Integration.WilsonThermalReplicaChessboard
import YM.Integration.ReplicatedSignedCellBound

/-! The signed lower withdrawals use the original coordinate pullback and
complex conjugation in each physical reflection cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSealedReflections
open Lattice Wilson RG Cells Push.GridApprox OPE.Therm PhysicalNext.Repeat.Legato
open Set MeasureTheory QLocalPhysicalPathKernel WilsonPositionOriginalDressedQFailedPath
open scoped Classical Topology
variable {G:Gauge}

theorem original (R:Run G){N per i station:ℕ}(live:i < N)(ji:station ≤ i)(r q:ℕ)
    (roomL:room R.family.path.levels station i r)
    (Q:Site (R.family.side station per) → Config G (R.family.side (i+1) per) → ℂ)
    (L:Site (R.family.side station per) → Config G (R.family.side i per) → ℂ)
    (hq:∀j,Interior (window 0 q) (Q j))(hl:∀j,Interior (window 0 r) (L j)):
    let A:=R.family.path; let S:=tilesAt R.family.S per ji
    let T:=tilesAt R.family.S per (ji.trans (Nat.le_succ i)); let step:=backTo A N per (Nat.le_succ i)
    (∫ω:ConfigurationPath R per,(∏j:S.Cell,(T.copy j (Q j) (ω (i+1))-S.copy j (L j) (ω i)))
       ∂path R.family R.makes N per)=
      ∫U,T.fullAt (fun j V=>Q j V-step (L j) V) U ∂scene A N per (i+1):=by
  intro A S T step
  have eqv j:Envelope (T.copy j (Q j)):=cylinder_env
    (copy_window A per (ji.trans (Nat.le_succ i)) j q (Q j) (hq j))
  have el j:Interior (S.chamber j) (S.copy j (L j)):=by
    apply (copy_window A per ji j r (L j) (hl j)).enlarges
    simpa using room_fits per A.levels r ji (le_refl i) roomL j
  have dis:Pairwise fun j k=>Disjoint (S.chamber j) (S.chamber k):=by
    intro j k neq
    exact Set.disjoint_left.mpr (fun x hx hy=>neq ((S.which_chamber hx).symm.trans (S.which_chamber hy)))
  have paid:=WilsonRegisteredSealedArray.original R live Finset.univ (fun j=>T.copy j (Q j)) eqv
    (fun j=>S.copy j (L j)) S.chamber el dis
  apply paid.trans
  congr 1
  funext U
  apply Finset.prod_congr rfl
  intro j hj
  rw [backTo_copy A N per ji (Nat.le_succ i) j (cylinder_env (hl j))]
  unfold Tiling.copy
  split_ifs <;> simp <;> rfl
end YM.Integration.WilsonRegisteredSealedReflections
