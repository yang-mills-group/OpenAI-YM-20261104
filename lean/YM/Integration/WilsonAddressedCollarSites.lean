import YM.RG05Readout.Pulse.Writer

/-! A joint change of scale and origin on the actual finite Wilson cell.
    Child residues and derivative letters are summed independently. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarSites
open Finset Lattice Wilson RG Source Extra.Histories RG05Readout RG05Readout.Address
open RG05Readout.Native RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {I : Type} [DecidableEq I] [Fintype I]

theorem ray (d : I → ℕ) (j : (i : I) → Letter (d i)) (φ : Wave I) (δ : ℝ) (y : Cloud I) :
    (perform d j (fork δ y φ)).val 0 =
      (δ : ℂ)^(pegs d j (Finset.univ (α:=I)).toList) * (perform d j φ).val y := by
  unfold perform
  rw [machine_roll]
  change _ * (machine d j _ φ).val (y + δ • 0) = _ * _
  rw [smul_zero,add_zero]

theorem original {m N p : ℕ} (mN : m ≤ N) (d : I → ℕ) (x : (i : I) → Palette C (d i))
    (o : I → Site (C.side m p)) (φ : Wave I) (δ : ℝ) (y : Cloud I)
    (U : Config G (C.side N p)) :
    let cell := C.S.toDepth mN p
    scalp (C:=C) d x o mN (fork δ y φ) U =
      ∑ t : I → Site cell.count, (∏ i, ratioX cell (d i)) *
        ∑ j : (i : I) → Mark C (d i),
          (((δ * (cell.count.val : ℝ)⁻¹ : ℝ) : ℂ)^
              (pegs d (fun i => (j i).1) (Finset.univ (α:=I)).toList) *
            (perform d (fun i => (j i).1) φ).val (y + δ • fun i => placeR cell (t i))) *
          ∏ i, key C N p (d i) (x i) (j i) (cell.assemble (o i,t i)) U := by
  unfold scalp
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [fly_fork]
  apply congrArg ((_ : ℂ) * ·)
  apply Finset.sum_congr rfl
  intro j _
  rw [ray]

theorem regularity (d : I → ℕ) (j : (i : I) → Mark C (d i)) :
    pegs d (fun i => (j i).1) (Finset.univ (α:=I)).toList ≤ ∑ i, d i :=
  pegs_cost d (fun i => (j i).1)

end YM.Integration.WilsonAddressedCollarSites
