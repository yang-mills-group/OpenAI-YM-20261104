import YM.Integration.FVA1Physical.Wilson.SchurPurchase
import YM.MSbar.Spruce.GlobalP

/-! Rooted decay of the exterior dependence of the actual Schur Gaussian.
The retained covariance is compared in complete absolute rows and columns. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Matrix Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Whisk MSbar.Bulk MSbar.Mosaic MSbar.Bakery.Film MSbar.Kelvin
open Push.Uniform Next.SectorChange RGComparison.Core16
open scoped Classical Topology
variable {G : Gauge}

def schurShift (A : Mosaic.Issue G) (J : Voice G) (y : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (U : Config G A.f) :=
  let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
  let v:=linCash A.F z
  him J A.F (boxY y b) (represent (tint G (Exterior.Body 1 A.c) z)) ν
    (mold A.pre A.F A.v) (boxX y b) v U - chair A.F ν v

def schurCovGap (A : Mosaic.Issue G) (y : ℝ) (b : Site A.f) :=
  let M:=mold A.pre A.F A.v
  let i:=includeX (G:=G) A.F (boxX y b)
  M⁻¹ - extendM i (pinch i M)⁻¹

theorem schur_core_rows (A : Mosaic.Issue G) (J : Voice G) (χ : ChartRatio G) (clear : Clear G J)
    (y : ℝ) (z : Positions (Primary A.c G)) (b : Site A.f) {a d k h C W rate : ℝ} {p : ℕ}
    (suite : Suite J χ A.F (boxX y b) (boxY y b) (represent (tint G (Exterior.Body 1 A.c) z))
      A.v A.pre (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y) a d k h (linCash A.F z))
    (solve : Solver (includeX (G:=G) A.F (boxX y b)) (address A.F G ∘ Sum.inr) 0 rate C W p (mold A.pre A.F A.v))
    (hrate : 0≤rate) (i : Key A.F G) :
    let M:=schurCovGap A y b
    let l:=address A.F G ∘ Sum.inr
    let β:=Real.exp (-rate*(spotN y))*Eve rate b (l i)
    (∀ U∈hotel A.F (boxX y b) (boxY y b) J (represent (tint G (Exterior.Body 1 A.c) z))
       (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
       |schurShift A J y z b U i|≤β*(W*(k+pillow y))) ∧
    (∑ j,|M i j| * liftW 0 p (separation (l i) (l j)))≤β*(W*C) ∧
    (∑ j,|M j i| * liftW 0 p (separation (l j) (l i)))≤β*(W*C) := by
  intro M l β
  let F:=A.F
  let X:=boxX y b
  let Y:=boxY y b
  let O:=represent (tint G (Exterior.Body 1 A.c) z)
  let ν:=vest (priced F A.v A.pre.clip A.pre.path) z
  let v:=linCash F z
  let idx:=includeX (G:=G) F X
  have outside := fun (j : Key F G) (hj : j ∉ Set.range idx) => Mosaic.housing F b y j hj
  have cost := realFuel idx (secureY F X G) solve.bids outside (le_refl 0) hrate solve.travels
    (solve.growth.low (show (0:ℝ)≤0+rate by linarith))
  constructor
  · intro U live
    have room := frozen J F X Y O U ν χ clear v suite.seat (halo_subset _ _) live
    let e:=outY J F Y O ν X v U
    have bill := Spruce.defense e idx b p (spotN y) p solve (le_refl 0) hrate room (secureY F X G) outside i
    have shift : schurShift A J y z b U i=((vanish idx (mold A.pre F A.v))*ᵥ e) i := by
      simp only [schurShift,him,add_sub_cancel_left]
      rfl
    rw [shift]; exact bill.trans_eq (by dsimp only [β,l,F,Function.comp_apply]; ring)
  refine ⟨(cost.upper i).trans_eq ?_,(cost.lower i).trans_eq ?_⟩ <;> dsimp only [β,l,F,Function.comp_apply] <;> ring
end YM.Integration.FVA1Physical.Wilson
