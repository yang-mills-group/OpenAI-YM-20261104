import YM.Integration.MSFixedRatioGaussianForecast
import YM.FormalBulk08.Reef.Mount
import YM.FVAAlt2.Periodic.Primary

/-! Canonical forest, all color entries and the complete restricted
Maxwell form in the two original Gaussian descriptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioGaussianGeometry
open Lattice Laurent Exterior RG Next.Free Stationary Tree FormalBulk08 FormalBulk08.Flat
open Matrix Function RegulatorIR RegulatorIR.Oracle RegulatorIR.Geometry RegulatorIR.Halo
open RegulatorIR.Ledger FreeResolvent MSFixedRatioGeometry MSFixedRatioCalibration
open scoped Classical Matrix BigOperators

variable {G : Gauge} {c f : Side} (S : StepData c f)

private theorem forest_ext {g : Ratio c f} {A B : Forest g} (hu : A.up=B.up) (hh : A.height=B.height) : A=B := by
  cases A
  cases B
  cases hu
  cases hh
  rfl

theorem forest : (Flat.routes S.patch).forest (S:=S)=Halo.bios S := by
  apply forest_ext (A:=(Flat.routes S.patch).forest (S:=S)) (B:=Halo.bios S) _ rfl
  funext x
  change Flat.slideTo S.patch (S.ratio.residue x)=
    if h:Tree.leaf S.ratio x then Bark.toward S.ratio x h else posDir 0
  by_cases h : Tree.leaf S.ratio x
  · rw [dif_pos h]
    unfold Flat.slideTo
    split
    · rfl
    · rename_i hn
      exact (hn ((Flat.Lodge.is_leaf S x).mp h)).elim
  · rw [dif_neg h]
    unfold Flat.slideTo
    split
    · rename_i hy
      exact (h ((Flat.Lodge.is_leaf S x).mpr hy)).elim
    · rfl

/-- Both descriptions retain exactly the same link, Lorentz direction
and color away from the fixed forest. -/
def address (F : Forest S.ratio) : Active G F ≃ Flat.Alive G S F := Reef.pines F

theorem color {j k : ℕ} (A : Matrix (Body j c) (Body k f) ℝ) :
    Stationary.patron G A=FreeResolvent.tensor G A := by
  apply Flat.mat_confirm
  intro x
  rw [Stationary.patron_fee]
  funext v
  obtain ⟨z,i,h⟩:=v
  exact (congrFun (FreeResolvent.component_mul A x h) (z,i)).symm

private theorem color_add {j k : ℕ} (A B : Matrix (Body j c) (Body k f) ℝ) (a : ℝ) :
    FreeResolvent.tensor G (A+a • B)=FreeResolvent.tensor G A+a • FreeResolvent.tensor G B := by
  ext i k
  by_cases h : i.2.2=k.2.2 <;> simp [FreeResolvent.tensor,h]

private theorem embedded (F : Forest S.ratio) :
    (Flat.dropRoot G S F)ᵀ=FreeResolvent.insertion (fun x : Flat.Alive G S F=>x.val) := by
  ext x y
  simp [Flat.dropRoot,FreeResolvent.insertion,Matrix.one_apply,eq_comm]

/-- The full signed form on free links agrees in every matrix entry,
including the block prediction penalty. -/
theorem restricted {j : ℕ} (F : Forest S.ratio) (V : Next.Free.Train j) (H : FreeResolvent.FaceRow)
    (hH : Precision.K (H.acts f)=Precision.K ((Next.Free.pink S.kernel.penalty V).acts f)) :
    (Flat.testPrecision G S F V).submatrix (address S F) (address S F)=treeMatrix G S F H := by
  have hfull : fullMatrix G S H=Stationary.patron G (Precision.K ((Next.Free.pink S.kernel.penalty V).acts f))+
      S.kernel.penalty • ((Stationary.patron G (Precision.probe S))ᵀ*Stationary.patron G (Precision.probe S)) := by
    unfold fullMatrix baseMatrix
    rw [hH,color_add,←Stationary.patron_star,←Stationary.patron_mul,color,color]
  have hmat : Flat.testPrecision G S F V=(fullMatrix G S H).submatrix (fun x : Flat.Alive G S F=>x.val)
      (fun x : Flat.Alive G S F=>x.val) := by
    rw [←FreeResolvent.insertion.compress,←embedded S F,hfull]
    simp only [Flat.testPrecision,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_add,
      Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc]
  rw [hmat]
  ext i k
  rfl

theorem original {K : KernelChoices} (p : Patch) (Y : Program K) (w : Page history) (c : Side) :
    let S:=Oracle.avenue p K c
    let F:=Halo.bios S
    (Flat.testPrecision G S F (Copula.Diagram p w.downW)).submatrix (address S F) (address S F)=
      treeMatrix G S F ((lattice p).tables Y w).metric :=
by
  dsimp only
  let A:=Oracle.avenue p K c
  let F:=Halo.bios A
  exact restricted (G:=G) A F (Copula.Diagram p w.downW) (((lattice p).tables Y w).metric)
    (MSFixedRatioGaussianForecast.precision p Y w (c*p.L))

end YM.Integration.MSFixedRatioGaussianGeometry
