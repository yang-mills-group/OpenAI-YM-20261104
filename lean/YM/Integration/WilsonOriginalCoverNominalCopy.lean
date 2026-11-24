import YM.Integration.FVA1Physical.TwoReset.MarkCover
import YM.Integration.WilsonOriginalCoverNominalWords

/-! The one-page-normalized connected pair on each actual auxiliary period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalCopy
open FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (R : Run G)
variable {V ι μ ν α : Type} [DecidableEq V] [Fintype V] {m n N : ℕ}
local notation "S" => R.family.path.levels.clock.op
local notation "K" => RunFormalChain.fromRun R
local notation "c" => R.family.side m n
local notation "f" => R.family.side (m+1) n
variable {J : Passport (R.family.side (m+1) n) V} {W : Census V}
variable (h : m < N)
variable (D : Layout G) (T : Finset Age) (p : ℕ) (M : ι → Row J W G α) (w : V → ℕ)
local notation "CC" => Covers R.family.path.levels.S m
local notation "CC'" => coverFilter R.family.path.levels.S m

def ordinary (t:α) (X:Side) (hX:(R.family.side m n).val ∣ X.val)
    (Y:∀ b:CC X, Forest (S m b.val).ratio) (u:∀ b:CC X,(S m b.val).Choices)
    (x:Stationary.Link G X) (s:W.Mode) (b:CC X) : Polynomial ℂ :=
  let material := copyColor (tiled R hX b) M w (fun i:ι => (M i).paint t) D T
  let A := Stationary.arm G (R.family.side m b.val) 1 (convey (coverWin b.prop) x)
  WilsonOriginalCoverNominalWords.ordinary ((K).step N m b h) (Y b) (u b) (Stock.census Unit)
    material A p s

def deposit (t:α) (X:Side) (hX:(R.family.side m n).val ∣ X.val)
    (Y:∀ b:CC X, Forest (S m b.val).ratio) (u:∀ b:CC X,(S m b.val).Choices)
    (x:Stationary.Link G X) (a d:V) (s:W.Mode) (j:ℕ) (b:CC X) : ℂ :=
  let word := fun q:W.Mode => ordinary R h D T p M w t X hX Y u x q b
  (((Pages X (R.family.side m b.val):ℕ):ℝ)⁻¹ : ℝ) •
    (word s - word (W.fire a) * word (W.fire d)).coeff j

theorem purchased (t:α) (X:Side) (hX:(R.family.side m n).val ∣ X.val)
    (Y:∀ b:CC X, Forest (S m b.val).ratio) (u:∀ b:CC X,(S m b.val).Choices)
    (x:Stationary.Link G X) (a d:V) (s:W.Mode) (apart : a≠d) (both : s.val={a,d})
    (c₀ : ℝ) (B : BudgetPoint) {a₀ : ℝ} {k : ℕ} (staff : Air.Staff M (fun i:ι => (M i).paint t) w a₀ k)
    (valid : Legal T D) (j : ℕ) (hj : j≤p) (b : CC X) :
    (FVA1Physical.TwoReset.FkCover R h D T p M w t X hX Y u x j b).part s =
      deposit R h D T p M w t X hX Y u x a d s j b := by
  have reg := copy_standard (tiled R hX b) M w (fun i:ι => (M i).paint t) D T staff valid
  have pair := WilsonOriginalCoverNominalWords.original ((K).step N m b h) (Y b) (u b) (Stock.census Unit)
    (copyColor (tiled R hX b) M w (fun i:ι => (M i).paint t) D T)
    (Stationary.arm G (R.family.side m b.val) 1 (convey (coverWin b.prop) x))
    p reg.1 c₀ B a d s apart both j hj
  exact congrArg (fun v : ℂ => (((Pages X (R.family.side m b.val):ℕ):ℝ)⁻¹ : ℝ) • v) pair

end YM.Integration.WilsonOriginalCoverNominalCopy
