import YM.Integration.FVA1Physical.TwoReset.MarkCover
import YM.QuadraticLocal.Rebirth.Press

/-!
# Across the first physical reclosure to the second

Passport repayment also binds the predictor after *actual* reset.
Adjacently reparameterize the very cover Fk packet including the
inverse-g powers in the unit convention of the marks. This file is formal —
retain also the discrepancy incurred in evaluated coordinates, in the
actual-witness Tattoo.Sycamore estimate, not in a test of the parametric series.
-/

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Rebirth
open Comparison.RG02 Comparison.RG02.Adjacent
open Comparison.RG02.Moving Path Shift
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G:Gauge} {V ι μ α:Type} [DecidableEq V] [Fintype V]
variable {n C:Side} {P:Passport n V} {W:Census V}
variable (M:ι→Row P W G α) (t:α) (w:V→ℕ)
variable (D: Layout G) (T: Finset Age) (q:Pace.Coin) (h : q 0=0) (l p : ℕ)
variable (u : n.val∣C.val)
local notation "Q" => (Rebirth.caliber q h).back l
local notation "M'" => Mutation.stamp M q h l p
local notation "f" => peek u M w D T t
local notation "g" => peek u M' w D T t
variable (S: Finset ℤ) (hS:∀ i,(M i).lamp.lag∈ S)
variable {a b:ℝ} {σ k:ℕ}
variable (hn:Air.Staff M (fun i=> (M i).paint t) w a σ)
variable (hb:Air.Staff (Mutation.stamp M q h l p) (fun i=> (Mutation.stamp M q h l p i).paint t) w b k)
variable (j:W.Mode)
local notation "pageM" s:max => (fun i:ι=> TwoReset.copy u (M i) s)
local notation "I"=> Fin (Pages n C)
local notation "E" s:max => Sleeve.currency t w (pageM s) j T D
local notation "E'" s:max => Sleeve.currency t w (Mutation.stamp (pageM s) q h l p) j T D
local notation "F"=> (fun i x=> (f i x).part j)
local notation "F'"=> (fun i x=> (g i x).part j)
include hS hn
private lemma discipline (s:I) (x: Stationary.Link G C) : ContDiffAt ℝ ω
    (fun y:ℝ=> Adjacent.ages (E s) 0 p y ((Q).rating y) x) 0 := by
  let L := (pageM s)
  let K := ( Q )
  have h₁:= Sleeve.chronicle t w L j S hS q h l p (copy_staff u M w _ hn s) T D x
  refine ContDiffAt.congr_of_eventuallyEq ?_ h₁
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro j _
  exact (Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (K.spin j)).mul contDiffAt_const)

include hb
lemma active_bend (i:ℕ) (hi:i≤p) (x:Stationary.Link G C) :
    F' i x=Adjacent.born F Q 0 p i x := by
  let φ(s:I) := E s
  let Φ(s:I) (y:ℝ):= Adjacent.ages (φ s) 0 p y ((Q).rating y) x
  have he (i) (x:Stationary.Link G C): F i x = ∑ s:I, φ s i x := by
    change (peek u M w D T t i x).part j = _
    rw [peek_pages u M w D T t x i hn, Poly.part_sum]; rfl
  have hh : (fun y:ℝ=> Adjacent.ages F 0 p y ((Q).rating y) x) = fun y:ℝ=> ∑ s:I, Φ s y := by
    funext y; unfold Φ Adjacent.ages Adjacent.cover
    simp_rw [he, Finset.mul_sum]; rw [Finset.sum_comm]
  have hk : Adjacent.born F Q 0 p i x= ∑ s:I, Adjacent.born (E s) Q 0 p i x:= by
    unfold Adjacent.born; rw [hh,msum univ Φ (fun s _=> discipline M t w D T q h l p u S hS hn j s x)]
  rw [hk]
  change (peek u (M') w D T t i x).part j = _
  rw [peek_pages u (Mutation.stamp M q h l p) w D T t x i hb,Poly.part_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (Sleeve.reexpressed t w (pageM v) j S hS q h l p (copy_staff u M w _ hn v)
    T D x (copy_staff u (M') w _ hb v) i hi).symm

end YM.Integration.FVA1Physical.TwoReset
