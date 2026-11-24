import YM.Integration.WilsonLongContactFrozenLetter

/-! The complete physical singleton satisfies the frozen-input obligations of the Gaussian comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Gaussian Tablet Quill Baffle Polar Prism Brim
open WardBin.Lies Push.PriceCompiler Foramen Gate Lotus Township Finset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {U : Config G c} {j n : ℕ} {L : Side}
variable {d A t C' w M N Q v δ K b' ζ β W k ε y₀ J' L₀ X' : ℝ}
open YM.Integration.WilsonLongContactTown

variable {R : RG.Rep G f}


open Blaze ConnectedActivityE6.Blaze
open YM.Integration.WilsonLongContactFrozenTest

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Coat T F) (i : ℕ) (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I)

def forecast (q κ : Chi) (b : ℝ) (D : Record) (V : Config G c) (H : Config G f→ℝ) :=
  a.hymn T (gStep R.beta) q b X.k H (Baffle.magic D R.p R.beta κ) 1 V

def fixed (u : Prices G I) : Config G f := strip6 X a X.V (anchor X a u R.beta)

/-- The physical comparison originally issued by Sill, with its full test and actual covariance. -/
def BorelRows (H:E→ Config G f→ℝ)(p:E)(n:ℕ):= ∃ l:ℕ, ∃ (T:Fin l→E→ℝ)(V:Fin l→ Config G f→ℝ), (∀ x u, H x u=∑ i, T i x*V i u) ∧ ∀ i, ContDiffAt ℝ (n:WithTop ℕ∞) (T i) p ∧ Measurable (V i) ∧ ∃ b,∀ y,‖V i y‖≤b

def allowance (ζ v : ℝ) (D : Record) (κ : Chi) (V : E→ Config G c) (n : ℕ) : Prop :=
  (∀ᶠ s in 𝓝 (0:E), (vary X (V s)).relating.PosDef) ∧
  ∀ (M : E→ Config G f→ℝ) (A : ℝ), 0≤A →
    (∀ y, LocalOn (inspected (R.activities.reg i).support) (M y)) → BorelRows M 0 n →
    (∀ u : Prices G I, (∀ k, ‖anchor X a u R.beta k‖≤6*ζ*X.t) →
      Brush n A 1 (fun y=>M y (fixed X i a u)) 0) →
    ∀ q b, Brush n (A*v) 1 (fun y=>deal X i R a ∅ ζ (V y) (M y) -
      forecast X i a q κ b D (V y) (M y)) 0

theorem corrected (hp : Scrim X a) (room : Room P S T X.x)
    (M : Leaf R) (source : M.turn=.logKey i) (ζ v W : ℝ) (D : Record) (κ : Chi)
    (V : E→ Config G c) (n l : ℕ) (Γ : ChartRatio G) (q : Chi) (b : ℝ)
    (original : allowance X i a ζ v D κ V n) :
    Brush n (M.weight*v) 1 (fun y=>(town T M).cinema (vary X (V y)) (solitary S M) W ζ Γ l
      (podium S G Y X.B) - forecast X i a q κ b D (V y) M.ingredient) 0 := by
  have shaped : M.crest=(R.activities.reg i).support := by
    change M.turn.support R=(R.activities.reg i).support
    rw [source]; rfl
  have paid := original.2 (fun _=>M.ingredient) M.weight
    ((norm_nonneg _).trans (M.earn 1)) (fun _=>shaped ▸ M.specific) (rows M n (0:E))
    (fun u _=>current M n (0:E) (fixed X i a u)) q b
  apply paid.shimmy
  filter_upwards [original.1] with y hy
  rw [measured X i M source a hp room W ζ (V y) Γ l (hy.submatrix Subtype.val_injective)]
  unfold deal
  simp only [purse6, Finset.prod_empty, mul_one]

end YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
