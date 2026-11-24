import YM.GradedFar.Physical.Actual

/-!
# A calibrated homogeneous transition receipt on these same books

Application uses BOOK'S concrete seated fields below. Here no special orientation
assumptions borrowed. Assert the precise budgets needed from the PoseFit claims.
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
    (S : (d:ℕ) → ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ : ℝ→ℝ)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "F"=> familyPoint U J
local notation "F'"=> familyPoint U K

/-- Earlier, still-physical PoseFit receipts on any finite stock used here. At the exact
finitely specified calls (not estimates on a convenient hierarchy witness).
It is enough to apply C5 in unselected compact settings (this limited
request or that one). The outputs of PoseFit are used here, not claimed
bought by kernel physical chapter. Device at this COMMON cap 6. Budgets on
`Mixed` include two legs when step comparisons use couplings at BOTH poses.
No M.2 etc hypotheses here, and not already assuming on this clock the
PFrame/G.1 or continuation comparisons. -/
structure Ample : Prop where
    preorder : Latest N (familyPoint U J)
    mixed : ∀ (d : ℕ) (u v : Dframe.Toon G d), Offered N (familyPoint U J d) (next J d) u v

/-- separate these from the stated physical hypotheses, prove for our orientation
in the application. -/
structure Bookshelf : Prop where
    fixed (d:ℕ) : Moving.Held N (Y d) (familyPoint U J d)
    stage (d:ℕ) : ∀ᶠ r in τ,∀ z∈Growth.Small, permissible (Moving.forwards (next J d) r z)
    layers (d:ℕ) : Layer N θ (S d) (next J d) (next K d)
    known : θ= Pose.kinetic N (familyPoint U J 6)

structure Earned : Prop where
    pre_meter : ∀ d, Beginning N θ d (familyPoint U J d)
    clock : Tendsto (fun r=> θ r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1)
    short (p d:ℕ) : 1≤p → PTheta N M θ p ∧ PFrame N M (Zenith (next K d)) θ p
    main (q d :ℕ) {C B :ℝ}(c0:0<C)(b0:0<B) :
        (∀ᶠ p : ℕ in atTop, ∀ᶠ r in τ,∀ s≥0, exp s ≤ C*g r^(-B) →
          theta_err N M θ p r s+frame_err N M (Zenith (next K d)) θ p r s ≤ g r^q) ∧
        ∀ᶠ r in τ, ∀ s≥0, exp s ≤ C*g r^(-B) →
          ‖Zenith (next K d) r s‖ ≤ 2*exp s^d ∧ ‖Zenith (next K d) (r*exp s) (-s)‖ ≤ 2

include H
-- layering depends on θ thus have leading from Ample for constructing Bookshelf (without already h positive θ)
lemma crown (hθ : θ= Pose.kinetic N (F 6)) (Q : Ample N U J) (he : ∀ d, Held N (Y d) (F d)) :
    Tendsto (fun r=> θ r/g r) τ (𝓝 1) ∧ ∀ d, Beginning N θ d (F d) := by rw [hθ]; exact
    ⟨heated N M H F Y he Q.preorder, fun d=> Books.begin N M H F Y he Q.preorder⟩

theorem booked (Q : Ample N U J) (R : Bookshelf N U J K S Y θ) : Earned N M U J K θ := by
  obtain ⟨hx,hy⟩:= crown N M H U J Y θ R.known Q R.fixed
  have hc d:= aligned N M H (Q.mixed d) θ (hy d) (R.stage d)
  refine ⟨hy,hx,fun p d hp=>?_ ,fun n d _ _ a b=>?_⟩
  · exact Moving.earned N M H (next J) (next K) S F Y θ R.known hx hc hy R.fixed (refits U J) R.layers p d hp
  exact G1 N M H (next J) (next K) S F Y θ R.known hx hc hy R.fixed (refits U J) R.layers a b (hasMotion K d) n
end
end YM.FVA2.GradedFar.Physical
