import YM.GradedFar.Pose.Calibrate
import YM.GradedFar.FormalSecond

/-!
# Cheap public M2 entry (no `import` of the expensive actual Run/Frame source)
 Computes even the PoseFit arithmetic needed from C5 to (M.2) given the
 measurements etc. (see `Elected/Remainder.lean` for the application to the
 *actual* `WPTR.reading` fields, under exactly those inputs).
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m d k j q : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G
variable (F : Plans G 6) (proxy : ℝ → ℝ) (near : Tendsto (fun r=> proxy r / gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Y : ℝ → Prediction G 6) (u : ℝ → Normalize.Change G 6)
variable (compP : ∀ n x, ∀ᶠ r in τ, ContinuousOn (fun p=> F r n p x) (conf n))
  (full : ∀ n (x:Tags G 6 n) (y:Test n), ∀ᶠ r in τ, Y r n y x=y.applyTo (fun p=> F r n p x))
  (fixed : ∀ᶠ r in τ,(N.store.measure 6).D (Y r)=(N.store.measure 6).D (reference G 6))
  (hc : Tendsto (fun i=> guide G 6 (u i)) τ (𝓝 0))
  (hQ : 1 ≤ q) (hq : k ≤ q+1)
  (acts : RawCalibration N F proxy k q u) (hk : 2 ≤ k)
include H near compP full fixed hc hQ hq acts hk
local notation "θ"=> kinetic N F
/-- M.2-second wrt **any** calibration with the specified hypotheses. Works
at general F (in particular the actual one). The physical application in
`Elected` supplies these hypotheses on the book when using Pose.F3 & costs
there. -/
theorem M2_conditional {K:Set (Points n)}{S:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hS:IsCompact S)(hy:S⊆Outside m)
   (d : Fin n→ℕ)(e:Fin m→ℕ) (L R:ℝ) (p h:ℕ) : Tendsto (fun r=> θ r/g r) τ (𝓝 1) ∧
    ∃ C:ℝ,0<C ∧ ∃ a:ℕ, ∃ T₀:ℝ, 2≤T₀ ∧ ∀ᶠ r in τ, ∀ T ≥ T₀,
     ∀x∈K,∀y∈S, ∀v:Inputs G d, Within L v → ∀ w:Inputs G e, Within R w →
       ‖crop p (θ r) (Yx N M x y v w (Real.log T))- crop p (θ r) (Dx N M y w (Real.log T) (cActual N x v h p (θ r)))‖ ≤ C*(T⁻¹^(h+1)+g r^(p+1))*(1+Real.log T)^a := by
   have he:= (paid_kinetic N M F proxy near H Y u compP full fixed hc q k hQ hq acts hk).1
   exact ⟨he,paid H hK hx hS hy d e L R p h (kinetic N F) he⟩
end
end YM.FVA2.GradedFar.Pose
