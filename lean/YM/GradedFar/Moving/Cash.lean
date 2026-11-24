import YM.GradedFar.Moving.Dress
import YM.GradedFar.Growth.Exact

/-! Arithmetic of the (G.1) step conclusion. The real applications
below consume its stated previous hypotheses (not a purchase of those here).
Use on all admitted profiles.
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "K"=> Kseries N M
local notation "α"=> Measure.adjust N.scheme N.criterion
local notation "ψ"=> GroupS.ψ N.criterion M ν
open Reg.Point (stepV)
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Z Z' : (d:ℕ)→Rolled G d) (S : (d:ℕ) → ℝ→FieldEnd G d)
    (F : (d:ℕ)→Pose.Plans G d) (Y : (d:ℕ)→ℝ→ Prediction G d)
    (θ : ℝ→ℝ) (called : θ=Pose.kinetic N (F 6)) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1))
    (hz : ∀ d,Righted (Z d)) (h : ∀ d, Beginning N θ d (F d)) (hy : ∀ d,Held N (Y d) (F d))
    (he : ∀ d, refit (Z d) (F d)) (hu : ∀ d, Layer N θ (S d) (Z d) (Z' d))

include H h he hy hz hu called ht

/-- The local (G.1) *steps* needed in the iteration; all p≥1. -/
lemma earned (p d : ℕ) (hp : 1≤p) : PTheta N M θ p ∧ PFrame N M (Zenith (Z' d)) θ p := by
    let P:= ℝ × ↥Growth.Small; let r (i:P):=i.1; let z (i:P):ℝ:=i.2.val
    have hθ:=time_value (I:=P) filed N M r z tendsto_comap (fun i=>i.2.property) H θ ht (hz 6) (h _) (Y _) (hy _) (he _) called hp
    have hf:=dressed (I:=P) filed N M r z tendsto_comap (fun i=>i.2.property) H θ ht (hz d) (h d) (Y _) (hy _) (he _) (hu _) hθ
    obtain ⟨C,hC,hq⟩:= hf.2.exists_pos; obtain ⟨D,hD,hθ⟩:= hθ.exists_pos
    constructor
    · refine ⟨D,hD,?_⟩; filter_upwards [eventually_comap.mp hθ.bound,positive_g simple] with r hr hv s hs
      have h := hr (r,⟨s,hs⟩) rfl; change theta_err N M θ p r s ≤ D * ‖g r^(p+1)‖ at h; rwa [Real.norm_of_nonneg (by positivity)] at h
    refine ⟨C,hC,?_⟩; filter_upwards [eventually_comap.mp hq.bound,positive_g simple] with r hr hv s hs
    have h := hr (r,⟨s,hs⟩) rfl; change frame_err N M (Zenith (Z' d)) θ p r s ≤ C * ‖g r^(p+1)‖ at h; rwa [Real.norm_of_nonneg (by positivity)] at h
lemma G1 {C B : ℝ} (c0:0<C)(b0:0<B) (hs : travels (Zenith (Z' d))) (q : ℕ) :
    (∀ᶠ p : ℕ in atTop, ∀ᶠ r in τ,∀ s≥0, exp s ≤ C*g r^(-B) →
      theta_err N M θ p r s+frame_err N M (Zenith (Z' d)) θ p r s ≤ g r^q) ∧
    ∀ᶠ r in τ, ∀ s≥0, exp s ≤ C*g r^(-B) →
      ‖Zenith (Z' d) r s‖ ≤ 2*exp s^d ∧ ‖Zenith (Z' d) (r*exp s) (-s)‖ ≤ 2 := by
    have h pc (hc : 1≤pc):= earned N M H Z Z' S F Y θ called ht hz h hy he hu pc d hc
    exact ⟨growing N M H _ _ ht hs (fun i hi=>(h i hi).2) (fun i hi=>(h i hi).1) c0 b0 q,
      Growth.norms N M H _ _ ht hs (fun i hi=>(h i hi).2) (fun i hi=>(h i hi).1) c0 b0⟩
end
end YM.FVA2.GradedFar.Moving
