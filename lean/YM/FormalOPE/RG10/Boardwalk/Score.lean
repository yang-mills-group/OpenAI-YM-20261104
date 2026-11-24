import YM.FormalOPE.RG10.Boardwalk.Orchestra
/-! # Graded Gram and Frame inverse inventory

 one fixed horizon n. Decimal near polynomial costs from declared Z, converting both matrix and
 its inverse in the same filtration/clock. Supports Hermit as real operators after orientation (real
 diagnostics). Use also before orientation where determinant placement & real detector/basis
 fields from Boots (RG08/11) are given; not asserting a positive lower bound without this! -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open RG10.Profile Gliss Gazebo Matrix Position.Grade Peal Trellis
open scoped Topology BigOperators Classical ContDiff
variable {I J K T : Type*}{l:Filter I}{P:Path l}{r:ℕ}
variable {L M : I→ Matrix J K fps}
abbrev Bars (P:Path l) (r:ℕ)(L M:I→Matrix J K fps):= ∀ i j, Posi P r (fun k=>L k i j) (fun k=>M k i j)
namespace Bars
variable {A B:I→ Matrix J K fps}
lemma add (hL:Bars P r L M)(hA:Bars P r A B): Bars P r (fun i=> L i+A i) (fun i=> M i+B i) := fun i j=> (hL i j).join (hA i j)
lemma sub (hL:Bars P r L M)(hA:Bars P r A B): Bars P r (fun i=> L i-A i) (fun i=> M i-B i) := fun i j=> (hL i j).minus (hA i j)
lemma fixed (A:Matrix J K fps): Bars P r (fun _=> A) (fun _=>A):= fun i j=> Posi.fixed (A i j)
lemma fit {R S:I→ Matrix J K fps}(hR:R=ᶠ[l] L)(hS:S=ᶠ[l] M)(hz:Bars P r R S): Bars P r L M:= fun i j=> (hz i j).fits (hR.mono fun _ hi=>congr_fun₂ hi i j) (hS.mono fun _ hi=>congr_fun₂ hi i j)
lemma mul [Fintype K]{A B:I→ Matrix K T fps}(hL:Bars P r L M)(hA:Bars P r A B) : Bars P r (fun i=> L i*A i) (fun i=> M i*B i) := fun i j=> Posi.sum _ (fun k _=> (hL i k).mul (hA k j))
variable {F G:I→ Matrix J J fps}[Fintype J][DecidableEq J](h : Bars P r F G)
-- needed even for Gram powers, through r not one of the lower inverse costs only
include h
lemma determinant : Posi P r (fun i=>(F i).det) (fun i=>(G i).det):= by simp_rw [Matrix.det_apply']; apply Posi.sum; intro i _; exact (Posi.fixed _).mul (Posi.product univ (fun j _=> h (i j) j))
lemma adjoint : Bars P r (fun i=>(F i).adjugate) (fun i=>(G i).adjugate):= by
 intro i j; simp_rw [Matrix.adjugate_apply]; apply determinant; intro k a; simp_rw [Matrix.updateRow_apply]; split_ifs; exact Posi.fixed _; exact h k a
lemma leasing (hz:Acr P (fun i=>constantCoeff ((F i).det))): Bars P r (fun i=> (F i)⁻¹) (fun i=>(G i)⁻¹) := by
 intro i j; exact ((determinant h).rates hz).mul (adjoint h i j)
omit h
variable (hA:Acr P (fun i=>constantCoeff ((F i).det)))
include hA
lemma allowed : ∀ᶠ i in l,IsUnit (F i).det:= hA.openAt.mono (fun i hi=>by simpa [PowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero] using hi)
include h
lemma coherent : Acr P (fun i=>constantCoeff (G i).det):= hA.rent (determinant h).constants
omit hA h
lemma obligate {M:Matrix J J ℝ}(h : IsUnit M.det)(hz: Tendsto (fun i=> (F i).map constantCoeff) l (𝓝 M)): Acr P (fun i=>constantCoeff (F i).det):= by
 simp_rw [RingHom.map_det]; exact Acr.source (isUnit_iff_ne_zero.mp h) (continuous_id.matrix_det.continuousAt.tendsto.comp hz) -- type
end Bars
end YM.FormalOPE.RG10.Boardwalk
