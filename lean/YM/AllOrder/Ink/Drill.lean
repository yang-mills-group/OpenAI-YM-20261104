import YM.AllOrder.Ink.Plant
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Pointwise
-- compact-dimension reconstruction to avoid differentiated limits at varying n
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
def jetPart (X:Type) [NormedAddCommGroup X][NormedSpace ℝ X] (k:ℕ): Submodule ℝ (X→ℝ) where
 carrier:= Rank X k
 zero_mem':= Rank.nil k 0
 add_mem' := fun _ h=> Rank.add ‹_› h
 smul_mem' :=fun _ _ h=> Rank.scal h _ -- arguments implicit?
-- to jet tuple, finite rank or multilinear GLM. 
abbrev leafJet (k:ℕ)(X:Type)[NormedAddCommGroup X][NormedSpace ℝ X] := ContinuousMultilinearMap ℝ (fun _:Fin k=> X) ℝ
local notation "R"=> jetPart X k
def jSpend (k j:ℕ): (jetPart X k) →ₗ[ℝ] leafJet j X where
 toFun x:= iteratedFDeriv ℝ j x.val 0
 map_add' := fun x y=> by
   have hx:= (show Rank _ _ x.val from x.property).read; have hy:= (show Rank _ _ y.val from y.property).read; exact iteratedFDeriv_add_apply (hx.smooth.contDiffAt.of_le le_top) (hy.smooth.contDiffAt.of_le le_top)
 map_smul' :=fun x p=> iteratedFDeriv_const_smul_apply (a:=x) ((show Rank _ _ p.val from p.property).read.smooth.contDiffAt.of_le le_top)
lemma major {x: R}:Rank X k x.val:= x.property -- scope syntax implicit using notation? 
def cells (k:ℕ): (jetPart X k) →ₗ[ℝ] (j:Fin (k+1))→ leafJet j.val X:= LinearMap.pi fun j=>jSpend k j.val
lemma full_span (x:X){f:X→ℝ} (h:Rank X k f): f x= ∑ i∈range (k+1), jet f i x:= by
 let L:= ContinuousLinearMap.toSpanSingleton ℝ x; let f':= f ∘ L; have he:= rank_taylor (h.lead L); let t:=delay (someJ f') k; rw [← one_smul ℝ x]; change f' 1=∑ i∈_,jet f i _; rw [one_smul,show f' 1=t 1 from congr_fun he.2 1]; unfold t delay; simp_rw [one_pow,one_smul]; apply Finset.sum_congr rfl; intro i _; exact jet_entry (h.read.smooth.contDiffAt.of_le le_top) _
lemma cells_active (k:ℕ): Injective (cells (X:=X) k):= by
 intro x y h; apply Subtype.ext; funext i; rw [full_span i (major (x:=x)), full_span i (major (x:=y))]; exact Finset.sum_congr rfl fun j hj=> congr_arg (fun w : leafJet j X=> _* w (fun _=>i)) (congr_fun h ⟨j,Finset.mem_range.mp hj⟩)
instance (k:ℕ): FiniteDimensional ℝ (jetPart X k) := .of_injective (cells k) (cells_active _)
def probeL {F : (X→ℝ)→ℝ}(h:LinTest X k F) : (jetPart X k)→L[ℝ]ℝ := LinearMap.toContinuousLinearMap {
 toFun x := F x.val
 map_add' := fun x y=> h.add x.val y.val x.property y.property
 map_smul' := fun x y=> h.scale y.val x y.property }
variable {ι : Type*}{Ω:Filter ι}
lemma station_rank {F: (X→ℝ)→ℝ}{f:X→ℝ}{g:ι→X→ℝ}(h:LinTest X k F)(hf: Rank X k f)(hg:∀ᶠ i in Ω, Rank X k (g i))(H:∀ x,Tendsto (fun i=>g i x) Ω (𝓝 (f x))): Tendsto (fun i=>F (g i)) Ω (𝓝 (F f)):= by
 let u: R:= ⟨f,hf⟩; let v(i:ι):R:= if h: Rank X k (g i) then ⟨g i,h⟩ else u
 have hv : ∀ᶠ i in Ω,(v i).val= g i:= hg.mono fun i hi=>by simp [v,hi]
 have hh : Tendsto v Ω (𝓝 u):= tendsto_subtype_rng.mpr ?_; -- lem
 apply (((probeL h).continuous.continuousAt.tendsto).comp hh).congr'; filter_upwards [hv] with i hi; exact congr_arg F hi
 exact tendsto_pi_nhds.mpr fun x=> (H x).congr' (hv.mono fun i hi=> (congr_fun hi x).symm)
lemma familiar (l:ℕ)(P:ℝ→X)(H:ContDiffAt ℝ ω P 0) (k:ℕ): LinTest X k (fun f=> someJ (f∘P) l):= ⟨fun f g hf hg=>congr_fun (some_add (hf.read.smooth.contDiffAt.comp _ H) (hg.read.smooth.contDiffAt.comp _ H)) l,fun f c h=>((eo_Act l (h.read.smooth.contDiffAt.comp _ H)).smul c).writes l le_rfl⟩
end Pointwise
end YM.AllOrder.Ink
