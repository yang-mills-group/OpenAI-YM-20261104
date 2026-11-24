import YM.FVA2.Orbit.Vertical
import YM.FVA2.Slice.Triad
/-!
# Particular Landau gauge for the manuscript and the matching input

`links` are on the permitted transverse slice in the even inversion convention. For the FP matrix (see `Sectors.lean`) use
mean-zero in place of pinning at root 0; include here the exact change
of variable for this. This is on the **transverse slice**. We explicitly need constant gauge tangencies
to stay in this Landau slice. See `Unroot` afterwards.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Finset Topology Lattice MeasureTheory
open Pert Orb
open Orbit -- FVA2
open MS MS.Koszul MS.Native MS.Bare MS.Native.Chart
open scoped ContDiff Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators
namespace FiniteOrbit
variable {G:Gauge} {n:Side}
local notation "T" => Site n
local notation "I" => PertExtension.Orb.OEdge n
local notation "Z" => Parameter G n
local notation "Y" => Potential G n
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "S" => SiteGhost G n
local notation "L" => Transverse G n
local notation "C" => G.Color
open scoped Classical
-- rooting projections
private lemma cen_grad (x:S) : ∃ z:Z, (∀ p:T, z.val p=x.val p-x.val 0) ∧ gZ z=gM x:= by
    let z:Z:=⟨fun p=>x.val p-x.val 0, ⟨fun p=> by dsimp only; rw [evenZ], sub_self (x.val 0)⟩⟩
    exact ⟨z,fun _=>rfl,Subtype.ext (funext (fun i=> by change x.val _-x.val 0-(x.val _-x.val 0)=x.val _- x.val _; abel))⟩
def renorm (G:Gauge)(n:Side) : SiteGhost G n ≃ₗ[ℝ] Root G n :=
  let M : SiteGhost G n ≃ₗ[ℝ] SiteGhost G n:= LinearEquiv.ofBijective (dLin ∘ₗ gM) ⟨mean_inj, LinearMap.surjective_of_injective mean_inj⟩
  M.trans ((bridgeEquiv G n).symm.trans (gaugeAngles G n).symm)
lemma renorm_eq (x:S) : (∀ p:T, atSite p (renorm G n x)=x.val p - x.val 0) ∧ gZ (gaugeAngles G n (renorm G n x))= gM x:= by
    obtain ⟨z,hz,hh⟩:=cen_grad x; have he:gaugeAngles G n (renorm G n x)=z:= by
      apply (bridgeEquiv G n).injective; simp only [renorm,LinearEquiv.trans_apply,gaugeAngles,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply]; exact (congr_arg (dLin (G:=G) (n:=n)) hh).symm
    exact ⟨fun p=>by rw [← angles_eq,he];exact hz p, by rw [he,hh]⟩
-- by parts
lemma by_parts (x : Lot G T)(f: Chart.City G T) : linkPair (grad x) f=(∑ v:T, inner ℝ (x v) (divB f v))/2 := by
    let F := fun v:T=> ∑ i:Axis, inner ℝ (x (v+step i)) (f (v,i)); unfold linkPair grad divB
    congr 1
    rw [Fintype.sum_prod_type (α₁:=T)]; simp_rw [inner_sub_left, inner_sum (𝕜:=ℝ),inner_sub_right,Finset.sum_sub_distrib]; congr 1
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    let l:=Equiv.addRight (step i : T); apply Fintype.sum_equiv l; intro v; change _= inner ℝ _ (f (v+step i-step i,i)); rw [add_sub_cancel_right]; rfl
lemma by_parts_L (z:Lot G T)(v:L): linkPair (grad z) (includeA G n v)=0:= by rw [by_parts, show divB ((includeA G n) v)=0 from div_none v]; simp

def traceLink (G:Gauge)(n:Side) : Transverse G n→ₗ[ℝ] Rep G n := (touches G n).comp (LinearMap.ker dLin).subtype
def traceCont (G:Gauge)(n:Side) : Transverse G n →L[ℝ] Rep G n where
  toLinearMap:= traceLink G n
  cont:= continuous_pi fun i=> ((continuous_apply (A:=fun _: Edge (Site n)=>G.Color) i.val).comp continuous_subtype_val).comp continuous_subtype_val
lemma germ_trace (G:Gauge)(n:Side) : ContDiffAt ℝ ω (⇑(traceLink G n)) 0:=
 (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Transverse G n) (F:=Rep G n) (traceCont G n)).contDiffAt
lemma traceLink_line (x:R)(y:L) : fderiv ℝ (orbiting ⇑(traceLink G n)) 0 (x,y)=vertical 0 x + traceLink G n y:= by
  let t:= traceCont G n; have h : ContDiffAt ℝ ω (⇑t) 0:= germ_trace G n
  obtain hh:= (axes_later (⇑t) h t.map_zero).self_of_nhds x y; rw [t.map_zero,show fderiv ℝ t 0=t from ContinuousLinearMap.fderiv (E:=Transverse G n) (F:=Rep G n) (𝕜:=ℝ) t] at hh; exact hh
lemma telescope (x:R)(y:L) : fderiv ℝ (orbiting ⇑(traceLink G n)) 0 (x,y) = touches G n ( -gZ (gaugeAngles G n x) + y.val ):= by rw [traceLink_line,vertical_flat, map_add,map_neg];rfl
private lemma trace_valid (ev:Even n.val) : Bijective (fderiv ℝ (orbiting ⇑(traceLink G n)) 0):= by
 let D:= fderiv ℝ (orbiting ⇑(traceLink G n)) 0; let U:= fanEquiv (G:=G) ev; let W':=gaugeAngles G n; let A:= bridgeEquiv G n; have hb(y:L) : dLin y.val=0:= y.property
 constructor
 · rintro ⟨x,y⟩ ⟨z,w⟩ H; rw [telescope,telescope] at H; have hh:=rep_inj H; have he:= congr_arg (dLin (G:=G) (n:=n)) hh; simp only [map_add,map_neg,hb,add_zero,neg_inj] at he; obtain rfl:= W'.injective (A.injective he); exact Prod.ext rfl (Subtype.ext (add_left_cancel hh))
 intro x; let z:= A.symm (dLin (U.symm x)); let y:= U.symm x - gZ z; let l: L:= ⟨y,show dLin y=0 from by unfold y; rw [map_sub, show dLin (gZ z)=_ from A.apply_symm_apply _, sub_self]⟩
 refine ⟨(W'.symm (-z), l),?_⟩
 rw [telescope,show gaugeAngles G n (W'.symm (-z))= -z from W'.apply_symm_apply _,map_neg,neg_neg, show gZ z + l.val= U.symm x from (add_sub_cancel _ _)] -- lemma orientation
 exact U.apply_symm_apply x
/-- Real Landau Screen. -/
def land (G: Gauge){n: Side}(ev:Even n.val) : Screen G n (Transverse G n) where
 σ:= traceLink G n
 germ:= germ_trace G n
 origin:= map_zero _
 valid:= trace_valid ev
lemma tilted_here (ev:Even n.val)(x:R)(y:L) : (land G ev).hurdle (x,y)=vertical 0 x + traceLink G n y:= traceLink_line x y
lemma landed (ev:Even n.val)(x:L) : Orbit.ignite ((land G ev).σ x)=MS.Native.Chart.nation (includeA G n x):= lit x.val
-- A linear function picking the normal part in this gauge

def root_test (ev:Even n.val) (x:S) : Rep G n →ₗ[ℝ] ℝ where
 toFun p:= linkPair (grad x.val) ((fanEquiv ev).symm p).val
 map_add' p q:= by simp [map_add,linkPair,inner_add_right,Finset.sum_add_distrib,add_div]
 map_smul' c p:= by simp [map_smul,linkPair,real_inner_smul_right,← Finset.mul_sum,mul_div_assoc]
lemma tests_blank (ev:Even n.val) (z:S)(x:L) : root_test ev z (traceLink G n x)=0:= by
    change linkPair _ ((fanEquiv ev).symm (fanEquiv ev x.val)).val=0; rw [LinearEquiv.symm_apply_apply]; exact by_parts_L z.val x
end FiniteOrbit
end YM.FVA2.Slice
