import YM.Integration.WilsonIndependentWardEulerStamps
import YM.Integration.WilsonIndependentMatchedTopContacts

/-! Exact Euler and divergence rows on the inverted finite Wilson board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardEulerBoard
open Finset Function Lattice RG Source WardBin Wilson PowerSeries PertExtension PertExtension.Orb
open XSpace FVA2 FormalOPE.RG10 FormalOPE.RG10.InversionWard
open RegulatorIR RegulatorIR.Profiles
open WilsonIndependentWardEulerStamps
open scoped Classical Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}(d:Axis)(o:Site n)

theorem admissible (fit:FitsIn (scope d) n) :
    PreTest (places o (energy (G:=G) d)) ∧ PreTest (places o (discharge (G:=G) d)) := by
  have folded_pre {f:CoverConfig G→ℝ}(p:LocalStamp (fun _=>f) 0)(px:Proxy (places o f)) : PreTest (places o f) := by
    apply px.active
    intro t _ U
    change f (expandAt o (Lattice.gauge t U))=f (expandAt o U)
    rw [expandAt_gauge]
    exact p.people.guise 0 _ _
  have A:=printed (G:=G) d o
  constructor
  · exact folded_pre (original d).1 ((A.pair A).after (fun v=>⟪v.1,v.2⟫_ℝ) (contDiff_fst.inner ℝ contDiff_snd))
  · apply folded_pre (original d).2
    rw [folded_trace d o fit]
    exact Proxy.sum _ (fun i _=>WilsonIndependentWardSingleSlope.scalar _
      (A.after _ (innerSL ℝ (dirs G i)).contDiff) _)

theorem mutable : LocalOn (footprint (scope d) o) (fun U:Config G n=>euler U (edgeAt (b d) o)) := by
  rw [←folded]
  simpa only [footprint,places,Finset.coe_image] using! LocalOn.expandAt (↑(scope d)) _ (supported (G:=G) d) o

theorem actual_energy (hn:Even n.val)(U:Config G n)(live:retained U) :
    effort (edgeAt (b d) o) (fun V:Config G n=>euler V (edgeAt (b d) o)) U=places o (energy d) U := by
  rw [agrees hn (edgeAt (b d) o) U live]
  have root:=congrFun (folded (G:=G) d o) U
  change ⟪euler U _,euler U _⟫_ℝ=⟪places o (vector d) U,places o (vector d) U⟫_ℝ
  rw [root]

theorem actual_divergence (fit:FitsIn (scope d) n)
    (clear:avoids (edgeAt (b d) o) (footprint (scope d) o)) :
    fallout (edgeAt (b d) o) (fun V:Config G n=>euler V (edgeAt (b d) o))=places o (discharge d) := by
  rw [folded_trace d o fit]
  funext U
  rw [singlyDiv _ (mutable d o) clear (proxy_force _) U,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun H:Config G n→ℝ => slope (edgeAt (b d) o) (dirs G i) H U)
  funext V
  exact congrArg (fun x=>⟪dirs G i,x⟫_ℝ) (congrFun (folded (G:=G) d o) V).symm

variable {s:XSpace.Period}(T:s.Tree)

theorem tree_retained (x:T.Field G) : retained (T.links x) := by
  funext i
  rw [all_reversed]
  change (s.restore _ (s.reflect i))⁻¹=s.restore _ i
  rw [s.restore_reflect,inv_inv]

theorem tree_energy (o:Site s.side) :
    BareOrb.stencil T (effort (edgeAt (b d) o) (fun V:Config G s.side=>euler V (edgeAt (b d) o))) =
      BareOrb.stencil T (places o (energy d)) := by
  apply congrArg (TreeFormal.enter (G:=G) T)
  funext v
  exact actual_energy d o (even_iff_two_dvd.mpr s.even) (T.links v) (tree_retained T v)

end YM.Integration.WilsonIndependentWardEulerBoard
