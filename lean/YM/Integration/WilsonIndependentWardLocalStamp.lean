import YM.Integration.WilsonIndependentMatchedTopWard
import YM.RegulatorIR.Profiles.Staple
import YM.Next.WARD_BIN.Stencils

/-! A fixed local cover scalar with a genuine finite-board matrix germ is
an order-zero incoming word at each translated position. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardLocalStamp
open Finset Filter Lattice RG Wilson Source Source.Drops WardBin PertExtension PertExtension.Series
open FormalOPE.RG10.InversionWard
open RegulatorIR RegulatorIR.Profiles RegulatorIR.Halo RegulatorIR.Geometry RegulatorIR.Prim
open scoped Classical BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}

theorem original (f:CoverConfig G→ℝ)(S:Finset Cover)(loc:LocalOn S f)
    (gauged:GaugeInvariant f)(n:Side)(o:Site n)(home:FitsIn S n)
    (printed:Proxy (WardBin.places o f)) : LocalStamp (fun _=>f) 0 := by
  obtain ⟨A,analytic,rep⟩:=printed
  have eq:f=fun U=>A (image (above o U)) := by
    funext U
    rw [←fromAbove loc home o U,rep]
    rfl
  have cont:Continuous f:=by
    rw [eq]
    exact analytic.continuous.comp (cont_image.comp (above_cont o))
  refine ⟨⟨cont.comp continuous_snd,fun _=>gauged,?_⟩,⟨S,fun _=>loc⟩,?_⟩
  · intro E _ _ _ U matrix _ _ _
    rw [eq]
    exact analytic.contDiffAt.comp 0 (contDiffAt_pi.mpr (fun i=>matrix (Lattice.lift (i.1-o),i.2)))
  · intro v
    obtain ⟨a,cap⟩:=isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
    refine ⟨max 0 a,le_max_left ..,Eventually.of_forall (fun t=>?_)⟩
    simpa only [outing,pow_zero,mul_one] using (cap (win G (t • v)) (Set.mem_univ _)).trans (le_max_right 0 a)

end YM.Integration.WilsonIndependentWardLocalStamp
