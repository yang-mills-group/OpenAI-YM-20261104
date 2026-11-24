import YM.Comparison.RG02.Bulk.Fk
import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Shadows

/-!
# The normalized Haar factor in the actual kernel

The officer term in `Bulk.Fk` uses the chart's normalized Jacobian.
Its finite product has the universal `LocalH.spin` germ on the same
joint field space. The original path, loop term and field coordinates
are retained before taking any finite derivative.

These are germ identities. They impose no bound on the chart scale
or radius and do not replace the Haar density away from the origin.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualKernelHaar
open Filter Finset RG Precision Lattice Tree
open Comparison.RG02
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio)

local notation "E" => Bulk.Joint S F (G := G)

include K in
/-- The complete finite normalized Haar product, on the original joint
field space, has the universal spin germ. -/
theorem normalized_haar_germ :
    (fun z : E => ∏ i, O.J (z.2.2 i)) =ᶠ[𝓝 0]
      (fun z : E => ∏ i, LocalH.spin G (z.2.2 i)) := by
  have hi (i : F.Free) :
      Tendsto (fun z : E => z.2.2 i) (𝓝 0) (𝓝 0) :=
    ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).tendsto 0
  filter_upwards [eventually_all.mpr
    (fun i : F.Free => (hi i).eventually (MS.Bare.Maurer.real_ratio K.ratio))]
    with z hz
  exact Finset.prod_congr rfl (fun i _ => hz i)

/-- The complete officer retains the original loop term and the minus
sign in front of the logarithm of the full Haar product. -/
theorem officer_germ :
    Bulk.officer F K =ᶠ[𝓝 (0 : E)]
      (fun z : E => loop P (Work.F03.live F z.2) -
        Real.log (∏ i, LocalH.spin G (z.2.2 i))) := by
  filter_upwards [normalized_haar_germ K F] with z hz
  exact congrArg (fun j : ℝ => loop P (Work.F03.live F z.2) - Real.log j) hz

/-- Every finite derivative of the same officer can be read from the
universal Haar germ, without any additional smoothness premise. -/
theorem officer_derivatives (n : ℕ) :
    iteratedFDeriv ℝ n (Bulk.officer F K) 0 =
      iteratedFDeriv ℝ n
        (fun z : E => loop P (Work.F03.live F z.2) -
          Real.log (∏ i, LocalH.spin G (z.2.2 i))) 0 :=
  ((officer_germ K F).iteratedFDeriv ℝ n).eq_of_nhds

end YM.Integration.ActualKernelHaar
