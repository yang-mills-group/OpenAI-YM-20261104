import YM.Integration.WilsonSeparatedOriginalSlabWatchBorn
import YM.MSbar.UV.Compact
import YM.RG05Readout.Nuclear.Pings

/-! Averaging the one common centre in the test itself at the original physical scale. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchMean
open Function Set Filter MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits RG17 PhysMS
open Next.UVStress RG05Readout RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabPhysicalBox WilsonSeparatedOriginalSlabWatchSupport WilsonSeparatedOriginalSlabWatchDensity WilsonSeparatedOriginalSlabWatchFubini WilsonSeparatedOriginalSlabWatchNormalization
open scoped Topology BigOperators ContDiff Classical
variable {I:Type}[Fintype I]

def delta (θ:ℝ)(z:E4):Cloud I:=fun _=> -(θ • z)

def leaf (θ:ℝ)(Ψ:Wave I)(g:Body)(p:Cloud I×E4):ℂ:=g.val p.2*Ψ.val (p.1+delta θ p.2)

theorem regular (θ:ℝ)(Ψ:Wave I)(g:Body):ContDiff ℝ ∞ (leaf θ Ψ g):=by
  have hg:ContDiff ℝ ∞ g.val:=g.property
  have hΨ:ContDiff ℝ ∞ Ψ.val:=Ψ.property
  apply (hg.comp contDiff_snd).mul;apply hΨ.comp;apply contDiff_fst.add;apply contDiff_pi.mpr;intro i;change ContDiff ℝ ∞ (fun p:Cloud I×E4=> -(θ • p.2));fun_prop

def wave (θ:ℝ)(Ψ:Wave I)(g:Body):Wave I:=⟨MSbar.High.sectionL (leaf θ Ψ g) Native.box volume,MSbar.High.section_smooth (regular θ Ψ g) Pert.Cellular.cells_compact⟩

def charge (g:Body):ℝ:=∫z in Native.box,‖g.val z‖

theorem jet (θ:ℝ)(Ψ:Wave I)(g:Body)(n:ℕ)(x:Cloud I)(z:E4):
    MSbar.High.half n (leaf θ Ψ g) (x,z)=g.val z • iteratedFDeriv ℝ n Ψ.val (x+delta θ z):=by
  change iteratedFDeriv ℝ n (g.val z • (fun y:Cloud I=>Ψ.val (y+delta θ z))) x=_
  have smooth:ContDiff ℝ n (fun y:Cloud I=>Ψ.val (y+delta θ z)):=(lit Ψ n).comp (contDiff_id.add contDiff_const)
  rw [iteratedFDeriv_const_smul_apply smooth.contDiffAt,iteratedFDeriv_comp_add_right]

theorem tall (θ:ℝ)(Ψ:Wave I)(g:Body){D:ℕ}{R e:ℝ}(cost:Nuclear.Tall Ψ D R e):Nuclear.Tall (wave θ Ψ g) D R (charge g*e):=by
  intro n hn x;change ‖iteratedFDeriv ℝ n (MSbar.High.sectionL _ Native.box volume) x‖≤_
  rw [MSbar.High.under_leaf (regular θ Ψ g) Pert.Cellular.cells_compact]
  have paid:IntegrableOn (fun z=>‖g.val z‖*(R^n*e)) Native.box volume:=
    ((show ContDiff ℝ ∞ g.val from g.property).continuous.norm.mul continuous_const).continuousOn.integrableOn_compact Pert.Cellular.cells_compact
  calc
    _≤∫z in Native.box,‖g.val z‖*(R^n*e):=by
      apply norm_integral_le_of_norm_le paid;apply Eventually.of_forall;intro z;rw [jet,norm_smul];exact mul_le_mul_of_nonneg_left (cost n hn _) (norm_nonneg _)
    _=R^n*(charge g*e):=by rw [integral_mul_const,charge];ring

end YM.Integration.WilsonSeparatedOriginalSlabWatchMean
