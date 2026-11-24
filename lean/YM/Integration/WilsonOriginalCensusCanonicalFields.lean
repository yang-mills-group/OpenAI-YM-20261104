import YM.Integration.WilsonOriginalCensusCanonicalRows
import YM.Integration.WilsonThermometerFrozenCopies
import YM.Integration.SignedRegisteredKernelPolynomial

/-! The actual preselected rows on every copied field, with their own cleared powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalFields
open Function Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonThermometerDeclaredSeeds WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows
open FVA1Physical.TwoReset Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonOriginalStarGradedScene
open QuadraticLocal.Earn QuadraticLocal.Sunrise XSpace Push Push.AbsoluteSums
open Comparison.RG02.Bulk Next.SectorChange AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open ActualRunCurvaturePackets NativeCurvatureTensor
open scoped Classical BigOperators

variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V→ℕ)(q:(j:V)→Choice R d j)(hd:∀j,0 < d j)
variable {n f:Side}(o:V→Site n)(σ:ℝ)
local notation "M" => row R d q hd o σ
local notation "J" => Stock.census V

def stamp (j:V):ℕ:=d j+1-pole R d (entry R d j (q j))

theorem painted (j:V)(t:ℝ)(x:Affinity.Wallet (room V))(z:Site f)(U:Config G f):
    (M j).paint x*↑(Loan.letter (M j).lamp (M j).atom z t U)=
      probe j x*SignedRegisteredKernelPolynomial.primitive (raw R d (entry R d j (q j))) z (stamp R d q j) t U:=by
  let a:=raw R d (entry R d j (q j))
  let Z:=normalizer a σ
  have sz:(unitAtom a σ).unmasked U z=Z⁻¹*a.unmasked U z:=evaluated a σ _
  have nz:(Z:ℂ)*(Z:ℂ)⁻¹=1:=mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive a σ).ne')
  have paid:(M j).lamp.stamp=stamp R d q j:=by
    have h:=WilsonOriginalStarGradedScene.pole_grade R d (entry R d j (q j))
    rw [site] at h
    have r:=WilsonOriginalStarSceneWords.low R d (entry R d j (q j))
    change rank R d _ -pole R d _ +d j+1-rank R d _= _
    unfold stamp
    have h':rank R d (entry R d j (q j)) ≤ d j+1+(rank R d (entry R d j (q j))-pole R d (entry R d j (q j))):=by omega
    omega
  change ((Z:ℂ)*probe j x)*↑(t^(M j).lamp.stamp*(unitAtom a σ).unmasked U z)=_
  rw [paid,sz]
  simp only [SignedRegisteredKernelPolynomial.primitive,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv]
  change _=probe j x*(_*(a.unmasked U z:ℂ))
  linear_combination probe j x*(t^(stamp R d q j):ℝ)*(a.unmasked U z:ℂ)*nz

theorem colored (h:n.val∣f.val)(x:Affinity.Wallet (room V))(L:Layout G)(pay:Finset Age)(s:Hot (J))(t:ℝ)(U:Config G f):
    (copyColor h M d (fun a=>(M a).paint x) L pay).mark s t U=
      ∑p:Fin (Pages n f),∑j:V,if (J).fire j=s.val then
        probe j x*SignedRegisteredKernelPolynomial.primitive (raw R d (entry R d j (q j)))
          (FVA1Physical.TwoReset.copy h (M j) p).center (stamp R d q j) t U else 0:=by
  classical
  unfold copyColor
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Air.craft,QuadraticLocal.Fk.grant,Air.sums,tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  have address:(ScatterR.actor (fun a=>FVA1Physical.TwoReset.copy h (M a) p) j).val=(J).fire j:=rfl
  by_cases selected:(J).fire j=s.val
  · simp only [if_pos (address.trans selected),if_pos selected]
    exact painted R d q hd o σ j t x _ U
  · simp only [if_neg (fun h=>selected (address.symm.trans h)),if_neg selected]

end YM.Integration.WilsonOriginalCensusCanonicalFields
