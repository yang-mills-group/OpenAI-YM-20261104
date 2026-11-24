import YM.Integration.WilsonSeparatedPrefixCanonicalRate
import YM.Integration.WilsonSeparatedPrefixCanonicalRoof

/-! Dispense the complete two-flat optical bill before any physical cutoff
or period. The full stencil, all proper faces and the actual duration remain
in this calculation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalCash
open Function Filter Finset Lattice Wilson RG Source PhysicalNext.Repeat.Legato Marker Lodestar
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (run:WilsonPositionProgramNestedLengths.Nested R.rolls)(A₀ D L p:ℕ)(cap:ℝ):
    ∀ᶠ j:ℕ in atTop,∀k l:ℕ,j≤k+1 → l≤L →
    R.family.S.a j/R.family.S.a (k+1)≤(H (k+1))^A₀ → ∀w:I → ℝ,(∀i,0<w i) →
    (H (k+1))^D*(Real.exp cap*((WilsonSeparatedPrefixCanonicalTapRate.value R (k+1))⁻¹*
      WilsonOriginalOccupiedStencil.price (Fintype.card I))*
      (∑t:(Marks I).Mode,Poly.toll w t*WilsonSeparatedPrefixCanonicalHeard.roof R w t k j l))≤
      ((H (k+1))^p)⁻¹:=by
  let n:=Fintype.card I
  let debit:=6+(4+6*L)*n+D
  let T:=Real.exp cap*WilsonOriginalOccupiedStencil.price n*WilsonSeparatedPrefixCanonicalRoof.front I
  have pn:0≤WilsonOriginalOccupiedStencil.price n:=Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  have tn:0≤T:=by dsimp [T,WilsonSeparatedPrefixCanonicalRoof.front];positivity
  filter_upwards [WilsonSeparatedPrefixCanonicalRate.original R simple run A₀ debit n p T tn,
    WilsonSeparatedPrefixCanonicalRoof.original (I:=I) R simple pace,
    (RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j salary cutoff warm k l jf jl span w wp
  let x:=H (k+1)
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R (k+1)
  have xp:0≤x:=zero_le_one.trans (warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le jf))
  have ep:0<E:=Real.exp_pos _
  have head:0≤Real.exp cap*(E⁻¹*WilsonOriginalOccupiedStencil.price n):=by positivity
  have gross:=cutoff k l L jf jl w wp
  calc
    _ ≤ x^D*(Real.exp cap*(E⁻¹*WilsonOriginalOccupiedStencil.price n)*(WilsonSeparatedPrefixCanonicalRoof.front I*
        x^(6+(4+6*L)*n+6*(k+1-j)*n))):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left gross head) (pow_nonneg xp _)
    _ = T*x^(debit+6*(k+1-j)*n)*E⁻¹:=by
      dsimp [T,debit]
      simp only [pow_add]
      ring
    _ ≤ _:=salary (k+1) jf span

end YM.Integration.WilsonSeparatedPrefixCanonicalCash
