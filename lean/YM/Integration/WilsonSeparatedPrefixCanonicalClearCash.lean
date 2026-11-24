import YM.Integration.WilsonSeparatedPrefixCanonicalSplit
import YM.Integration.WilsonSeparatedPrefixCanonicalClearHeard

/-! The clear-field hearing spends one actual radius for each occupied name at each date. The nested geometry finances that finite collar. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearCash
open Function Filter Finset Lattice Wilson RG Source PhysicalNext.Repeat.Legato Marker Lodestar
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

theorem reserved (simple:G.Simple)(run:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (window D target:ℕ)(cap:ℝ):
    ∀ᶠ j:ℕ in atTop,∀f:ℕ,j≤f → R.family.S.a j/R.family.S.a f≤(H f)^window →
    ∀(w:I→ℝ), (∀v,0<w v) →
      WilsonSeparatedPrefixCanonicalSplit.reserve R f*((H f)^D*(Real.exp cap*
        ((WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹*WilsonOriginalOccupiedStencil.price (Fintype.card I))*
        (∑s:(Stock.census I).Mode,Poly.toll w s*WilsonSeparatedPrefixCanonicalClearHeard.roof R w s f j)))≤((H f)^target)⁻¹:=by
  let n:=Fintype.card I
  let cost:=WilsonSeparatedPrefixCanonicalClearPost.fare I
  let states:ℝ:=Fintype.card (Stock.census I).Mode
  let stamp:=WilsonOriginalOccupiedStencil.price n
  have cp:0≤cost:=(Real.exp_pos _).le
  have sp:0≤ states:=Nat.cast_nonneg _
  have jp:0≤ stamp:=Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun h _=>norm_nonneg _))
  let C:=Real.exp cap*stamp*(states*cost)
  have credit:0≤C:=mul_nonneg (mul_nonneg (Real.exp_pos _).le jp) (mul_nonneg sp cp)
  filter_upwards [WilsonSeparatedPrefixCanonicalSplit.half R simple run window D n target C credit,
    (RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j half warm f jf span w pos
  let x:=H f
  let e:=6*(f-j)*n
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R f
  let U:=WilsonSeparatedPrefixCanonicalSplit.reserve R f
  have hot:1≤x:=warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le jf)
  have modes(s:(Stock.census I).Mode):
      Poly.toll w s*WilsonSeparatedPrefixCanonicalClearHeard.roof R w s f j≤cost*x^e:=by
    have tp:0<Poly.toll w s:=Poly.worth pos s
    have cut:6*(f-j)*s.val.card≤e:=Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    change Poly.toll w s*(cost*x^(6*(f-j)*s.val.card)/Poly.toll w s)≤_
    calc _ = cost*x^(6*(f-j)*s.val.card):=by field_simp [tp.ne']
         _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hot cut) cp
  have book:(∑s:(Stock.census I).Mode,Poly.toll w s*WilsonSeparatedPrefixCanonicalClearHeard.roof R w s f j)≤ states*(cost*x^e):=by
    exact (Finset.sum_le_sum (fun s _=>modes s)).trans_eq (by simp [states])
  have ep:0<E:=Real.exp_pos _
  have up:0<U:=(Real.exp_pos _)
  have unit:0≤x^D:=pow_nonneg (zero_le_one.trans hot) _
  have ray:0≤Real.exp cap*(E⁻¹*stamp):=mul_nonneg (Real.exp_pos _).le (mul_nonneg (inv_nonneg.mpr ep.le) jp)
  calc _ ≤ U*(x^D*(Real.exp cap*(E⁻¹*stamp)*(states*(cost*x^e)))):=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left book ray) unit) up.le
       _ = U*(C*x^(D+6*(f-j)*n)*E⁻¹):=by rw [pow_add];dsimp only [C,e];ring
       _ ≤ _:=half f jf span

theorem original (simple:G.Simple)(run:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (window D target:ℕ)(cap:ℝ):
    ∀ᶠ j:ℕ in atTop,∀f:ℕ,j≤f → R.family.S.a j/R.family.S.a f≤(H f)^window →
    ∀(w:I→ℝ), (∀v,0<w v) →
      (H f)^D*(Real.exp cap*((WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹*
        WilsonOriginalOccupiedStencil.price (Fintype.card I))*
        (∑s:(Stock.census I).Mode,Poly.toll w s*WilsonSeparatedPrefixCanonicalClearHeard.roof R w s f j))≤((H f)^target)⁻¹:=by
  filter_upwards [reserved (I:=I) R simple run window D target cap,
    (RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j pay warm f jf span w pos
  have out:=pay f jf span w pos
  have res:1≤WilsonSeparatedPrefixCanonicalSplit.reserve R f:=Real.one_le_exp (by positivity)
  by_cases h:0≤(H f)^D*(Real.exp cap*((WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹*
      WilsonOriginalOccupiedStencil.price (Fintype.card I))*
      (∑s:(Stock.census I).Mode,Poly.toll w s*WilsonSeparatedPrefixCanonicalClearHeard.roof R w s f j))
  · exact (le_mul_of_one_le_left h res).trans out
  · have hp:0≤H f:=zero_le_one.trans (warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le jf))
    exact (le_of_not_ge h).trans (inv_nonneg.mpr (pow_nonneg hp _))

end YM.Integration.WilsonSeparatedPrefixCanonicalClearCash
end
