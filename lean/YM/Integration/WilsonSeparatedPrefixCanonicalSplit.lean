import YM.Integration.WilsonSeparatedPrefixCanonicalCash

/-! Half of the original separated reserve remains available for a genuine
trial-peer wallet whose inverse grows faster than every fixed power. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalSplit
open Function Filter Finset Lattice Wilson RG Source PhysicalNext.Repeat.Legato Marker Lodestar
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

def reserve(f:ℕ):ℝ:=Real.exp ((Real.log (H f))^2/64)

theorem half (simple:G.Simple)(run:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (A₀ D m P:ℕ)(C:ℝ)(cp:0≤C):
    ∀ᶠ j:ℕ in atTop,∀f:ℕ,j≤f → R.family.S.a j/R.family.S.a f≤(H f)^A₀ →
    reserve R f*(C*(H f)^(D+6*(f-j)*m)*(WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹)≤((H f)^P)⁻¹:=by
  filter_upwards [WilsonSeparatedPrefixCanonicalRate.original R simple run A₀ (2*D) (2*m) (2*P) (C^2) (sq_nonneg _),
    (RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j received warm f jf span
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R f
  let U:=reserve R f
  let x:=H f
  have xp:0≤x:=zero_le_one.trans (warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le jf))
  have ep:0<E:=Real.exp_pos _
  have up:0<U:=Real.exp_pos _
  have square:U^2=E:=by
    change (Real.exp _)^2=Real.exp _
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have product:E*(E⁻¹)^2=E⁻¹:=by field_simp [ep.ne']
  let e:=D+6*(f-j)*m
  have links:(x^e)^2=x^(2*D+6*(f-j)*(2*m)):=by
    rw [←pow_mul];congr 1;dsimp [e];ring
  have same:(U*(C*x^e*E⁻¹))^2=C^2*x^(2*D+6*(f-j)*(2*m))*E⁻¹:=by
    calc
      _ = C^2*(x^e)^2*(U^2*(E⁻¹)^2):=by ring
      _ = _:=by rw [square,product,links]
  have target:((x^P)⁻¹)^2=(x^(2*P))⁻¹:=by rw [←inv_pow,←pow_mul,Nat.mul_comm P 2,inv_pow]
  apply (sq_le_sq₀ (mul_nonneg up.le (mul_nonneg (mul_nonneg cp (pow_nonneg xp _)) (inv_nonneg.mpr ep.le))) (inv_nonneg.mpr (pow_nonneg xp _))).mp
  change (U*(C*x^e*E⁻¹))^2≤((x^P)⁻¹)^2
  rw [same,target]
  exact received f jf span

theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (run:WilsonPositionProgramNestedLengths.Nested R.rolls)(A₀ D L p:ℕ)(cap:ℝ):
    ∀ᶠ j:ℕ in atTop,∀k l:ℕ,j≤k+1 → l≤L →
    R.family.S.a j/R.family.S.a (k+1)≤(H (k+1))^A₀ → ∀w:I → ℝ,(∀i,0<w i) →
    reserve R (k+1)*((H (k+1))^D*(Real.exp cap*((WilsonSeparatedPrefixCanonicalTapRate.value R (k+1))⁻¹*
      WilsonOriginalOccupiedStencil.price (Fintype.card I))*
      (∑t:(Marks I).Mode,Poly.toll w t*WilsonSeparatedPrefixCanonicalHeard.roof R w t k j l)))≤
      ((H (k+1))^p)⁻¹:=by
  let n:=Fintype.card I
  let debit:=6+(4+6*L)*n+D
  let T:=Real.exp cap*WilsonOriginalOccupiedStencil.price n*WilsonSeparatedPrefixCanonicalRoof.front I
  have pn:0≤WilsonOriginalOccupiedStencil.price n:=Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  have tn:0≤T:=by dsimp [T,WilsonSeparatedPrefixCanonicalRoof.front];positivity
  filter_upwards [half R simple run A₀ debit n p T tn,
    WilsonSeparatedPrefixCanonicalRoof.original (I:=I) R simple pace,
    (RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j bill cutoff warm k l jf jl span w wp
  let x:=H (k+1)
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R (k+1)
  have xp:0≤x:=zero_le_one.trans (warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le jf))
  have ep:0<E:=Real.exp_pos _
  have head:0≤Real.exp cap*(E⁻¹*WilsonOriginalOccupiedStencil.price n):=by positivity
  have budget:=cutoff k l L jf jl w wp
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)) (bill (k+1) jf span)
  calc
    _ ≤ x^D*(Real.exp cap*(E⁻¹*WilsonOriginalOccupiedStencil.price n)*(WilsonSeparatedPrefixCanonicalRoof.front I*
        x^(6+(4+6*L)*n+6*(k+1-j)*n))):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left budget head) (pow_nonneg xp _)
    _ = T*x^(debit+6*(k+1-j)*n)*E⁻¹:=by
      dsimp [T,debit]
      simp only [pow_add]
      ring

end YM.Integration.WilsonSeparatedPrefixCanonicalSplit
