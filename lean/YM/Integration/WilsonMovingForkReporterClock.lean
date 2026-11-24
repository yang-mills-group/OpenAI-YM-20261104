import YM.Integration.WilsonOriginalTwoFlatPublicOuter

/-! The actual elected reporting clock at a source that fits a polynomial
span is bounded in the measuring coupling at the smallest physical radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterClock
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot
open scoped Topology Classical
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(B:ℕ):
    ∃C:ℝ,0<C ∧ ∀ᶠ r in trail,∀j,a j ≤ r → r ≤ (β j)^B*a j →
      (β j)*(wilson z r)^2 ≤ C:=by
  let s:=G.slopeConstant
  have sp:0<s:=Gauge.slopeConstant_pos simple
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have little:=(Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (s*(B:ℝ))).comp
    (hat_rate (P) simple)
  simp only [mul_zero] at little
  obtain ⟨m,after⟩:=eventually_atTop.mp (little.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2)))
  have basepos:0 < (P).clock.bar:=(P).clock.bar_pos
  refine ⟨2*((P).clock.bar+s*(s⁻¹+1)),by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,link.positive,(link.conforms simple).eventually
    (ge_mem_nhds zero_lt_one),link.running.eventually (ge_mem_nhds (by linarith:s⁻¹<s⁻¹+1)),
    (ge_mem_nhds (R.family.S.a_pos m)).filter_mono nhdsWithin_le_nhds] with r rp gp gu run fine
  change 0<r at rp
  change LogV r*(wilson z r)^2 ≤ s⁻¹+1 at run
  intro j aj span
  have mj:m≤j:=by
    by_contra! earlier
    exact (not_le_of_gt (R.family.S.strictAnti earlier)) (aj.trans fine)
  have hp:0<β j:=(zero_lt_one.trans ((P).fits.delayed j))
  have ap:=R.family.S.a_pos j
  have crop:=after j mj
  change s*(B:ℝ)*(Real.log (β j)/(β j))≤1/2 at crop
  rw [←mul_div_assoc] at crop
  have loss:=(div_le_iff₀ hp).mp crop
  have inv:(a j)⁻¹ ≤ (β j)^B*r⁻¹:=by
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ ap rp]
    simpa only [one_mul] using span
  have sizes:=Real.log_le_log (inv_pos.mpr ap) inv
  rw [Real.log_mul (pow_pos hp B).ne' (inv_pos.mpr rp).ne',Real.log_pow] at sizes
  change R.family.S.scale j ≤ (B:ℝ)*Real.log (β j)+LogV r at sizes
  have defn:β j=(P).clock.bar+s*R.family.S.scale j:=rfl
  have bk:β j≤2*((P).clock.bar+s*LogV r):=by
    have geom:=mul_le_mul_of_nonneg_left sizes sp.le
    linarith only [defn,geom,loss,mul_add s ((B:ℝ)*Real.log (β j)) (LogV r),
      mul_assoc s (B:ℝ) (Real.log (β j))]
  have pay:=mul_le_mul_of_nonneg_right bk (sq_nonneg (wilson z r))
  have two:(wilson z r)^2≤1:=pow_le_one₀ gp.le gu
  have bar:=mul_le_mul_of_nonneg_left two (P).clock.bar_pos.le
  simp only [mul_one] at bar
  have normalized:=mul_le_mul_of_nonneg_left run sp.le
  calc
    _ ≤ 2*((P).clock.bar+s*LogV r)*(wilson z r)^2:=pay
    _ = 2*((P).clock.bar*(wilson z r)^2+s*(LogV r*(wilson z r)^2)):=by ring
    _ ≤ _:=by linarith only [bar,normalized]


end YM.Integration.WilsonMovingForkReporterClock
