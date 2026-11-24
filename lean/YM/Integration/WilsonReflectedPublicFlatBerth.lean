import YM.Integration.WilsonReflectedOpticalWidth
import YM.Integration.WilsonInvariantActionSeparatedCells

/-! A physical intermediate mesh clears the quadratic Wilson support
radius on each truly occupied cell of the dilated separated test. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicFlatBerth
open Filter Function Set Lattice RG Wilson Source Extraction Table Next.UVStress
open MeasureTheory Marker Extraction.Order Spec Next.Rank RG17 FullVolume Climb Trace.Pilot
open WilsonInvariantActionPosition PhysicalNext.Repeat.Legato RG05Readout.Address WilsonReflectedOriginalPrefixTariff
open WilsonInvariantActionSeparatedCells
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "A₀" => R.family.path.levels
local notation "H₀" => (A₀).clock.hatBeta
local notation "mesh" => R.family.S.a

/-- The floor and constants are chosen prior to the physical cutoffs.  Both
microscopic sites may have arbitrary residues over the selected flat. -/
theorem original (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (φ:Test 2){Q:Set (Points 2)}(compact:IsCompact Q)(separated:Q⊆conf 2)(support:tsupport φ⊆Q)
    (c:ℝ)(cp:0 ≤ c):
    ∃ first : ℕ, ∀ᶠ t in trail, ∀ (ht : 0 < t) (m : ℕ), first  ≤  m → mesh m  ≤  t →
      let f:=berth R 5 m
      m<f ∧ (H₀ m)^5 ≤ mesh m/mesh f ∧ mesh m/mesh f ≤ (H₀ m)^5*(H₀ m)^(1:ℝ) ∧
      ∀N per (live:f ≤ N) (x:Fin 2→Site (R.family.side N per)),
        WilsonExternalMeshMass.charge R.family (dilate ht φ) x≠0 →
        c*(1+(((A₀).budget f).B:ℝ))^2 ≤ (gap R.family live x:ℝ):=by
  obtain ⟨l,u,lp,_,physical⟩:=filed R.family φ compact separated support
  obtain ⟨M,F,mp,_fp,actual⟩:=WilsonReflectedOpticalWidth.original R simple slow 0 5 (η:=1) zero_lt_one
  have date:=WilsonAddressedCollarWindow.original R simple slow 5 (η:=1) zero_lt_one
  let bill:=c*(M^2+2)^2
  have future:=((Next.Rank.Station.hat_rate (A₀) simple).eventually_ge_atTop ((bill+1)/l))
  obtain ⟨floor,paid⟩:=eventually_atTop.mp (actual.and (date.and future))
  refine ⟨floor,?_⟩
  filter_upwards [physical] with t draws
  intro ht m late scale f
  obtain ⟨metric,scales,room⟩:=paid m late
  refine ⟨scales.1,scales.2.1,scales.2.2,?_⟩
  intro N per live x owns
  obtain ⟨near,_⟩:=draws ht f N per live x owns
  have atM:1 ≤ H₀ m:=((A₀).fits.delayed m).le
  have atF:1 ≤ H₀ f:=((A₀).fits.delayed f).le
  have mp':0 ≤ M:=mp.le
  have logF:=Real.log_nonneg atF
  have logBound:Real.log (H₀ f) ≤ M*H₀ m:=by
    refine le_trans ?_ metric.1
    unfold width
    linarith only [abs_nonneg G.slopeConstant]
  have defB:((A₀).budget f).B=⌈(Real.log (H₀ f))^2⌉₊:=rfl
  have side:(((A₀).budget f).B:ℝ) ≤ (M*H₀ m)^2+1:=by
    rw [defB]
    exact (Nat.ceil_lt_add_one (sq_nonneg _)).le.trans (add_le_add_left (pow_le_pow_left₀ logF logBound 2) 1)
  have hs:1 ≤ (H₀ m)^2:=one_le_pow₀ atM
  have compactR:1+(((A₀).budget f).B:ℝ) ≤ (M^2+2)*(H₀ m)^2:=by nlinarith only [side,hs]
  have localPay:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) compactR 2) cp
  have collect:c*(1+(((A₀).budget f).B:ℝ))^2 ≤ bill*(H₀ m)^4:=by
    exact localPay.trans_eq (by dsimp only [bill];ring)
  have fact:bill+1 ≤ l*(H₀ m):=by simpa only [mul_comm] using (div_le_iff₀ lp).mp room
  have head:bill*(H₀ m)^4+1 ≤ l*(H₀ m)^5:=by
    have w:=mul_le_mul_of_nonneg_right fact (pow_nonneg (zero_le_one.trans atM) 4)
    nlinarith only [w,one_le_pow₀ (n:=4) atM]
  have mr:mesh m/mesh f ≤ t/mesh f:=div_le_div_of_nonneg_right scale (R.family.S.a_pos f).le
  have data:l*(H₀ m)^5 ≤ (gap R.family live x:ℝ)+1:=by
    apply (mul_le_mul_of_nonneg_left (scales.2.1.trans mr) lp.le).trans
    simpa only [mul_div_assoc] using near
  linarith only [collect,head,data]

end YM.Integration.WilsonReflectedPublicFlatBerth
end
