import YM.Integration.WilsonAddressedPublicWilsonClock
import YM.Integration.WilsonReflectedOpticalStock
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicPrintingDate
open Function Filter Set MeasureTheory Finset Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame Cells
open GapsContact GapsContact.Seams GapsContact.Stamps PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open WilsonMeasuredPublicSlots WilsonMeasuredPublicClearance 
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)}
    {z:Trace.Terrace.Arch R.family} {H:(Bel R.family.book).Hierarchy}


open RG05Readout.Address RG05Readout.Planes WilsonLimitConstruction Next.Rank RG05Readout
local notation "A₀" => R.family.path.levels
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta


open WilsonInvariantActionPosition WilsonMeasuredPublicClearance
open WilsonThermometerUnitFilingFourPoolClock
local notation "depth_" T:max => deep T
local notation "shell" => WilsonThermometerUnitFilingFourPoolShell.radius
def span (T:ℕ):ℕ:=1+2*(deep T)+(2*(deep T)+4)

theorem tends (simple:G.Simple)(v:ℕ)(vp:0<v)(u:ℕ):
    Tendsto (fun r=>berth R u (WilsonMeasuredWindow.stop A₀ simple v r)) trail atTop:=
  tendsto_atTop_mono (fun r=>(arrival R u (WilsonMeasuredWindow.stop A₀ simple v r)).1.le)
    (WilsonMeasuredWindow.stop_tendsto A₀ simple v vp)

/-- The genuine receipt at each reported field fits between the prescribed
    finite-grade floor and a common optical grid chosen before the cutoff. -/
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F l z H)
    (v T gate D:ℕ)(vp:0<v){clear:ℝ}(room:0<clear):
    ∀ᶠ r:ℝ in trail,
    let m:=WilsonMeasuredWindow.stop A₀ simple v r
    let f:=berth R (span T) m
    clear*r/a_ f ≤ (H_ f)^(span T+2) ∧
    ∀n (board:Book F l (z:=z) D T n clear r) (d:Fin (D+1)) (x:S.Field d.val),
      let L:=(board.bank.department d.val (Nat.le_of_lt_succ d.isLt)).print x
      gate ≤ L.j ∧ L.j ≤ f:=by
  let U:=deep T
  let power:=2*U+4
  obtain ⟨C,hC,purse⟩:=WilsonThermometerUnitFilingFourPoolClock.invoice F simple bliss U
  have dates:=WilsonMeasuredWindow.stop_tendsto A₀ simple v vp
  have time:=Station.hat_rate A₀ simple
  have small:=gt_mem_nhds (div_pos (R.family.S.a_pos gate) room)
  filter_upwards [WilsonAddressedPublicWilsonClock.original F simple slow bliss v vp,
    WilsonAddressedPublicGuardClock.physical R simple slow v (span T) vp (by norm_num:0<(1/2:ℝ)),
    dates.eventually (WilsonAddressedCollarWindow.original R simple slow (span T) (by norm_num:0<(1/2:ℝ))),
    dates.eventually (time.eventually_ge_atTop C),dates.eventually (time.eventually_ge_atTop clear),
    purse,small.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r fee rad inside large enough bought tiny rp
  let m:=WilsonMeasuredWindow.stop A₀ simple v r
  let f:=berth R (span T) m
  let g:=wilson z r
  let Q:=H_ m
  let ξ:=shell z U r
  have rp':0<r:=rp
  have gp:0<g:=fee.1
  have Hp:0<Q:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have full:0<H_ f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  change (clear*r/a_ f  ≤  (H_ f)^(span T+2)) ∧ _
  constructor
  · have fk:m ≤ f:=inside.1.le
    have ch:clear ≤ H_ f:=enough.trans (WilsonReflectedOpticalStock.monotone R simple fk)
    have dim:(span T:ℝ)+2*(1/2:ℝ)=((span T+1:ℕ):ℝ):=by push_cast;ring
    have bound:r/a_ f ≤ (H_ f)^(span T+1):=by simpa only [dim,Real.rpow_natCast] using rad
    calc
      _ = clear*(r/a_ f):=by ring
      _  ≤  (H_ f)*(H_ f)^(span T+1):=mul_le_mul ch bound (div_nonneg rp'.le (R.family.S.a_pos f).le) full.le
      _ = _:=by rw [pow_succ (H_ f) (span T+1)];ring
  · intro n board d x
    let L:=(board.bank.department d.val (Nat.le_of_lt_succ d.isLt)).print x
    have aj:=R.family.S.a_pos L.j
    have af:=R.family.S.a_pos f
    have stock:0<dock ξ:=bought.1
    have upper:dock ξ^T*g^(2*U) ≤ C:=
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ board.wallet (by dsimp [U,deep];omega : T ≤ U))
        (pow_nonneg gp.le _)).trans bought.2
    have factor:dock ξ^T ≤ C*g⁻¹^(2*U):=by
      rw [inv_pow,←div_eq_mul_inv]
      exact (le_div_iff₀ (pow_pos gp _)).mpr upper
    have source:r*g^power  ≤  dock ξ^T*a_ L.j:=L.breadth.le
    have collar:r/a_ L.j ≤ dock ξ^T*g⁻¹^power:=by
      have divided:=mul_le_mul_of_nonneg_right source (pow_nonneg (inv_pos.mpr gp).le power)
      rw [inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ gp.ne'),mul_one] at divided
      apply (div_le_iff₀ aj).2
      simpa only [inv_pow,mul_assoc,mul_comm,mul_left_comm] using divided
    have earned:r/a_ L.j ≤ Q^(span T):=calc
      r/a_ L.j  ≤  dock ξ^T*g⁻¹^power:=collar
      _  ≤  (C*g⁻¹^(2*U))*g⁻¹^power:=mul_le_mul_of_nonneg_right factor (pow_nonneg (inv_pos.mpr gp).le _)
      _  ≤  (Q*Q^(2*U))*Q^power:=mul_le_mul
        (mul_le_mul large (pow_le_pow_left₀ (inv_pos.mpr gp).le fee.2.2.2 _) (pow_nonneg (inv_pos.mpr gp).le _) Hp.le)
        (pow_le_pow_left₀ (inv_pos.mpr gp).le fee.2.2.2 _) (pow_nonneg (inv_pos.mpr gp).le _)
        (mul_nonneg Hp.le (pow_nonneg Hp.le _))
      _ = _:=by
        change Q*Q^(2*U)*Q^power=Q^((1+2*U)+power)
        rw [pow_add Q (1+2*U) power,pow_add Q 1 (2*U),pow_one]
    have settled:r/a_ L.j ≤ r/a_ f:= (earned.trans inside.2.1).trans
      (div_le_div_of_nonneg_right fee.2.2.1 af.le)
    have seat:a_ f ≤ a_ L.j:=by by_contra! gone;exact (not_lt_of_ge settled) (div_lt_div_of_pos_left rp' aj gone)
    have housed:=WilsonAddressedPublicOpticalFare.housed R F l board d x
    have first:clear*r<a_ gate:=by simpa only [mul_comm] using (lt_div_iff₀ room).mp tiny
    constructor
    · by_contra! gone;exact (not_lt_of_ge ((R.family.S.strictAnti gone).le)) (housed.trans_lt first)
    · by_contra! gone;exact (not_lt_of_ge seat) (R.family.S.strictAnti gone)

end YM.Integration.WilsonAddressedPublicPrintingDate
end
