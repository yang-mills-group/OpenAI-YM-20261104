import YM.Integration.WilsonMeasuredPublicEntranceCardDetector
import YM.Integration.WilsonAddressedPublicHomeWidth
import YM.Integration.WilsonAddressedReportingScale
import YM.Integration.WilsonThermometerUnitFilingFourPoolClock
import YM.GapsContact.Slab.Dyadic

/-! Pay the spectral norm of the very weak field in the commissioned book using
its physical card on the two time detectors, before choosing a Taylor order. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
namespace YM.Integration.WilsonMeasuredPublicEntranceWeakTestCost
open Function Filter Finset Set Lattice Wilson RG Source Cells Extraction Spec Table Climb GapsContact
open Trace.Pilot Trace.Terrace GapsContact.Seams
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (width fee)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
local notation "g" => wilson z
local notation "a" => R.family.S.a

def slot {e:ℕ}(marked:Bool)(v:S.Field e):S.Field e:=if marked then S.adj F.room.kernel.spin e timeAxis v else v

private theorem geometry {r γ wall M:ℝ}(rp:0<r)(gp:0<γ)(g1:γ≤1)(bill:wall*γ^2≤r*M)
    (deep:2*M*γ^2<1):r≤r*γ⁻¹^4 ∧ 2*wall<r*γ⁻¹^4:=by
  simp only [inv_pow,←div_eq_mul_inv]
  have p4:0<γ^4:=pow_pos gp _
  constructor
  · apply (le_div_iff₀ p4).mpr
    exact mul_le_of_le_one_right rp.le (pow_le_one₀ gp.le g1)
  · apply (lt_div_iff₀ p4).mpr
    calc
      2*wall*γ^4=(wall*γ^2)*(2*γ^2):=by ring
      _≤(r*M)*(2*γ^2):=mul_le_mul_of_nonneg_right bill (by positivity)
      _=r*(2*M*γ^2):=by ring
      _<r:=by simpa using mul_lt_mul_of_pos_left deep rp

theorem tariff (simple:G.Simple)(bliss:Bliss F l z H)(cash:PostT R.family.path.levels)
    (slow:WilsonWindowReportingPace.Slow R.kit)(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    {D:ℕ}(T:ℕ)(d:Fin (D+1)):
    ∃h:ℕ,∃A:ℝ,0≤A ∧ ∀ᶠ r in trail,∀B:Book F (l:=l) H z D T r,Housed F B →
      ∀v:S.Field d.val,∀b marked:Bool,0≤fee F B d v b →
      Ascent.cost F d.val r (slot F marked v)*(g r)^h ≤ A*fee F B d v b:=by
  obtain ⟨roof,A,m,roofpos,apos,bill⟩:=Ascent.bills F simple bliss d.val
  obtain ⟨M,_,widths⟩:=WilsonAddressedPublicHomeWidth.original F simple bliss cash slow T (p:=1) one_pos
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have close:Tendsto (fun r=>2*M*(g r)^2) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=2*M)).mul ((link.conforms simple).pow 2)
  have goes:Tendsto (outer z 4) trail (𝓝 0):=tendsto_nhdsWithin_iff.mp (longer F simple bliss 4) |>.1
  refine ⟨4*m,A,zero_le_one.trans apos,?_⟩
  filter_upwards [widths,link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    close.eventually_lt_const zero_lt_one,goes.eventually_lt_const (lt_min zero_lt_one roofpos),self_mem_nhdsWithin]
    with r rooms gp g1 deep short (rp:0<r)
  intro B housed v b marked fn
  have w:=rooms B housed d v b
  have geom:=geometry rp gp g1 (by simpa only [Real.rpow_one] using w.2) deep
  let τ:=outer z 4 r
  have tp:0<τ:=lt_of_lt_of_le rp geom.1
  have paid:Ascent.cost F d.val τ (slot F marked v)≤fee F B d v b:=by
    cases marked
    · exact WilsonMeasuredPublicEntranceCardDetector.original R F B d v b cash below w.1 tp
        (short.trans_le (min_le_left ..)) geom.2 fn
    · exact WilsonMeasuredPublicEntranceCardDetector.reflected R F B d v b cash below w.1 tp
        (short.trans_le (min_le_left ..)) geom.2 fn
  have recover:=bill.all r τ ⟨tp,(short.trans_le (min_le_right ..)).le⟩ ⟨rp,geom.1⟩ (slot F marked v)
  have ratio:τ/r=(g r)⁻¹^4:=by dsimp [τ,outer];field_simp [rp.ne']
  calc
    _≤ (A*(τ/r)^m*fee F B d v b)*(g r)^(4*m):=mul_le_mul_of_nonneg_right
      (recover.trans (mul_le_mul_of_nonneg_left paid (mul_nonneg (zero_le_one.trans apos) (by positivity)))) (pow_nonneg gp.le _)
    _=A*fee F B d v b:=by rw [ratio,pow_mul,inv_pow,inv_pow];field_simp [gp.ne']

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(cash:PostT R.family.path.levels)
    (slow:WilsonWindowReportingPace.Slow R.kit)(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    {D:ℕ}(T:ℕ)(d:Fin (D+1)):
    ∃h:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀B:Book F (l:=l) H z D T r,Housed F B →
      ∀y:(Bel R.family.book).Field d.val,∀marked:Bool,
      Ascent.cost F d.val r (slot F marked ((B.V d) y))*(g r)^h ≤ C*‖y‖:=by
  obtain ⟨h,A,an,sold⟩:=tariff F simple bliss cash slow below T d
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨lo,hi,_,hip,coin⟩:=WilsonAddressedReportingScale.currency simple g link
  refine ⟨h+2,A*hi,mul_nonneg an (zero_le_one.trans hip),?_⟩
  filter_upwards [sold,coin,self_mem_nhdsWithin,(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r sale rate (rp:0<r) (r1:r≤1)
  intro B housed y marked
  have d0:0≤dock r:=zero_le_one.trans (dock_valid r ⟨rp,r1⟩)
  have exactFee:fee F B d ((B.V d) y) true=dock r*‖y‖:=by simp [fee]
  have earn:=sale B housed ((B.V d) y) true marked ((mul_nonneg d0 (norm_nonneg _)).trans_eq exactFee.symm)
  rw [exactFee] at earn
  calc
    _ = (Ascent.cost F d.val r (slot F marked ((B.V d) y))*(g r)^h)*(g r)^2:=by rw [pow_add];ring
    _ ≤ (A*(dock r*‖y‖))*(g r)^2:=mul_le_mul_of_nonneg_right earn (sq_nonneg _)
    _ = A*(dock r*(g r)^2)*‖y‖:=by ring
    _ ≤ A*hi*‖y‖:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left rate.2.2.2 an) (norm_nonneg _)

end YM.Integration.WilsonMeasuredPublicEntranceWeakTestCost
end
