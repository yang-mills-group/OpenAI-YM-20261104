import YM.Integration.WilsonAddressedPublicCardBooks
import YM.Integration.WilsonAddressedPublicSelfCards
import YM.Integration.WilsonThermometerWeakPairNumeric
import YM.Integration.WilsonThermometerUnitFilingFourPoolBill

/-! The before-cutoff reflected card of a named homogeneous physical field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicHomeCard
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame
open WilsonThermometerUnitFilingFourPoolShell (radius)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee)
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G){l:Ultrafilter (ℕ×ℕ)}
    {z:Trace.Terrace.Arch R.family}{H:(Bel R.family.book).Hierarchy}

def exponent (T d:ℕ):ℕ:=max 4 (WilsonThermometerUnitFilingFourPoolBill.exponent T 0 d)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (T d:ℕ)(x:RG17.Free R.family d):
    ∃A:ℝ,0 ≤ A ∧ ∀ᶠ r in trail,∀{D:ℕ}(hd:d ≤ D)(B:Book F (l:=l) H z D T r),Housed F B →
    ∀br:Bool,fee F B ⟨d,by omega⟩ (homogeneous F J Z r d x) br*(wilson z r)^(exponent T d) ≤ A:=by
  let g:=wilson z
  let E:=WilsonThermometerUnitFilingFourPoolBill.exponent T 0 d
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨A₀,A₀p,pooled⟩:=WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead paid T 0 d x
  obtain ⟨A₁,A₁p,home⟩:=WilsonThermometerUnitFilingFourPoolRent.converted F J Z simple lead paid d x
    (u:=id) («a»:=fun _=>1) tendsto_id (by simpa only [one_mul] using! tendsto_id)
    (Eventually.of_forall (fun _=>⟨one_pos,le_rfl⟩))
  obtain ⟨D₁,D₁p,dockPay⟩:=WilsonThermometerWeakPairNumeric.tariff simple g link 2
  refine ⟨max A₀ (D₁*A₁),A₀p.trans (le_max_left ..),?_⟩
  filter_upwards [pooled,home 1 one_pos,dockPay,link.positive,
    (link.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r prior own logPay gp small rle rp
  intro D hd B housed br
  let val:=homogeneous F J Z r d x
  have gd:0≤g r:=gp.le
  have rpos:0<r:=rp
  have chip:0 ≤ dock r:=by unfold dock LogV;rw [Real.log_inv];have h:=Real.log_nonpos rpos.le rle; linarith
  have wider {m e:ℕ}(h:m ≤ e):g r^e ≤ g r^m:=pow_le_pow_of_le_one gd small h
  cases br
  · change (dock (radius z T r)^T*Ascent.cost F d (radius z T r) val)*(g r)^(exponent T d) ≤ _
    have prior':(dock (radius z T r)^T*Ascent.cost F d (radius z T r) val)*(g r)^E ≤ A₀:=by
      simpa only [WilsonThermometerUnitFilingFourPoolClock.outer,pow_zero,mul_one] using prior
    have sr:radius z T r ≤ 1:=by
      unfold radius
      exact (mul_le_mul_of_nonneg_right rle (pow_nonneg gd _)).trans (by
        rw [one_mul];exact pow_le_one₀ gd small)
    have sp:0 ≤ dock (radius z T r):=by
      have srp:0 ≤ radius z T r:=mul_nonneg rpos.le (pow_nonneg gd _)
      unfold dock LogV;rw [Real.log_inv];have h:=Real.log_nonpos srp sr;linarith
    exact ((mul_le_mul_of_nonneg_left (wider (le_max_right 4 E))
      (mul_nonneg (pow_nonneg sp _) (Ascent.cost_pos ..))).trans prior').trans (le_max_left ..)
  · have raw:=WilsonAddressedPublicSelfCards.weak F B ⟨d,by omega⟩ val housed.1 chip
    have c:Ascent.cost F d r val ≤ A₁:=by simpa only [id_eq,one_mul,Real.one_rpow,mul_one] using own
    have bank:dock r^2*g r^4 ≤ D₁:=(le_div_iff₀ (pow_pos gp 4)).mp logPay
    have ae:=mul_le_mul_of_nonneg_right raw (pow_nonneg gd (exponent T d))
    apply ae.trans
    calc
      _ ≤ (dock r^2*Ascent.cost F d r val)*g r^4:=mul_le_mul_of_nonneg_left
        (wider (le_max_left 4 E)) (mul_nonneg (sq_nonneg _) (Ascent.cost_pos ..))
      _ = (dock r^2*g r^4)*Ascent.cost F d r val:=by ring
      _ ≤ D₁*A₁:=mul_le_mul bank c (Ascent.cost_pos ..) D₁p.le
      _ ≤ _:=le_max_right .. 

end YM.Integration.WilsonAddressedPublicHomeCard
end
