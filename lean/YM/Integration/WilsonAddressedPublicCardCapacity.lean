import YM.Integration.WilsonAddressedPublicHomeCard

/-! The original reflected-card price on the entire measured reporting space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonAddressedPublicCardCapacity
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonThermometerUnitFilingFourPoolShell (radius smaller)
open WilsonMatrixOriginalDeckCapacity (capacity)
open WilsonAddressedPublicHomeCard (exponent)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee)
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G){l:Ultrafilter (ℕ×ℕ)}
    {z:Trace.Terrace.Arch R.family}{H:(Bel R.family.book).Hierarchy}

include Z in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F J)(T d:ℕ):
    ∃A:ℝ,0 ≤ A ∧ ∀ᶠ r in trail,∀{D:ℕ}(hd:d ≤ D)(B:Book F (l:=l) H z D T r),Housed F B →
    ∀(v:S.Field d)(br:Bool),fee F B ⟨d,by omega⟩ v br*(wilson z r)^(exponent T d) ≤ A*‖(J r d).symm v‖:=by
  let g:=wilson z
  let k:=2*T+4
  let E:=2*T+k*(d+1)
  obtain ⟨C,cp,own⟩:=WilsonThermometerUnitFilingFourPoolRent.primary F J Z lead d
  obtain ⟨K,kp,relative⟩:=WilsonMatrixOriginalDeckCapacity.original F d J lead
  obtain ⟨B₀,bp,clock⟩:=WilsonThermometerUnitFilingFourPoolClock.invoice F simple bliss T
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨B₁,b₁p,logFee⟩:=WilsonThermometerWeakPairNumeric.tariff simple g link 2
  let A:=max (B₀*C*K) (B₁*C)
  have kn:0 ≤ K:=zero_le_one.trans kp
  have bn:0 ≤ B₀:=zero_le_one.trans bp
  refine ⟨A,(mul_nonneg (mul_nonneg bn cp) kn).trans (le_max_left ..),?_⟩
  filter_upwards [own,(smaller F simple bliss T).eventually own,relative 1 one_pos,clock,logFee,link.positive,
    (link.conforms simple).eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin,
    (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r ownHere ownThere move paid logs gp gu rp ru
  have pos:0<r:=rp
  have chip:0 ≤ dock r:=by unfold dock LogV;rw [Real.log_inv];linarith [Real.log_nonpos pos.le ru]
  have hp:0 < g r:=gp
  have wider {m e:ℕ}(h:m ≤ e):g r^e ≤ g r^m:=pow_le_pow_of_le_one hp.le gu h
  intro D hd B housed v br
  let x:=‖(J r d).symm v‖
  have xn:0 ≤ x:=norm_nonneg _
  cases br
  · let a:=(g r)^k
    let s:=radius z T r
    let p:=dock s^T
    have ap:0 < a:=pow_pos hp k
    have thin:a ≤ 1:=pow_le_one₀ hp.le gu
    have sr:s=a*r:=mul_comm ..
    have pn:0 ≤ p:=pow_nonneg paid.1.le _
    have die:a^(-(d:ℝ)-1)*(g r)^(k*(d+1))=1:=by
      rw [show -(d:ℝ)-1= -((d+1:ℕ):ℝ) by push_cast;ring,Real.rpow_neg ap.le,Real.rpow_natCast,pow_mul]
      exact inv_mul_cancel₀ (pow_pos ap _).ne'
    have transfer:=((move a ⟨ap,thin⟩ v).1)
    rw [←sr] at transfer
    have actual:Ascent.cost F d s v ≤ C*(K*a^(-(d:ℝ)-1)*x):=(ownThere v).trans (mul_le_mul_of_nonneg_left transfer cp)
    have due:Ascent.cost F d s v*(g r)^(k*(d+1)) ≤ C*K*x:=by
      calc
        _ ≤ (C*(K*a^(-(d:ℝ)-1)*x))*(g r)^(k*(d+1)):=mul_le_mul_of_nonneg_right actual (pow_nonneg hp.le _)
        _ = C*K*x*(a^(-(d:ℝ)-1)*(g r)^(k*(d+1))):=by ring
        _ = C*K*x:=by rw [die,mul_one]
    change (p*Ascent.cost F d s v)*(g r)^(exponent T d) ≤ A*x
    calc
      _ ≤ (p*Ascent.cost F d s v)*(g r)^E:=mul_le_mul_of_nonneg_left
        (wider (le_max_right 4 E)) (mul_nonneg pn (Ascent.cost_pos ..))
      _ = (p*(g r)^(2*T))*(Ascent.cost F d s v*(g r)^(k*(d+1))):=by rw [show E=2*T+k*(d+1) by rfl,pow_add];ring
      _ ≤ B₀*(C*K*x):=mul_le_mul paid.2 due (mul_nonneg (Ascent.cost_pos ..) (pow_nonneg hp.le _)) bn
      _ ≤ A*x:=by rw [←mul_assoc,←mul_assoc];exact mul_le_mul_of_nonneg_right (le_max_left ..) xn
  · have card:=WilsonAddressedPublicSelfCards.weak F B ⟨d,by omega⟩ v housed.1 chip
    have logPay:dock r^2*g r^4 ≤ B₁:=(le_div_iff₀ (pow_pos hp 4)).mp logs
    apply (mul_le_mul_of_nonneg_right card (pow_nonneg hp.le _)).trans
    calc
      _ ≤ (dock r^2*Ascent.cost F d r v)*g r^4:=mul_le_mul_of_nonneg_left (wider (le_max_left 4 _))
        (mul_nonneg (sq_nonneg _) (Ascent.cost_pos ..))
      _ = (dock r^2*g r^4)*Ascent.cost F d r v:=by ring
      _ ≤ B₁*(C*x):=mul_le_mul logPay (ownHere v) (Ascent.cost_pos ..) b₁p.le
      _ ≤ A*x:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (le_max_right ..) xn

end YM.Integration.WilsonAddressedPublicCardCapacity
end
