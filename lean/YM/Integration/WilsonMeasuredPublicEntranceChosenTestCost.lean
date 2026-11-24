import YM.Integration.WilsonMeasuredPublicEntranceWeakTestCost
import YM.Integration.WilsonAddressedPublicCardCapacity
import YM.Integration.WilsonMacroscopicRichTwoDatePivot
import YM.Integration.WilsonOriginalTwoFlatPublicNamedFare

/-! The finite original weak and pooled names, including the reflected copy,
have a common physical size exponent on their own previously booked scale. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonMeasuredPublicEntranceChosenTestCost
open Function Filter Finset Set Lattice RG Wilson Source Cells Extraction Spec Table Climb GapsContact
open PhysicalNext.Repeat.Legato Trace.Terrace Trace.Pilot RG17 PhysMS
open FVA2 FVA2.Register MS MS.Land
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonAddressedPublicSelfCards (fee)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonMeasuredPublicEntranceWeakTestCost (slot)
open WilsonAddressedPublicHomeCard (exponent)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Arch R.family}
    (J:ℝ→tower S)(Z:WilsonPrescription G)
local notation "g" => wilson z

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(cash:PostT R.family.path.levels)
    (slow:WilsonWindowReportingPace.Slow R.kit)(below:(l:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d){D:ℕ}(T:ℕ)(d:Fin (D+1)):
    ∃h:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠr in trail,∀B:Book F (l:=l) H z D T r,Housed F B →
      ∀y:(Bel R.family.book).Field d.val,∀x:Free R.family d.val,∀b marked:Bool,
      Ascent.cost F d.val r (slot F marked (chosen F J Z r (B.V d) b y x))*(g r)^h≤C*(‖x‖+‖y‖):=by
  obtain ⟨hw,A,an,weak⟩:=WilsonMeasuredPublicEntranceWeakTestCost.original F simple bliss cash slow below T d
  obtain ⟨hc,C,cn,card⟩:=WilsonMeasuredPublicEntranceWeakTestCost.tariff F simple bliss cash slow below T d
  obtain ⟨D₀,dn,gross⟩:=WilsonAddressedPublicCardCapacity.original F J Z simple bliss lead T d.val
  obtain ⟨E,en,coin⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple d.val
  let γ:=exponent T d.val
  let h:=max hw (hc+γ)
  let A₀:=C*D₀*E
  have pos:0≤A₀:=mul_nonneg (mul_nonneg cn dn) en
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  refine ⟨h,max A A₀,an.trans (le_max_left ..),?_⟩
  filter_upwards [weak,card,gross,coin,link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one)]
    with r wk buy funds actual gp g1
  intro B house y x b marked
  cases b
  · let v:=homogeneous F J Z r d.val x
    obtain ⟨w,cardAt⟩:=
      (WilsonAddressedPublicSelfCards.original F B d v false).exists
    have a:=buy B house v false marked cardAt.cost
    have b:=funds (Nat.le_of_lt_succ d.isLt) B house v false
    have fit:‖(J r d.val).symm v‖≤E*‖x‖:=actual x
    change Ascent.cost F d.val r (slot F marked v)*(g r)^h≤_
    calc
      _ ≤ Ascent.cost F d.val r (slot F marked v)*(g r)^(hc+γ):=mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one gp.le g1 (le_max_right ..)) (Ascent.cost_pos ..)
      _ = (Ascent.cost F d.val r (slot F marked v)*(g r)^hc)*(g r)^γ:=by rw [pow_add];ring
      _ ≤ (C*fee F B d v false)*(g r)^γ:=mul_le_mul_of_nonneg_right a (pow_nonneg gp.le _)
      _ = C*(fee F B d v false*(g r)^γ):=by ring
      _ ≤ C*(D₀*(E*‖x‖)):=mul_le_mul_of_nonneg_left (b.trans (mul_le_mul_of_nonneg_left fit dn)) cn
      _ = A₀*‖x‖:=by dsimp [A₀];ring
      _ ≤ max A A₀*(‖x‖+‖y‖):=mul_le_mul (le_max_right ..) (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _) (pos.trans (le_max_right ..))
  · change Ascent.cost F d.val r (slot F marked ((B.V d) y))*(g r)^h≤_
    exact ((mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le g1 (le_max_left hw (hc+γ))) (Ascent.cost_pos ..)).trans
      (wk B house y marked)).trans (mul_le_mul (le_max_left ..) (le_add_of_nonneg_left (norm_nonneg _)) (norm_nonneg _) (an.trans (le_max_left ..)))

end YM.Integration.WilsonMeasuredPublicEntranceChosenTestCost
end
