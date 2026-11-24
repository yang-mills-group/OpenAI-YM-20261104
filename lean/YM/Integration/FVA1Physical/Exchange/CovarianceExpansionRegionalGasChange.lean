import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRegionalRosterBudget
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRosterLogWindow

/-! Regional thermodynamic falloff on a single edited physical bond. The true
signed region may be chosen using both configurations. No lower bound on
the full original gas appears in the price. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Finset Set Lattice RG Wilson Push.AbsoluteSums Push.GridApprox.Attach
open Marked Marked.RemoteRoster RoseCut
open YM.Integration.FVA1Physical.Round2.Curvature.Tariff.Native
open private regional_sum from YM.Integration.FVA1Physical.CommonHull.InteractingScalarOwnerComponent
open private positive_log_price from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRosterLogWindow
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

private theorem empty_terms (A:Activities G n)(s:Finset ℕ)(U V:Fld):
    regionalTerm A ∅ s U=regionalTerm A ∅ s V:=by
  unfold regionalTerm;split
  · rename_i reg
    have empty:s=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr;intro i hi
      obtain ⟨z,hz⟩:=(A.forced i).inventory_ne
      have atSite:z∈s.biUnion (fun l=>(A.forced l).inventory):=mem_biUnion.mpr ⟨i,hi,hz⟩
      exact Finset.notMem_empty z (reg.2 ▸ atSite)
    rw [empty]
    simp
  rfl

private theorem changed_terms (A:Activities G n){p:BudgetPoint}{w:ℝ}(law:A.ForcedFamily p)
    (paid:A.KBound p w)(small:w≤1)(e:Edge (Site n))(r:ℕ)(D:Support n)(U V:Fld)
    (off:ActualGas.sameOffBond e U V)(same:flags p.threshold U=flags p.threshold V)
    (cold:Healthy p.threshold (halo (r*leg p.B) {e.1}) U):
    SumBudget (fun s=>‖regionalTerm A D s U-regionalTerm A D s V‖)
      (Real.exp (-p.supportExponent*r)*(w+w)):=by
  by_cases quiet:D=∅
  · subst D
    obtain ⟨_,_,site⟩:=paid
    have wn:=budget_nonneg (site e.1)
    have zero(s:Finset ℕ):‖regionalTerm A ∅ s U-regionalTerm A ∅ s V‖=0:=by rw [empty_terms A s U V,sub_self,norm_zero]
    simp only [zero]
    exact ⟨fun _=>le_rfl,summable_zero,by rw [tsum_zero];exact mul_nonneg (Real.exp_pos _).le (add_nonneg wn wn)⟩
  have u:=regional_roster_wallet A small paid D (fun _=>U)
  have v:=regional_roster_wallet A small paid D (fun _=>V)
  simp only [if_neg quiet] at u v
  have paidAll:=budget_scale (Real.exp_pos (-p.supportExponent*r)).le (budget_plus u v)
  apply budget_mono paidAll (fun _=>norm_nonneg _);intro s
  by_cases eqn:regionalTerm A D s U=regionalTerm A D s V
  · calc _ = 0 := by rw [eqn,sub_self,norm_zero]
           _ ≤ _ := paidAll.1 s
  have someMove:∃ i∈s,A.K i U ≠ A.K i V:=by
    by_contra! all;apply eqn
    unfold regionalTerm;split
    · exact prod_congr rfl all
    rfl
  obtain ⟨i,hi,moves⟩:=someMove
  have reaches:=ActualGas.changed_forced_cover A e U V law off same r cold i moves
  let size:ℝ:=∑ j∈s,(coverNumber p.B (A.forced j).support:ℝ)
  have span:(r:ℝ)≤size:=(Nat.cast_le.mpr reaches).trans
    (single_le_sum (fun j _=>Nat.cast_nonneg (coverNumber p.B (A.forced j).support)) hi)
  have w_eq:rosterWeight A p s=Real.exp (p.supportExponent*size):=by
    unfold rosterWeight size;rw [Finset.mul_sum,Real.exp_sum]
  have reserve:1 ≤ Real.exp (-p.supportExponent*r)*rosterWeight A p s:=by
    rw [w_eq,←Real.exp_add,Real.one_le_exp_iff];nlinarith only [mul_le_mul_of_nonneg_left span p.exponent_pos.le]
  calc
    _ ≤ ‖regionalTerm A D s U‖+‖regionalTerm A D s V‖:=norm_sub_le .. 
    _ ≤ (Real.exp (-p.supportExponent*r)*rosterWeight A p s)*(‖regionalTerm A D s U‖+‖regionalTerm A D s V‖):=
      le_mul_of_one_le_left (add_nonneg (norm_nonneg _) (norm_nonneg _)) reserve
    _ = _:=by ring

/-- Any subregion of the physical torus has exponentially small signed gas
variation under this actual one-bond edit. Compulsory flags off the region
cost nothing, including when their full partition is tiny. -/
theorem signed_regional_bond_price (A:Activities G n){p:BudgetPoint}{δ w:ℝ}(valid:A.Valid p δ w)
    (small:w≤1)(e:Edge (Site n))(r:ℕ)(U V:Fld)(off:ActualGas.sameOffBond e U V)
    (cold:Healthy p.threshold (halo (r*leg p.B) {e.1}) U)(after:e.1∉flags p.threshold V)(F:Support n):
    ‖scalarParcel A p U F ∅-scalarParcel A p V F ∅‖ ≤ 2*w*Real.exp (-p.supportExponent*r):=by
  have before:e.1∉flags p.threshold U:=disjoint_left.mp cold (halo_subset _ _ (mem_singleton_self _))
  have same:=ActualGas.flags_at_bond e U V off before after
  let D:=flags p.threshold U∩F
  let C:Set (Finset ℕ):={s | ∀i∈s,lies A F i}
  have fixed:D=flags p.threshold V∩F:=by dsimp only [D];rw [same]
  let f:=fun s:Finset ℕ=>‖regionalTerm A D s U-regionalTerm A D s V‖
  have price:SumBudget f (Real.exp (-p.supportExponent*r)*(w+w)):=changed_terms A valid.forced valid.boundK small e r D U V off same cold
  have sumU:=regional_sum A p U valid D ∅ (lies A F)
  have sumV:=regional_sum A p V valid D ∅ (lies A F)
  have term(W:Fld)(s:Finset ℕ):regionPartners A W D ∅ s=regionalTerm A D s W:=by simp only [regionPartners,regionalTerm,Finset.disjoint_empty_left,Finset.empty_union,true_and]
  change ‖(∑' s:Pool (lies A F),regionPartners A U D ∅ s.val)-(∑' s:Pool (lies A F),regionPartners A V (flags p.threshold V∩F) ∅ s.val)‖≤_
  rw [←fixed,←sumU.tsum_sub sumV]
  simp_rw [term]
  have sumSub:Summable (fun s:C=>f s.val):=price.2.1.comp_injective Subtype.val_injective
  calc
    _ ≤ ∑' s:C,f s.val:=norm_tsum_le_tsum_norm sumSub
    _ ≤ ∑' s,f s:=Summable.tsum_subtype_le f C price.1 price.2.1
    _ ≤ _:=price.2.2.trans_eq (by ring)

/-- Quotient of the actual physical scalar gas on a cold, edited bond.
Only the signed scalar mass of the reachable component has to be appreciable,
and only if there is a legitimately contributing long actor. -/
theorem component_physical_gas_log (A:Activities G n){p:BudgetPoint}{δ w:ℝ}(valid:A.Valid p δ w)
    (small:w≤1)(e:Edge (Site n))(r:ℕ)(U V:Fld)(off:ActualGas.sameOffBond e U V)
    (cold:Healthy p.threshold (halo (r*leg p.B) {e.1}) U)(after:e.1∉flags p.threshold V)
    (up:0<A.gas p U)(vp:0<A.gas p V){m:ℝ}(mp:0<m)(rel:2*w*Real.exp (-p.supportExponent*r) ≤ m/2)
    (floor:(longFiled A p e r U ∨ longFiled A p e r V) →
      let F:=jointTerritory A e U V
      m≤max |scalarParcel A p U F ∅| |scalarParcel A p V F ∅|):
    |Real.log (A.gas p U)-Real.log (A.gas p V)| ≤ 2*(2*w*Real.exp (-p.supportExponent*r))/m:=by
  let F:=jointTerritory A e U V
  have fee:=signed_regional_bond_price A valid small e r U V off cold after F
  by_cases eqn:A.gas p U=A.gas p V
  · rw [eqn,sub_self,abs_zero];exact div_nonneg (mul_nonneg zero_le_two ((norm_nonneg _).trans fee)) mp.le
  have before:e.1∉flags p.threshold U:=disjoint_left.mp cold (halo_subset _ _ (mem_singleton_self _))
  obtain ⟨zu,zv,_,logeq⟩:=two_field_local_odds A valid e U V off before after up vp
  rw [logeq]
  exact positive_log_price (abs_pos.mpr zu) (abs_pos.mpr zv) mp
    ((abs_abs_sub_abs_le_abs_sub _ _).trans fee) rel
    (floor (gas_change_needs_roster A p valid.forced e r U V off cold after eqn))

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
