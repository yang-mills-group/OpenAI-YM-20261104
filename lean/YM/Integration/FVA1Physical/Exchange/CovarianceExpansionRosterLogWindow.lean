import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionBondGasWitness

/-! The only unpriced part of the physical gas oscillation on a cold bond
requires a small gas and a long legally contributing owner together. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function Finset Set MeasureTheory Lattice RG Wilson Push.GridApprox.Attach
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

/-- Both the tests and the exceptional sector are selected regions on the
original finite regulator, defined without reference to a tail estimate. -/
theorem longFiled_borel (A:Activities G n)(p:BudgetPoint)(law:A.ForcedFamily p)
    (e:Edge (Site n))(r:ℕ):MeasurableSet {U:Fld|longFiled A p e r U}:=by
  let F:=fun s:Finset ℕ=>{U:Fld| A.gasOccurrence p s U ≠ 0}
  have fm(s:Finset ℕ):MeasurableSet (F s):=by
    have m:Measurable (A.gasOccurrence p s):=Measurable.ite (A.admissible_borel p s)
      (Finset.measurable_fun_prod _ fun i _=>law.meas i) measurable_const
    exact (measurableSet_eq_fun m measurable_const).compl
  let geo:=fun j:ℕ=> e.1∈(A.forced j).support ∧ e.1+step e.2∈(A.forced j).support ∧
    r ≤ coverNumber p.B (A.forced j).support
  let Z:=fun j:ℕ=>(A.forced j).inventory.filter (fun z=>z∉halo (r*leg p.B) {e.1})
  let T:=fun s:Finset ℕ=>s.filter geo
  have eq:{U:Fld|longFiled A p e r U}=⋃s:Finset ℕ,F s ∩ (⋃j∈T s,⋃z∈Z j,{U:Fld|z∈flags p.threshold U}):=by
    ext U
    simp only [F,T,Z,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff,Finset.mem_filter,geo,longFiled]
    constructor
    · rintro ⟨s,live,j,member,src,dst,cost,z,owns,hot,far⟩
      exact ⟨s,live,j,⟨member,src,dst,cost⟩,z,⟨owns,far⟩,hot⟩
    rintro ⟨s,live,j,⟨member,src,dst,cost⟩,z,⟨owns,far⟩,hot⟩
    exact ⟨s,live,j,member,src,dst,cost,z,owns,hot,far⟩
  rw [eq]
  exact MeasurableSet.iUnion fun s=>(fm s).inter (Finset.measurableSet_biUnion (T s) fun j _=>
    Finset.measurableSet_biUnion (Z j) fun z _=>(flags_open (G:=G) z p.threshold).measurableSet)

private theorem one_log {a b δ m:ℝ}(ap:0<a)(bp:0<b)(mp:0<m)(lb:m/2 ≤ b)
    (d:a-b ≤ δ)(dn:0 ≤ δ):Real.log a-Real.log b ≤ 2*δ/m:=by
  rw [←Real.log_div ap.ne' bp.ne']
  have slog:=Real.log_le_sub_one_of_pos (div_pos ap bp)
  have shop:=div_le_div_of_nonneg_left dn (half_pos mp) lb
  calc
    _ ≤ a/b-1:=slog
    _ = (a-b)/b:=by field_simp
    _ ≤ δ/b:=div_le_div_of_nonneg_right d bp.le
    _ ≤ δ/(m/2):=shop
    _ = _:=by ring

private theorem positive_log_price {a b δ m:ℝ}(ap:0<a)(bp:0<b)(mp:0<m)(paid:|a-b| ≤ δ)
    (small:δ ≤ m/2)(floor:m ≤ max a b):|Real.log a-Real.log b| ≤ 2*δ/m:=by
  have dn:0 ≤ δ:=(abs_nonneg _).trans paid
  obtain ⟨hl,hr⟩:=abs_le.mp paid
  have low:m/2 ≤ a ∧ m/2 ≤ b:=by
    rcases le_max_iff.mp floor with ha|hb <;> constructor <;> linarith
  exact abs_le.mpr ⟨by linarith only [one_log bp ap mp low.1 (show b-a ≤ δ by linarith only [hl]) dn],
    one_log ap bp mp low.2 hr dn⟩

theorem low_gas_roster_log (A:Activities G n)(p:BudgetPoint)(law:A.ForcedFamily p){w:ℝ}
    (paid:A.KBound p w)(ew:w ≤ 1)(e:Edge (Site n))(r:ℕ)(U V:Fld)(off:ActualGas.sameOffBond e U V)
    (localU:Healthy p.threshold (halo (r*leg p.B) {e.1}) U)(after:e.1∉flags p.threshold V)
    (up:0<A.gas p U)(vp:0<A.gas p V){m:ℝ}(mp:0<m)
    (delta:2*w*Real.exp (-p.supportExponent*r) ≤ m/2)
    (u:longFiled A p e r U → m ≤ A.gas p U)(v:longFiled A p e r V → m ≤ A.gas p V):
    |Real.log (A.gas p U)-Real.log (A.gas p V)| ≤ 2*(2*w*Real.exp (-p.supportExponent*r))/m:=by
  have move:=ActualGas.actual_gas_bond_falloff A law paid ew e r U V off localU after
  by_cases same:A.gas p U=A.gas p V
  · rw [same,sub_self,abs_zero]
    exact div_nonneg (mul_nonneg zero_le_two ((norm_nonneg _).trans move)) mp.le
  have t:=gas_change_needs_roster A p law e r U V off localU after same
  exact positive_log_price up vp mp move delta (t.elim (fun h=>(u h).trans (le_max_left ..)) (fun h=>(v h).trans (le_max_right ..)))

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
