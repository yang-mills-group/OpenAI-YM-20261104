import YM.Integration.WilsonOriginalNullAppointments

/-! An arbitrary fixed reserve at the original stability exponent. It uses
the same affine-cell section, granted regular derivatives and genuine upper
wrapping estimate before the cutoff and period are read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullGain
open Function Filter Lattice Wilson RG Source Labels Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local Extra.Histories Next.Foundations
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem stock (C:Family G) {ε:ℝ} (ep:0<ε) : ∀ᶠ i:ℕ in atTop,
    4*(2+4*(C.path.levels.params i).columns)*(GermGraph.factor C i)^(-(2/5:ℝ)) ≤
      ε*(GermGraph.factor C i)^(-(1/8:ℝ)) := by
  open GermGraph Real in
  obtain ⟨base,previous⟩:=eventually_atTop.mp (factor_large C (1/16) (by norm_num))
  have rising : Tendsto (GermGraph.factor C) atTop atTop := tendsto_atTop.mpr fun a=>by
    let b:=max 1 a
    have bp:0<b:=zero_lt_one.trans_le (le_max_left _ _)
    filter_upwards [GermGraph.factor_large C b⁻¹ (inv_pos.mpr bp)] with j his
    exact (le_max_right _ _).trans (inv_inv b ▸ his.1)
  have grown := (tendsto_rpow_atTop (show (0:ℝ)<1/8 by norm_num)).comp rising
  filter_upwards [eventually_ge_atTop (base+1),grown.eventually_ge_atTop (12/ε)] with i eligible enough
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show i≠0 by omega)
  let l:=GermGraph.factor C (j+1)
  have l1:1 ≤ l:=(GermGraph.factor_positive C _).le
  have lp:0<l:=zero_lt_one.trans_le l1
  have prev:= (previous j (by omega)).2
  have single : 4*GermGraph.stock C (j+1) ≤ l^(1/16:ℝ):=prev.trans
    (Real.rpow_le_rpow (zero_lt_one.trans_le (GermGraph.factor_positive C j).le).le
      (WilsonOriginalNullStock.adjacent C j) (by norm_num))
  have one:=Real.one_le_rpow l1 (show (0:ℝ) ≤ 1/16 by norm_num)
  have head:4*(2+4*GermGraph.stock C (j+1)) ≤ 12*l^(1/16:ℝ):=by linarith only [single,one]
  have enough': 12 ≤ ε*l^(1/8:ℝ):=by
    have h:12/ε ≤ l^(1/8:ℝ):=enough
    simpa only [mul_comm ε] using (div_le_iff₀ ep).mp h
  have count : 4*(2+4*GermGraph.stock C (j+1)) ≤ (ε*l^(1/8:ℝ))*l^(1/16:ℝ) :=
    head.trans (mul_le_mul_of_nonneg_right enough' (Real.rpow_nonneg lp.le _))
  calc
    _ ≤ ((ε*l^(1/8:ℝ))*l^(1/16:ℝ))*l^(-(2/5:ℝ)) :=
      mul_le_mul_of_nonneg_right count (Real.rpow_nonneg lp.le _)
    _ = ε*l^((1/8:ℝ)+1/16+ -(2/5:ℝ)) := by rw [Real.rpow_add lp,Real.rpow_add lp];ring
    _ ≤ ε*l^(-(1/8:ℝ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le l1 (by norm_num)) ep.le

variable (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "T₀" => R.family.localSection d
local notation "B₀" j:max => R.family.path.levels.budget j
local notation "w₀" j:max => price G (max (B₀ j).order (B₀ j).power)
local notation "staff₀" j:max => factor R.family.params T₀ (B₀ j).supportExponent (w₀ j)
local notation "block₀" j:max => GermGraph.factor R.family j
local notation "stock₀" j:max => 2 + 4*(R.family.path.levels.params j).columns

structure Appointment (ε:ℝ) (i:ℕ) : Prop where
  ordinary : WilsonOriginalNullAppointments.Paid R d i
  reserve : 4*(stock₀ i)*(block₀ i)^(-(2/5:ℝ)) ≤ ε*(block₀ i)^(-(1/8:ℝ))
  wrapped : ∀ (per:ℕ) (U:Rep G (R.family.side (i+1) per)), U.p=B₀ (i+1) →
    ∀ (o:Site (R.family.side (i+1) per))
      (h:Coefficient F₀ (R.family.side (i+1) per)) {κ b:ℝ}, h.Format o R.family.params U →
      h.remBound o U κ b → Germ.projection F₀ R.family.params U.p.threshold o h=0 →
      let wage := price G (max U.p.order U.p.power)
      let fee := (block₀ i)^d*(4*staff₀ i+1)*U.p.mass ((T₀).footprint o) (wage*(F₀).coeffSize h.x)
      4*(stock₀ i)*fee ≤ ε*(block₀ i)^(-(1/8:ℝ))*b

theorem original (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R d) {ε:ℝ} (ep:0<ε)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (roster:∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power) :
    ∀ᶠ i:ℕ in atTop, Appointment R d ε i := by
  obtain ⟨upper,hwrap⟩:=eventually_atTop.mp (WilsonMeasuredNullWrappedDate.original R simple d (-((d:ℝ)+7)))
  filter_upwards [WilsonOriginalNullAppointments.original R d simple M slow roster,stock R.family ep,
    eventually_ge_atTop upper,WilsonOriginalNullWrappedFee.original R d M,
    R.family.S.divergent.eventually_ge_atTop ε⁻¹] with i calendar reserve next bill late
  refine ⟨calendar,reserve,?_⟩
  intro per U point o h κ b shape paid null wage fee
  let s:=R.family.S.scale (i+1)
  have du : d ≤ U.p.order := point.symm ▸ calendar.upper.2.2.1
  have pu : d ≤ U.p.power := point.symm ▸ calendar.upper.2.2.2.1
  have held:=hwrap (i+1) (Nat.le_succ_of_le next) per U point o h shape paid du pu null
  have size:0 ≤ b:=rem_nonneg paid
  have ge:ε⁻¹ ≤ s:=late.trans ((OPE.scale_mono R.family.S).monotone (Nat.le_succ i))
  have inv:Real.exp (-s) ≤ ε := by
    rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos _) ep]
    linarith only [ge,Real.add_one_le_exp s]
  have exponent : Real.exp (-((d:ℝ)+7)*s) ≤ Real.exp (-((d:ℝ)+6)*s)*ε := by
    rw [show -((d:ℝ)+7)*s= -((d:ℝ)+6)*s+(-s) by ring,Real.exp_add]
    exact mul_le_mul_of_nonneg_left inv (Real.exp_pos _).le
  let v:=(germ_close F₀ R.family.params).choose
  have v0:0 ≤ v:=(germ_close F₀ R.family.params).choose_spec.1.le
  have value : ‖h.x‖ ≤ v*Real.exp (-((d:ℝ)+6)*s)*(ε*b) := by
    exact held.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left exponent v0) size).trans_eq (by ring))
  have priced:=bill per o h.x (ε*b) (mul_nonneg ep.le size) value
  dsimp only [fee,wage];rw [point]
  exact priced.trans_eq (by ring)

end YM.Integration.WilsonOriginalNullGain
