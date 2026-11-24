import YM.Integration.WilsonReportingPositiveTransfer

/-! The true affine cell rule transports an absolute bound on the actual
physical density. The signed bud average and the engineering scale are
retained through every selected step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPositiveSpine
open Filter Function Finset Lattice Wilson RG Source RG05Readout Address Native
open Extra.Histories MergeProof Accent WilsonReportingCellRoute
open private mean_norm from YM.Integration.WilsonReportingCellProfile
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {N per m d:ℕ}

def Covered (C:Family G) (N per j:ℕ) {d:ℕ} (t:Letter d) (K:ℝ)
    (F:Body→Goods G (C.side j per)) : Prop :=
  ∀ (φ:Body) (c:ℝ), (∀y∈Native.box, ‖readJ t y φ‖ ≤ c) → ∀ U,
    ‖F φ U‖ ≤ C.S.a j ^ kept t*c*K*(C.path.rep N per j).eval U

theorem step (h:C.Makes) (live:m<N) (t:Letter d) (K:ℝ) (F:Body→Goods G (C.side (m+1) per))
    (budget:Covered C N per (m+1) t K F) : Covered C N per m t K (journey C per m N d F) := by
  intro φ c hg Ω
  let L:ℝ:=(C.S.block m).val
  have pos:0<L:=Nat.cast_pos.mpr (C.S.block m).property
  let slot (i:Bud C per m):=Native.pull (displacement C per m i) L⁻¹ φ
  have range (i:Bud C per m) (y:E4) (inside:y∈Native.box) :
      ‖readJ t y (slot i)‖ ≤ L⁻¹^depth t*c := by
    change ‖readJ t y (Native.pull _ _ φ)‖ ≤ _
    have affine:readJ t y (slot i)=((L⁻¹^depth t:ℝ):ℂ)*readJ t (displacement C per m i+L⁻¹ • y) φ := by
      simp only [slot,readJ,rate_consider,smul_eq_mul]
    rw [←show slot i=Native.pull (displacement C per m i) L⁻¹ φ from rfl,affine,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr pos.le) _)]
    exact mul_le_mul_of_nonneg_left (hg _ (dist_box C per m i inside)) (by positivity)
  let active:=C.S.a (m+1)^kept t*(L⁻¹^depth t*c)*K
  have invoice(i:Bud C per m) (X:Config G (C.side (m+1) per)):
    ‖(F (slot i) ∘ Lattice.pull (1:Signed) (child C per m i)) X‖ ≤ active*(C.path.rep N per (m+1)).eval X := by
    have original:=budget (slot i) _ (range i) (Lattice.pull (1:Signed) (child C per m i) X)
    have symm:(C.path.rep N per (m+1)).eval (Lattice.pull (1:Signed) (child C per m i) X) =
        (C.path.rep N per (m+1)).eval X :=
      Complex.ofReal_inj.mp (vac_pull C.path N per (m+1) h.wilson live _ _ X)
    simpa only [active,Function.comp_apply,symm] using original
  have balance:L^d*L⁻¹^depth t*C.S.a (m+1)^kept t=C.S.a m^kept t := by
    have decay:L^d=L^kept t*L^depth t := by
      rw [←pow_add]
      exact congrArg (L^·) (Nat.sub_add_cancel (Nat.le_of_lt_succ t.1.isLt)).symm
    rw [decay,C.S.a_step,inv_pow,div_pow]
    change L^kept t*L^depth t*(L^depth t)⁻¹*(C.S.a m^kept t/L^kept t)=_
    field_simp
  let row (i:Bud C per m):=blast C.path N per m d (F (slot i) ∘ Lattice.pull (1:Signed) (child C per m i)) Ω
  have each (i:Bud C per m):‖row i‖ ≤ C.S.a m ^ kept t*c*K*(C.path.rep N per m).eval Ω := by
    refine (WilsonReportingPositiveTransfer.sector h live _ active (invoice i) Ω).trans_eq ?_
    change L^d*(C.S.a (m+1)^kept t*(L⁻¹^depth t*c)*K*(C.path.rep N per m).eval Ω)=_
    rw [←balance]
    ring
  change ‖(Address.average (fun i:Bud C per m=>blast C.path N per m d
    (F (slot i) ∘ Lattice.pull (1:Signed) (child C per m i)))) Ω‖ ≤ _
  have numerical: (Address.average (fun i:Bud C per m=>blast C.path N per m d
      (F (slot i) ∘ Lattice.pull (1:Signed) (child C per m i)))) Ω=Address.average row := by
    simp only [Address.average,Pi.smul_apply,Finset.sum_apply,row]
  exact numerical ▸ mean_norm row _ each

theorem route (h:C.Makes) (t:Letter d) (K:ℝ) (q:ℕ) (live:m+q ≤ N)
    (F:Body→Goods G (C.side (m+q) per)) (budget:Covered C N per (m+q) t K F) :
    Covered C N per m t K (WilsonReportingCellRoute.route C per N d m q F) := by
  induction q with
  | zero => exact budget
  | succ q ih =>
    have later:m+q<N:=Nat.lt_of_succ_le live
    exact ih later.le _ (step h (m:=m+q) later t K F budget)

end YM.Integration.WilsonReportingPositiveSpine
