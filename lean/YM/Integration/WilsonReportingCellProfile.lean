import YM.Integration.WilsonReportingCellField
import YM.RG05Readout.Test.Common
import YM.RG05Readout.Address.Mobile

/-! The full finite child quadrature preserves constant derivative
profiles and their supremum bound on the original compact reporting cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCellProfile
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source RG12
open Extra.Histories Trace.Physical RG05Readout Address Native
open WilsonReportingCellIntegral WilsonReportingCellMotion WilsonReportingBareCell WilsonReportingCellField
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {d m N per:ℕ}

private theorem mean_norm {I:Type*} [Fintype I] [Nonempty I] (w:I→ℂ) (c:ℝ)
    (paid:∀i,‖w i‖ ≤ c): ‖Address.average w‖ ≤ c := by
  rw [Address.average,norm_smul,norm_inv,Complex.norm_natCast]
  have h:0<(Fintype.card I:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ (Fintype.card I:ℝ)⁻¹ * ∑ _i:I,c :=
      mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>paid i))) (inv_pos.mpr h).le
    _ = c := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ h.ne',one_mul]

private theorem affine (t:Letter d) (δ:E4) (l:ℝ) (φ:Body) (x:E4):
    readJ t x (Native.pull δ l φ)=((l^depth t:ℝ):ℂ)*readJ t (δ+l • x) φ := by
  simp only [readJ,rate_consider,smul_eq_mul]

structure Rule (t:Letter d) (w:Body→ℂ):Prop where
  constant (φ:Body) (z:ℂ) : (∀x∈Native.box,readJ t x φ=z) → w φ=z
  bound (φ:Body) (c:ℝ) : (∀x∈Native.box,‖readJ t x φ‖ ≤ c) → ‖w φ‖ ≤ c

private theorem advance (t:Letter d) (w:Body→ℂ) (good:Rule t w) :
    Rule t (transfer C per m (depth t) w) := by
  let l:ℝ:=((C.S.block m).val:ℝ)⁻¹
  let a:ℂ:=((C.S.block m).val:ℂ)^depth t
  let b:ℂ:=(l^depth t:ℝ)
  have nz:((C.S.block m).val:ℂ)≠0:=by exact_mod_cast (C.S.block m).property.ne'
  have cancels:a*b=1:=by
    simp only [a,b,l,Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_natCast,inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero _ nz)
  constructor
  · intro φ z same
    unfold transfer
    have item (s:Bud C per m):a*w (Native.pull (displacement C per m s) l φ)=z := by
      have e:=good.constant (Native.pull (displacement C per m s) l φ) (b*z)
        (fun x hx=>by rw [affine,same _ (dist_box C per m s hx)])
      rw [e,←mul_assoc,cancels,one_mul]
    change Address.average (fun s:Bud C per m=>a*w (Native.pull (displacement C per m s) l φ))=z
    simp_rw [item]
    exact Address.ave_single z
  · intro φ c paid
    apply mean_norm _ c
    intro s
    have e:=good.bound (Native.pull (displacement C per m s) l φ) (‖b‖*c) (fun x hx=>by
      rw [affine,norm_mul]
      exact mul_le_mul_of_nonneg_left (paid _ (dist_box C per m s hx)) (norm_nonneg _))
    change ‖a*w _‖ ≤ c
    calc
      _ ≤ ‖a‖*(‖b‖*c) := (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left e (norm_nonneg _))
      _ = c := by rw [←mul_assoc,←norm_mul,cancels,norm_one,one_mul]

theorem original (t:Letter d) (q:ℕ) : Rule t (profile C per m (depth t) q (readJ t 0)) := by
  have go (w:Body→ℂ) (good:Rule t w): Rule t (profile C per m (depth t) q w) := by
    induction q generalizing w with
    | zero => exact good
    | succ q past => exact past _ (advance t w good)
  exact go _ ⟨fun _ _ paid=>paid _ box0,fun _ _ paid=>paid _ box0⟩

theorem measured (h:C.Makes) (t:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (q:ℕ) (live:m+q ≤ N) (φ:Body) (c:ℝ) (paid:Cap (d+2) φ c) :
    ‖total (WilsonReportingCellRoute.route C per N d m q (centered C t v N per (m+q)) φ)‖ ≤
    (pulseFee d*c)*‖total (row C t v N per m)‖ := by
  rw [WilsonReportingCellField.integral h t v aged q live,norm_mul]
  exact mul_le_mul_of_nonneg_right ((original t q).bound φ _ (fun _ hx=>fees d t hx paid)) (norm_nonneg _)

theorem diagonal (h:C.Makes) (t i:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (q:ℕ) (live:m+q ≤ N) (low:depth i ≤ depth t) :
    total (WilsonReportingCellRoute.route C per N d m q (centered C t v N per (m+q)) (line i)) =
    if t=i then total (row C t v N per m) else 0 := by
  rw [WilsonReportingCellField.integral h t v aged q live,
    (original t q).constant (line i) _ (fun x _=>sliceC t i x low)]
  split <;> simp

end YM.Integration.WilsonReportingCellProfile
