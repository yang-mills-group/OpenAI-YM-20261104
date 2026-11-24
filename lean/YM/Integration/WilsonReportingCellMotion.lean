import YM.Integration.WilsonReportingBareCell
import YM.RG05Readout.Weave.Average

/-! Compute the whole one-step change of the reporting source before
testing. The pullback of its derivative test removes exactly the excess
engineering power at each real child of the physical cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCellMotion
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source RG12
open Extra.Histories Trace.Physical RG05Readout Address Native WilsonReportingBareCell
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {d m N per:ℕ}

def row (C:Family G) {d:ℕ} (t:Letter d) (v:C.label (kept t)) (N per m:ℕ) :
    Goods G (C.side m per) :=
  ((C.factory (kept t) N per).entries m v).density 0 (C.localSection (kept t)) (C.path.rep N per m)

theorem test (t:Letter d) (δ:E4) (r:ℝ) (φ:Body):
    readJ t 0 (Native.pull δ r φ)=((r^depth t:ℝ):ℂ)*readJ t δ φ := by
  simp only [readJ,rate_consider,smul_zero,add_zero,smul_eq_mul]

theorem paid_power (t:Letter d) (l:ℝ) (h:0<l) :
    (l:ℂ)^d*((l⁻¹^depth t:ℝ):ℂ)=(l:ℂ)^(kept t) := by
  have pos:(l:ℂ)≠0:=by exact_mod_cast h.ne'
  have hdepth:depth t≤d:=Nat.le_of_lt_succ t.1.isLt
  calc
    _ = (l:ℂ)^(kept t+depth t)*((l:ℂ)^depth t)⁻¹ := by
      rw [Complex.ofReal_pow,Complex.ofReal_inv,inv_pow,Nat.sub_add_cancel hdepth]
    _ = _ := by rw [pow_add,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ pos),mul_one]

private theorem scalar {c f:Side} (o:StepData c f) (v:Config G f→ℂ) (β:ℝ) (z:ℂ) :
    o.push β (z • v)=z • o.push β v := by
  funext W
  simp only [StepData.push,Pi.smul_apply,smul_comm _ z,integral_smul]

theorem centered_step (h:C.Makes) (t:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (live:m<N) (φ:Body) :
    centered C t v N per m φ=readJ t 0 φ • blast C.path N per m (kept t) (row C t v N per (m+1)) := by
  change readJ t 0 φ • _ = _
  exact congrArg (fun F=>readJ t 0 φ • F)
    ((h.calibrated _ N per (aged.trans live.le)).unnormalized m aged live v)

theorem displaced (t:Letter d) (v:C.label (kept t)) (φ:Body) :
    journey C per m N d (centered C t v N per (m+1)) φ =
    Address.average (fun s:Bud C per m=>readJ t (displacement C per m s) φ • blast C.path N per m (kept t)
      ((row C t v N per (m+1)) ∘ Lattice.pull (1:Signed) (child C per m s))) := by
  unfold journey
  congr 1
  funext s
  let δ:=displacement C per m s
  let tr:=Lattice.pull (K:=G.El) (1:Signed) (child C per m s)
  let F:Goods G (C.side (m+1) per):=row C t v N per (m+1)
  let L:ℝ:=(C.S.block m).val
  change blast C.path N per m d ((readJ t 0 (Native.pull δ L⁻¹ φ)) • (F ∘ tr)) =
    readJ t δ φ • blast C.path N per m (kept t) (F ∘ tr)
  rw [test]
  unfold blast
  rw [scalar,smul_smul,smul_smul]
  congr 1
  rw [← mul_assoc]
  have pos:0<L:=by dsimp only [L]; exact_mod_cast (C.S.block m).property
  have fees:=paid_power t L pos
  simp only [L,Complex.ofReal_natCast] at fees ⊢
  rw [fees,mul_comm]

theorem diagonal (t:Letter d) (v:C.label (kept t)) :
    journey C per m N d (centered C t v N per (m+1)) (line t) =
    Address.average (fun s:Bud C per m=>blast C.path N per m (kept t)
      ((row C t v N per (m+1)) ∘ Lattice.pull (1:Signed) (child C per m s))) := by
  rw [displaced]
  simp only [sliceC t t _ le_rfl,ite_true,one_smul]

theorem off_axis (t i:Letter d) (v:C.label (kept t)) (lower:depth i ≤ depth t) (ne:t≠i) :
    journey C per m N d (centered C t v N per (m+1)) (line i)=0 := by
  rw [displaced]
  simp [sliceC t i _ lower,ne,Address.average]

end YM.Integration.WilsonReportingCellMotion
