import YM.RG05Readout.Suede.Silver

/-! The unmodified child average, including its genuine translated tests and
positive Wilson transition, propagates a scalar physical density in every
declared engineering grade. The physical scale factor telescopes exactly and
the price of a test on the fixed unit box does not accumulate along the path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUnitCells
open Function Set Finset Filter MeasureTheory Lattice Wilson RG Source Extra.Histories
open RG05Readout Address Native
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {m N p d:ℕ}

private theorem mean_bound {I:Type*} [Fintype I] [Nonempty I] (z:I→ℂ) (B:ℝ)
    (bound:∀i,‖z i‖≤B) : ‖Address.average z‖≤B := by
  have h:0<(Fintype.card I:ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  rw [Address.average,norm_smul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card I:ℝ)⁻¹ * ∑ i,‖z i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr h.le)
    _ ≤ (Fintype.card I:ℝ)⁻¹ * ∑ _i:I,B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>bound i)) (inv_nonneg.mpr h.le)
    _ = B := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ h.ne',one_mul]

private theorem mean_field {I:Type*} [Fintype I] (z:I→ℂ) (f:Goods G (C.side m p)) :
    Address.average (fun i=>z i • f)=Address.average z • f := by
  funext W
  simp only [Address.average,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,mul_assoc,Finset.sum_mul]

def Priced (C:Family G) (N p m d:ℕ) (income:Body→Goods G (C.side m p)) (A:ℝ) : Prop :=
  ∀(f:Body)(q:ℝ),Cap 0 f q → ∃ z:ℂ,
    income f=z • liftVac C.path N p m ∧ ‖z‖≤C.S.a m^d*A*q

theorem next (h:C.Makes) (live:m<N) {income:Body→Goods G (C.side (m+1) p)} {A:ℝ}
    (paid:Priced C N p (m+1) d income A) :
    Priced C N p m d (journey C p m N d income) A := by
  intro f q cap
  let L:ℝ:=(C.S.block m).val
  have one:1≤L:=by
    dsimp [L]
    exact_mod_cast (show 1≤(C.S.block m).val from (C.S.block m).property)
  have positive:0<L:=zero_lt_one.trans_le one
  let pulled (i:Bud C p m):=Native.pull (displacement C p m i) L⁻¹ f
  have entry (i:Bud C p m): Cap 0 (pulled i) q :=
    cap_aff _ (inv_nonneg.mpr positive.le) (inv_le_one_of_one_le₀ one) (dist_box C p m i) cap
  choose z hz using fun i:Bud C p m=>paid (pulled i) q (entry i)
  let factor : ℂ := ((C.S.block m).val:ℂ)^d
  have step (i:Bud C p m) :
      blast C.path N p m d (income (pulled i) ∘ Lattice.pull (1:Signed) (child C p m i)) =
        (factor*z i) • liftVac C.path N p m := by
    have move:(income (pulled i) ∘ Lattice.pull (1:Signed) (child C p m i))=
        z i • liftVac C.path N p (m+1) := by
      rw [(hz i).1]
      funext U
      exact congrArg (fun a:ℂ=>z i*a) (vac_pull C.path N p (m+1) h.wilson live _ _ U)
    rw [move]
    have lin:blast C.path N p m d (z i • liftVac C.path N p (m+1))=
        z i • blast C.path N p m d (liftVac C.path N p (m+1)) := by
      unfold blast
      rw [StepData.push_smul _ _ _ _ (vac_integrable C.path N p (m+1) h.wilson live)]
      exact smul_comm _ _ _
    rw [lin,blast_vac _ _ _ _ _ h.wilson live,smul_smul,mul_comm (z i)]
  refine ⟨Address.average (fun i=>factor*z i),?_,?_⟩
  · change Address.average (fun i=>blast C.path N p m d (income (pulled i) ∘ Lattice.pull (1:Signed) (child C p m i)))=_
    simp_rw [step]
    exact mean_field _ _
  · apply mean_bound
    intro i
    have normfactor:‖factor‖=L^d:=by simp [factor,L]
    rw [norm_mul,normfactor]
    calc
      _ ≤ L^d * (C.S.a (m+1)^d*A*q) := mul_le_mul_of_nonneg_left (hz i).2 (pow_nonneg positive.le _)
      _ = _ := by
        have eq:L*C.S.a (m+1)=C.S.a m:=by rw [Schedule.a_step]; dsimp only [L]; field_simp
        rw [← mul_assoc,← mul_assoc,← mul_pow,eq]

end YM.Integration.WilsonReportingUnitCells
