import YM.Integration.WilsonOriginalPublicPlantedGramBudget
import YM.Integration.WilsonOriginalPublicPlantedPivotFields

/-! Truncation on one actual normalized public Wilson print at every compact separated
test. The chosen polynomial clock absorbs the coefficient bill at the higher order. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedTaylorTail
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries
open WilsonPositionRawFiling WilsonPositionProtectedTuplePrice WilsonPositionProgramPublicDirectoryCoin
open WilsonOriginalPublicPlantedPivotFields (plant)
open private entry from YM.Integration.WilsonPositionCompactEpochSampling
open private mass from YM.Integration.WilsonOriginalPublicPlantedGramBudget
open scoped Topology BigOperators Classical

theorem truncate (a:ℕ→ℂ)(J Q:ℕ)(order:J≤Q){V t u:ℝ}(fund:0≤V)
    (positive:0<t)(small:8*t≤1)(close:|u|≤8*t)(paid:∀k≤Q,‖a k‖≤V):
    ‖(∑k∈range (Q+1),a k*(u:ℂ)^k)-∑k∈range (J+1),a k*(u:ℂ)^k‖≤
      ((Q+1:ℕ):ℝ)*V*(8*t)^(J+1):=by
  rw [←sum_Ico_eq_sub _ (Nat.succ_le_succ order)]
  calc
    _≤∑_k∈Ico (J+1) (Q+1),V*(8*t)^(J+1):=(norm_sum_le ..).trans (sum_le_sum (by
      intro k hk
      obtain ⟨start,stop⟩:=mem_Ico.mp hk
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (paid k (by omega))
        ((pow_le_pow_left₀ (abs_nonneg u) close k).trans
          (pow_le_pow_of_le_one (by positivity) small start)) (by positivity) fund))
    _≤((Q+1:ℕ):ℝ)*V*(8*t)^(J+1):=by
      rw [sum_const,nsmul_eq_mul,mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (Finset.Ico (J+1) (Q+1)).card≤Q+1 by simp only [Nat.card_Ico];omega)

variable {G:Gauge} (Z:WilsonPrescription G){sg:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z sg M T dial){n d:ℕ}(v:Tags G d n)
    {K:Set (Points n)}(compact:IsCompact K)(sep:K⊆conf n)
    (l:Filter ℝ){t:ℝ→ℝ}(pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))

include H compact sep pos small in
theorem directory (J Q:ℕ)(order:J≤Q)(D:ℕ)(C:ℝ){δ:ℝ}(toll:0<δ):
    ∃ i₀:ℕ,∀ᶠ r in l,∀i≥i₀,(i:ℝ)≤C*(-Real.log (t r))^D →
      ∀{B}(P:Handoff.Directory Z i B),Handoff.Directory.budget G n d+Q≤B →
      ∀s:Sample n,s.F=Z.run.step i → welcome s → familiar s∈K → ∀u:ℝ,|u|≤8*t r →
        ‖drawValue Z v Q P u s.layout-drawValue Z v J P u s.layout‖≤δ*(t r)^J:=by
  obtain ⟨A,ha,fee⟩:=terms Z H v Q compact sep
  let L:=((Q+1:ℕ):ℝ)*A*8^(J+1)
  have hl:0≤L:=by dsimp [L];positivity
  obtain ⟨j,borrow⟩:=mass Z H Q D C l pos small (δ:=δ/(1+L)) (by positivity)
  have horizon:=H.onSchedule.eventually frontier.smaller
  have side:∀ᶠ i:ℕ in atTop,16≤((Z.run.step i).p.side.val:ℝ):=
    (frontier.horizon.comp H.onSchedule).eventually_ge_atTop 16
  obtain ⟨i₀,available⟩:=eventually_atTop.mp (fee.and (horizon.and side))
  refine ⟨max i₀ j,?_⟩
  filter_upwards [borrow,pos,small.eventually (gt_mem_nhds (show (0:ℝ)<1/8 by norm_num))] with r room hr low
  intro i later clock B P budget s hs good near u close
  obtain ⟨printed,fine,large⟩:=available i ((le_max_left ..).trans later)
  let m:=(1+WilsonPositionRawMesh.mass Z (Z.run.step i) Q)^Q
  have hm : 0 ≤ m := by
    have h:0≤WilsonPositionRawMesh.mass Z (Z.run.step i) Q:=sum_nonneg fun _ _=>abs_nonneg _
    exact pow_nonneg (by linarith) _
  have test:Notch.Entry (1/16) s:=entry s (by rw [hs];exact_mod_cast large) (by rw [hs];exact fine) good
  have spent:=room i ((le_max_right ..).trans later) clock
  rw [abs_of_pos hr] at spent
  have used:m*t r*(1+L)≤δ:=(le_div_iff₀ (by positivity)).mp spent
  calc
    _≤((Q+1:ℕ):ℝ)*(A*m)*(8*t r)^(J+1):=truncate _ _ _ order (mul_nonneg ha hm) hr (by linarith) close
      (printed P budget s hs test near)
    _=L*(m*t r)*(t r)^J:=by dsimp only [L];rw [mul_pow,pow_succ (t r)];ring
    _≤δ*(t r)^J:=mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hm hr.le]:L*(m*t r)≤δ) (pow_nonneg hr.le _)

def value (β:Local.Physical.Deck G)(j q:ℕ)(s:Sample n)(u:ℝ):ℂ:=
  ∑k∈range (q+1),coeff k (Bare.normalized (Z.scheme.tree s.F.p) G
    (∏i,plant Z.scheme β (WilsonPositionRawEpoch.matrix Z j d) s i (v i)))*(u:ℂ)^k

include H compact sep pos small in
theorem original (β:Local.Physical.Deck G)(J Q:ℕ)(order:J≤Q)(D:ℕ)(C:ℝ){δ:ℝ}(toll:0<δ):
    ∃ i₀:ℕ,∀ᶠ r in l,∀i≥i₀,(i:ℝ)≤C*(-Real.log (t r))^D →
      ∃P:Handoff.Directory Z i (Handoff.Directory.budget G n d+Q),
      ∀s:Sample n,s.F=Z.run.step i → welcome s → familiar s∈K → ∀u:ℝ,|u|≤8*t r →
        drawValue Z v Q P u s.layout=value Z v β i Q s u ∧
        drawValue Z v J P u s.layout=value Z v β i J s u ∧
        ‖value Z v β i Q s u-value Z v β i J s u‖≤δ*(t r)^J:=by
  obtain ⟨i₀,funded⟩:=directory Z H v compact sep l pos small J Q order D C toll
  refine ⟨i₀,?_⟩
  filter_upwards [funded] with r prices
  intro i late clock
  obtain ⟨P⟩:=H.packets i (Handoff.Directory.budget G n d+Q)
  refine ⟨P,?_⟩
  intro s hs good near u close
  have top:=WilsonOriginalPublicPlantedPivotFields.drawn β Z P s v hs Q le_rfl u
  have below:=WilsonOriginalPublicPlantedPivotFields.drawn β Z P s v hs J (by omega) u
  refine ⟨top,below,?_⟩
  rw [show value Z v β i Q s u=drawValue Z v Q P u s.layout from top.symm,
      show value Z v β i J s u=drawValue Z v J P u s.layout from below.symm]
  exact prices i late clock P le_rfl s hs good near u close

end YM.Integration.WilsonOriginalPublicPlantedTaylorTail
