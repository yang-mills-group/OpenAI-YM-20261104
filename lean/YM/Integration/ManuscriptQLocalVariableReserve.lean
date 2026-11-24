import YM.Integration.ManuscriptQLocalPrescribedRadius
import YM.Integration.QLocalFiniteMeasuredRadius
import YM.Integration.FullQLocalCostSubpower

/-! The same marked source can spend a separate subpower pre-coupling price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalVariableReserve
open Function Filter Finset Lattice Wilson RG Marker PhysicalNext.Repeat.Legato Comparison.RG02
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.CostProfile Pert.Asymptotics ManuscriptQLocalRegularConditional ManuscriptQLocalOriginalConditionalTail
open scoped BigOperators Classical Topology
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}
  {C:Family G} {J:Request V} {A:NumericSchedule C J} {d:LocalFormal.Datum C Γ}

def Charged (F:AnalyticInput J A d) (b:ℝ):Prop:=F.packets.Paid (A.inputNorm d.level) F.inputAddresses F.inputRegion
  (fun v=>F.inputRadii v/F.kernelCosts v) 1 (A.inputWidth d.level) b F.coverOffset F.coverSlope

omit [Fintype V] in
theorem room {n:Side} {D:V → ComparisonDensity.Address.Orbit} (P:MarkedPackets D G n Γ) {p:BudgetPoint}
    {a:V → Support n} {Z:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n} {w:V→ℝ} {g width b c:ℝ} {off cov:ℕ}
    (H:P.Paid p a Z w g width b off cov) (hc:b≤c) : P.Paid p a Z w g width c off cov:=by
  refine {H with roots:=fun v=>?_}
  exact ⟨(H.roots v).1,(H.roots v).2.1,(H.roots v).2.2.trans hc⟩

private theorem scaled_radii (F:AnalyticInput J A d) (t:ℝ) :
    (fun v=>t*F.inputRadii v/F.kernelCosts v)=
      QLocalFiniteMeasuredRadius.smaller t (fun v=>F.inputRadii v/F.kernelCosts v):=by
  funext v
  exact mul_div_assoc t (F.inputRadii v) (F.kernelCosts v)

def resize (F:AnalyticInput J A d) {t:ℝ} (ht:0<t) (hs:t≤1) : AnalyticInput J A d:=
  { F with
    inputRadii:=fun v=>t*F.inputRadii v
    outputRadii:=fun v=>t*F.outputRadii v
    input_radius_positive:=fun v=>mul_pos ht (F.input_radius_positive v)
    output_radius_positive:=fun v=>mul_pos ht (F.output_radius_positive v)
    radius_admission:=fun v=>by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (F.radius_admission v) ht.le
    input_paid:=by
      rw [scaled_radii F t]
      exact room F.packets (QLocalFiniteMeasuredRadius.packets F.packets F.input_paid ht hs)
          (mul_le_of_le_one_left (A.admitted_cost_nonnegative d.level) hs)}

theorem resized (F:AnalyticInput J A d) {b t:ℝ} (H:Charged F b) (ht:0<t) (hs:t≤1) :
    Charged (resize F ht hs) (t*b):=by
  change F.packets.Paid _ _ _ (fun v=>t*F.inputRadii v/F.kernelCosts v) 1 _ (t*b) _ _
  rw [scaled_radii F t]
  exact QLocalFiniteMeasuredRadius.packets F.packets H ht hs

omit [Fintype V] in
theorem toll {w:V→ℝ} (t:ℝ) (s:Γ.Mode) :
    Poly.toll (fun v=>t*w v) s=t^s.val.card*Poly.toll w s:=by
  simp only [Poly.toll,Finset.prod_mul_distrib,Finset.prod_const]

variable (Γ) (R:Run G) (A:NumericSchedule R.family J) (hG:G.Simple)

include hG in
theorem original (fee:ℕ→ℝ) (hn:∀m,0≤fee m) (flat:ActualRunSubpowerShift.Subpower R fee)
    (k:ℕ) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m→
      ∀ (F : AnalyticInput J A d),Charged F (fee d.level)→
      ∀ (x : IndependentTests J.tests) (U : Config G (R.family.side d.level d.period)) (s : Γ.Mode),
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      let p₀:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
      let ℓ:=ManuscriptQLocalShiftLedger.weight (fun _:V=>F.packets.powerCap+F.packets.rankCap) s
      let L z:=Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source F.packets p₀ g x) z)
      ∃p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
        Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖≤
          ManuscriptQLocalRegularCalendar.constant (J:=J) Γ*g^((k+1:ℕ)-δ:ℝ) := by
  let v:=Fintype.card V
  let base:=fun m=>1+fee m
  have hbase:∀m,1≤base m:=fun m=>by dsimp [base]; linarith [hn m]
  have grow:=scalar_subpower_pow R hG A base (fun m=>zero_le_one.trans (hbase m))
    (scalar_subpower_add R hG A (fun _=>1) fee (scalar_subpower_constant R hG A 1) flat) v
  filter_upwards [ManuscriptQLocalRegularCalendar.purchased Γ R hG A k (half_pos hδ),
    grow (δ/2) (half_pos hδ)] with m paid price d hd F B x U s
  subst m
  let b:=base d.level
  let t:=b⁻¹
  have hb:1≤b:=hbase d.level
  have pos:0<b:=zero_lt_one.trans_le hb
  have ht:0<t:=inv_pos.mpr pos
  have hs:t≤1:=(inv_le_one₀ pos).2 hb
  have hroom:t*fee d.level≤A.admittedCost d.level:=by
    calc _ ≤ t*b:=mul_le_mul_of_nonneg_left (by dsimp [b,base];linarith) ht.le
         _ = 1:=inv_mul_cancel₀ pos.ne'
         _ ≤ _:=A.admitted_cost_ge_one _
  have B₀:=room F.packets (resized F B ht hs) hroom
  obtain ⟨p,degree,atPoint,bill⟩:=paid d rfl (resize F ht hs) F.packets B₀ F.power_bounded F.rank_bounded x U s
  refine ⟨p,degree,atPoint,?_⟩
  let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
  have hg:0<g:=IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have spend:b^s.val.card≤g^(-(δ/2)) := (pow_le_pow_right₀ hb (Finset.card_le_univ _)).trans (price d.cutoff d.period d.below)
  have restored (u:ℝ) : Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*u =
      b^s.val.card*(Poly.toll (fun v=>t*F.inputRadii v/F.kernelCosts v) s*u):=by
    simp only [mul_div_assoc,toll,t,inv_pow]; field_simp [pos.ne']
  dsimp only [resize] at bill
  have feePositive:= (mul_nonneg (Poly.worth (fun v=>div_pos (mul_pos ht (F.input_radius_positive v)) (F.kernel_positive v)) s).le (norm_nonneg _)).trans bill
  rw [restored]
  calc _ ≤ b^s.val.card*(ManuscriptQLocalRegularCalendar.constant (J:=J) Γ*g^((k+1:ℕ)-δ/2:ℝ)) :=
       mul_le_mul_of_nonneg_left bill (pow_nonneg pos.le _)
       _ ≤ g^(-(δ/2))*(ManuscriptQLocalRegularCalendar.constant (J:=J) Γ*g^((k+1:ℕ)-δ/2:ℝ)) :=
       mul_le_mul_of_nonneg_right spend feePositive
       _ = _:=by rw [mul_left_comm,←Real.rpow_add hg];congr 2;ring

end YM.Integration.ManuscriptQLocalVariableReserve
end
