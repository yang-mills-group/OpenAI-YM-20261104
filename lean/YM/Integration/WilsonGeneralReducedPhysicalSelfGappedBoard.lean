import YM.Integration.WilsonGeneralReducedPhysicalSelfGapped
import YM.Integration.WilsonGeneralReducedPhysicalSelfFullWord

/-! The spatial aperture is chosen from the free Gram before any thermal
order. All positive finite readings on its gapped bump use actual rounded
sites and the complete normalized finite-board insert. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfGappedBoard
open Filter Set Function Finset Metric Lattice Maxwell MS MS.Land MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Table.Pairing
open WilsonPositionProgramPublicReflectedRead WilsonPositionProgramPublicWickGram
open WilsonOriginalPublicPlantedGram (measured)
open WilsonPositionProgramPublicContrast (assay)
open WilsonGeneralReducedPhysicalSelfFullWord (finiteWord atNode)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped Classical Topology BigOperators
variable {G:Gauge}(Z:WilsonPrescription G){g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z g M T dial){d:ℕ}{I:Type}[Fintype I]{B₀:Local.Physical.Deck G}
    (a:Axis)(legs:I→Glyph B₀ d)

include H in
theorem budget (δ:ℝ)(hd:0<δ):∃ρ:ℝ,0<ρ ∧ ∀q:ℕ,∀(l:Filter ℝ){t:ℝ→ℝ},
    (∀ᶠ r in l,0<t r) → Tendsto t l (𝓝 0) → ∀(D:ℕ)(C:ℝ),∃j₀:ℕ,∀ᶠ r in l,∀j≥j₀,
    (j:ℝ)≤C*(-Real.log (t r))^D → ∀{B}(P:Handoff.Directory Z j B),Handoff.Directory.budget G 2 d+q≤B →
    ∀s:Sample 2,s.F=Z.run.step j → welcome s → dist (familiar s) (lower a)<ρ →
    ∀u:ℝ,|u|≤8*t r → ‖measured Z a legs q P u s-reading a (nodes a) legs‖≤δ:=by
  obtain ⟨b,hb,domain⟩:=Metric.mem_nhds_iff.mp ((conf_open 2).mem_nhds (separated a))
  let K:=closedBall (lower a) (b/2)
  have compact:IsCompact K:=isCompact_closedBall ..
  have sep:K⊆conf 2:=fun _ h=>domain (lt_of_le_of_lt (mem_closedBall.mp h) (by linarith))
  obtain ⟨ε,he,fee⟩:=gate_senses (lower a)
      (Metric.tendsto_nhds.mp (earned Z.scheme Z.store a legs) (δ/2) (half_pos hd))
  obtain ⟨j₁,ready⟩:=eventually_atTop.mp ((goesFront (Expense.Stretched.runs Z.run)).eventually fee)
  refine ⟨min (b/2) ε,lt_min (half_pos hb) he,?_⟩
  intro q l t pos small D C
  have family (i k:I):=WilsonOriginalPublicPlantedGramBudget.original Z H (signed a legs i k) q
      compact sep l pos small D C (half_pos hd)
  choose date owed using family
  have all:=eventually_all.mpr (fun i=>eventually_all.mpr (fun k=>owed i k))
  let j₀:=j₁+∑i,∑k,date i k
  refine ⟨j₀,?_⟩
  filter_upwards [all] with r bills j hj short B P cov s hs admitted near u hu
  have jbase:j₁≤j:=le_trans (Nat.le_add_right ..) hj
  have use₁:=ready j jbase s.layout s.center (by simpa only [welcome,←hs] using admitted)
  have hfree:‖matrix Z.scheme Z.store a legs s-reading a (nodes a) legs‖<δ/2:=by
    rcases s with ⟨F,x,c⟩
    dsimp at hs
    subst F
    simpa only [dist_eq_norm] using use₁ (near.trans_le (min_le_right ..))
  have member:familiar s∈K:=mem_closedBall.mpr (near.le.trans (min_le_left ..))
  have budget:‖measured Z a legs q P u s-matrix Z.scheme Z.store a legs s‖≤δ/2:=by
    apply (pi_norm_le_iff_of_nonneg (half_pos hd).le).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (half_pos hd).le).mpr
    intro k
    have smallDate : date i k≤∑i,∑k,date i k :=
      (single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ k)).trans
        (single_le_sum (f:=fun h=>∑k,date h k) (fun _ _=>Nat.zero_le _) (mem_univ i))
    exact bills i k j (smallDate.trans ((Nat.le_add_left ..).trans hj)) short P cov s hs admitted member u hu
  exact (norm_sub_le_norm_sub_add_norm_sub ..).trans (by linarith)

def atPlace (M:Mesh)(c:Four ℝ)(y:Points 2):Sample 2:=⟨M,draw y M c,c⟩

private theorem average {ι:Type}[Fintype ι]{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    (w:ι→ℝ)(v:ι→E)(b:E)(δ:ℝ)(positive:∀i,0≤w i)(unit:∑i,w i=1)(close:∀i,‖v i-b‖≤δ):
    ‖(∑i,w i • v i)-b‖≤δ:=by
  have eq:(∑i,w i • v i)-b=∑i,w i • (v i-b):=by
    simp only [smul_sub,sum_sub_distrib,←sum_smul,unit,one_smul]
  rw [eq]
  calc
    _≤∑i,‖w i • (v i-b)‖:=norm_sum_le _ _
    _≤∑i,w i*δ:=sum_le_sum fun i _=>by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (positive i)];exact mul_le_mul_of_nonneg_left (close i) (positive i)
    _=δ:=by rw [←sum_mul,unit,one_mul]

include H in
theorem original (each:Injective legs):∃(p:Points 2)(b:ContDiffBump p)(σ k:ℝ),0<σ ∧ 0<k ∧
    (∀y∈tsupport b,∀i:Axis,σ<y 1 i-y 0 i) ∧
    ∀q:ℕ,∀(l:Filter ℝ){t:ℝ→ℝ},(∀ᶠ r in l,0<t r) → Tendsto t l (𝓝 0) →
    ∀(D:ℕ)(C:ℝ),∃j₀:ℕ,∀ᶠ r in l,∀j≥j₀,(j:ℝ)≤C*(-Real.log (t r))^D →
    ∀{B}(P:Handoff.Directory Z j B),Handoff.Directory.budget G 2 d+q≤B →
    ∀c∈(Z.run.step j).Box,∀u:ℝ,|u|≤8*t r →
    ∀{ι:Type}[Fintype ι](w:ι→ℝ)(y:ι→Points 2), (∀i,0≤w i) → (∑i,w i=1) → (∀i,y i∈tsupport b) →
    ∀v:I→ℂ,k*‖v‖^2≤‖assay v v (∑i,w i • measured Z a legs q P u (atPlace (Z.run.step j) c (y i)))‖:=by
  obtain ⟨k,δ,kp,dp,margin⟩:=WilsonPositionProgramPublicWickGram.original a legs each
  obtain ⟨ρ,rp,fund⟩:=budget Z H a legs δ dp
  obtain ⟨p,b,σ,sp,poses⟩:=WilsonGeneralReducedPhysicalSelfGapped.original a (half_pos rp)
  refine ⟨p,b,σ,k,sp,kp,fun y hy=>(poses y hy).2,?_⟩
  intro q l t pos small D C
  obtain ⟨j₀,paid⟩:=fund q l pos small D C
  have spacing:Tendsto (fun j:ℕ=>(8:ℝ)*(Z.run.step j).spacing) atTop (𝓝 0):=by
    simpa only [mul_zero,comp_apply,Expense.a,id_eq] using (frontier.endpt.comp H.onSchedule).const_mul (8:ℝ)
  obtain ⟨j₁,late⟩:=eventually_atTop.mp (spacing.eventually_lt_const (half_pos rp))
  refine ⟨max j₀ j₁,?_⟩
  filter_upwards [paid] with r due j hj short n P grades c hc u heat ι inst w y wp unit support v
  apply margin
  apply average _ _ _ _ wp unit
  intro i
  let M:=Z.run.step j
  have rounded:dist (M.rel (draw (y i) M c) c) (y i)≤8*M.spacing:=by
    convert M.upper_corner c (z:=y i) (x:=draw (y i) M c) rfl using 1; norm_num
  have smallStep:=late j ((le_max_right ..).trans hj)
  change 8*M.spacing<ρ/2 at smallStep
  have rounded':dist (familiar (atPlace M c (y i))) (y i)≤8*M.spacing:=rounded
  have near:dist (familiar (atPlace M c (y i))) (lower a)<ρ:=
    (dist_triangle _ (y i) _).trans_lt (by have h:dist (y i) (lower a)<ρ/2:=(poses _ (support i)).1;linarith only [rounded',smallStep,h])
  exact due j ((le_max_left ..).trans hj) short P grades (atPlace M c (y i)) rfl hc near u heat

end YM.Integration.WilsonGeneralReducedPhysicalSelfGappedBoard
