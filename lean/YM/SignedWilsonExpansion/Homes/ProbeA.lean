import YM.PhysMS.Frame.Tensor
import YM.PhysMS.Frame.Step

/-! Operate with arbitrary ultrafilter below the *full* ordered fuse at fixed radius,
then r->0 (and arbitrary cut-book choices). Will prove coarse estimates uniform on
this staffed scope using a test-nonzero proof and joint position-limit continuity on
all fixed compact demands. Includes mixed caps. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open scoped Topology BigOperators Classical ContDiff
variable {n:ℕ} {ι : Type*}

lemma bound_of_ceiling {L:Filter ι} (v : ι→ℝ)
   (hc : ∀ U:Ultrafilter ι,(U:Filter _)≤L → ¬ Tendsto v (U:Filter _) atTop) :
   ∃ C:ℝ,∀ᶠ i in L,v i≤C := by
   by_contra! hp
   let K:=L⊓Filter.comap v atTop
   have HI:K.NeBot:=inf_neBot_iff_frequently_right.mpr fun {p} P=>by
      obtain ⟨s,hs,H⟩:= Filter.mem_comap.mp P
      obtain ⟨ε,hε⟩:=mem_atTop_sets.mp hs
      exact (hp ε).mono (fun _ he=> H (hε _ he.le))
   obtain ⟨U,hU,hK⟩:= (exists_ultrafilter_iff.mpr HI).imp (fun _ H=> le_inf_iff.mp H)
   exact hc U hU (tendsto_iff_comap.mpr hK)
lemma appointment {X:Type*} [TopologicalSpace X] {Z:Set X}(hZ:IsCompact Z) {U:Ultrafilter ι} {v:ι→X}
   (hv: ∀ᶠ i in (U:Filter ι), v i∈ Z) : ∃ y∈ Z,Tendsto v (U:Filter _) (𝓝 y) := by
   exact hZ.ultrafilter_le_nhds (U.map v) (Filter.le_principal_iff.mpr hv)
lemma regularly {X:Type*} {L:Filter ι} {v:ι→X} {f:Filter X} (hp : ∀ U:Ultrafilter ι,(U:Filter _)≤L→ Tendsto v (U:Filter _) f): Tendsto v L f :=
   Filter.tendsto_iff_comap.mpr (Filter.le_iff_ultrafilter.mpr (fun U hu=> Filter.tendsto_iff_comap.mp (hp U hu)))

def marginT (x:Test n):ℝ := 1+ ∫ v:Points n, ‖x v‖
lemma marginT_pos (x:Test n) : 0 < marginT x := add_pos_of_pos_of_nonneg zero_lt_one (integral_nonneg fun _=> by positivity)
lemma smooth_pay (f:Test n) (t:ℝ) (ht: 0≤t)
   {x y : Points n→ℂ} (X:ContinuousOn x (conf n)) (Y:ContinuousOn y (conf n))
   (h:∀ v ∈ tsupport f, dist (x v) (y v) ≤ t) : dist (f.applyTo x) (f.applyTo y) ≤ marginT f*t := by
   rw [dist_eq_norm, Test.applyTo,Test.applyTo,←integral_sub (f.smearing X) (f.smearing Y)]
   let d(v:Points n):= ‖f v‖ * t
   have H:∀ᵐ v:Points n, ‖(f v*x v)-(f v*y v)‖≤ d v:= Eventually.of_forall fun v=>by
     unfold d; by_cases hv:v∈ tsupport f
     · rw [←mul_sub,norm_mul]
       exact mul_le_mul_of_nonneg_left ((dist_eq_norm ..).symm.trans_le (h v hv)) (norm_nonneg _)
     simp [image_eq_zero_of_notMem_tsupport hv]
   refine (norm_integral_le_of_norm_le ((f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm.mul_const _) H).trans ?_
   unfold marginT; rw [integral_mul_const,add_mul,one_mul]; linarith
lemma chargeT {L:Filter ι} (f:Test n) {x:ι→Points n→ℂ} {y:Points n→ℂ} (hx:TendstoUniformlyOn x y L (tsupport f))
   (he:∀ᶠ i in L, ContinuousOn (x i) (conf n)) (H:ContinuousOn y (conf n)): Tendsto (fun i=>f.applyTo (x i)) L (𝓝 (f.applyTo y)):= by
   apply Metric.tendsto_nhds.mpr
   intro ε ep
   have ht:=marginT_pos f
   filter_upwards [he,Metric.tendstoUniformlyOn_iff.mp hx (ε/2/marginT f) (by positivity)] with i h hk
   exact ((smooth_pay f _ (by positivity) h H (fun v hv=> (dist_comm ..).trans_le (hk v hv).le)).trans_eq (by field_simp)).trans_lt (half_lt_self ep)

variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
lemma higher {F:Final C f S} {J:ℝ→tower S} (P:Leading F J) {L:Filter ι} {r:ι→ℝ} (hr:Tendsto r L trail)
   {d:Caps n} (b:ℕ) {U:ι→MaxwellSlots C d} {v:MaxwellSlots C d} (h : ∀ j, Tendsto (fun i=> U i j) L (𝓝 (v j)))
   {X:Set (Points n)} (hX:IsCompact X) (hx:X⊆conf n):
   TendstoUniformlyOn (fun i=>iteratedFDeriv ℝ b (measured F none (J (r i)) (U i) (r i))) (iteratedFDeriv ℝ b (WickGoal v)) L X :=
   measured_tensor F (hr.eventually self_mem_nhdsWithin) d b (fun _=>Module.finBasis ℂ _) hX hx
     (fun v=> Metric.tendstoUniformlyOn_iff.mpr (fun ε ep=> hr.eventually (Metric.tendstoUniformlyOn_iff.mp (P.lead n d _ b X hX hx) ε ep))) h
lemma zero_normD (x y:Points n→ℂ)(v:Points n):
   dist (iteratedFDeriv ℝ 0 x v) (iteratedFDeriv ℝ 0 y v)=dist (x v) (y v):= by
      rw [dist_eq_norm,dist_eq_norm, show iteratedFDeriv ℝ 0 x v - _ = iteratedFDeriv ℝ 0 (fun x' => x x'-y x') v from ?_, norm_iteratedFDeriv_zero]
      ext z; simp
lemma coordU {L:Filter ι}(x:ι→Points n→ℂ)(y:Points n→ℂ) {X:Set (Points n)} :
   TendstoUniformlyOn x y L X ↔ TendstoUniformlyOn (fun i => iteratedFDeriv ℝ 0 (x i)) (iteratedFDeriv ℝ 0 y) L X := by
      simp_rw [Metric.tendstoUniformlyOn_iff,zero_normD]
lemma sensedC {F:Final C f S}(r:ℝ) (hr:0<r) (J:tower S) {d:Caps n} (v:MaxwellSlots C d):
   ContinuousOn (measured F none J v r) (conf n) :=
   ((S.class_smooth S F.room.kernel.smooth (fun i=>⟨d i,J _ (v i)⟩)).continuousOn.comp (by fun_prop:ContinuousOn (fun x:Points n=>r • x) (conf n)) (fun _ h=> Work.A05.smul_conf hr h))
lemma WickC {d:Caps n} (v:MaxwellSlots C d) : ContinuousOn (WickGoal v) (conf n) := fun x h=> ((WickGoal_tied v h).continuousAt.continuousWithinAt)
lemma chargeV {F:Final C f S} {J:ℝ→tower S} (P:Leading F J) {L:Filter ι} {r:ι→ℝ} (hr:Tendsto r L trail)
   {d:Caps n} {U:ι→MaxwellSlots C d} {v:MaxwellSlots C d} (h: ∀ j, Tendsto (fun i=> U i j) L (𝓝 (v j))) (t:Test n) :
   Tendsto (fun i=>t.applyTo (measured F none (J (r i)) (U i) (r i))) L (𝓝 (t.applyTo (WickGoal v))) :=
   chargeT t ((coordU _ _).2 (higher P hr _ h t.hasCompactSupport t.tsupport_subset)) ((hr.eventually self_mem_nhdsWithin).mono (fun _ hi=> sensedC _ (show 0< r _ from hi) _ _)) (WickC _)

end YM.SignedWilsonExpansion.Homes
