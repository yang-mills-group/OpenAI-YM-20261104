import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Permit
/-! # Leading properties inherited by H. Including mixed caps and all compact derivatives.
Proof by fixed multilinear basis in `Sec`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d} (t:ℝ→ℝ)
    (hJ:Leading U J) (P:Realized J Y N A t)
local notation "late" => 𝓝[>] (0:ℝ)
variable {D: Fin n→ℕ} {K:Set (Points n)} (v:Slots G D) (hc:IsCompact K)(hz:K⊆conf n)
local notation "H'T" => booth K late
local notation "Bf" => BasisSlots G D

abbrev price (v: Slots G D) : MaxwellSlots C D:= fun i=>(Free.fields C.labels (D i)).symm (v i)
abbrev Μ (x:Points n) (v:Slots G D)(r:ℝ):= measured U none (J r) (price v) r x
lemma money (v:Slots G D) {r:ℝ} (hr:0<r) {x:Points n}(hx:x∈conf n) (p:ℕ) : ContDiffAt ℝ p (fun x=> Μ U J x v r) x := by
  let X:=spectate U none; let u (i: Fin n):S.Tag:=⟨ D i,J r (D i) ((Free.fields C.labels (D i)).symm (v i)) ⟩
  have h:= S.class_smooth (spectator U none) X.smooth u
  exact (.of_le ((h.contDiffAt ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))).comp (f:=fun x:Points n=>r • x) x (by fun_prop)) (WithTop.coe_le_coe.mpr le_top))
lemma jets (v:Slots G D) {r:ℝ} (hr:0<r) (j:ℕ) {x:Points n} (hx:x∈conf n) :
    iteratedFDeriv ℝ j (measured U none (J r) (price v) r) x = ∑ q:Bf,
      coordinates q v • iteratedFDeriv ℝ j (fun x=> Μ U J x (word q) r) x:= by
  have e : measured U none (J r) (price v) r=fun (x:Points n)=> ∑ q:Bf,coordinates q v • Μ U J x (word q) r := by
    funext x; let L:= S.classMoment S D (r • x); exact word_sigma v (L.compLinearMap (fun i=> (frame J r (D i)).toLinearMap))
  rw [e, iteratedFDeriv_fun_sum_apply (fun i _=> (money U J (word i) hr hx j).const_smul (coordinates i v))]; exact Finset.sum_congr rfl fun i _=> iteratedFDeriv_const_smul_apply' (money U J (word i) hr hx j)

lemma outlay {α F:Type*}[NormedAddCommGroup F] {A : I → α→F} {a:α→F} {K:Set α} :
    TendstoUniformlyOn A a L K ↔ Tendsto (fun x:I×α=>A x.1 x.2-a x.2) (L ×ˢ 𝓟 K) (𝓝 0) := by
  rw [tendstoUniformlyOn_iff_tendsto, uniformity_eq_comap_nhds_zero,tendsto_comap_iff]; rfl
include hc hz hJ
lemma holding (j:ℕ) : (fun i:ℝ×Points n=>iteratedFDeriv ℝ j (measured U none (J i.1) (price v) i.1) i.2)=O[H'T] Pose.home := by
  let V: MaxwellSlots C D:= price v; let F i:= iteratedFDeriv ℝ j (WickGoal V) i
  have hf : ContinuousOn F K:= by
    intro i hi; have h:= WickGoal_tied V (hz hi); exact (h.continuousAt_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top : (↑j:WithTop ℕ∞)≤ ∞)).continuousWithinAt
  obtain ⟨B,H⟩:= hc.exists_bound_of_continuousOn hf
  have hr : (fun i:ℝ×Points n=>F i.2) =O[H'T] Pose.home:= IsBigO.of_bound B (by simpa [Pose.home] using (placed (F:=late) (K:=K)).mono fun i hi=>H _ hi)
  exact ((isBigO_const_of_tendsto (outlay.mp (hJ.lead _ D V j K hc hz)) one_ne_zero).add hr).congr_left (fun i=>sub_add_cancel ..)
include P
variable (ht:Tendsto t late (𝓝 0))
local notation "Z" => fun (r:ℝ)(i:Fin n)=> stand (A (D i) (t r)) (v i)
include ht D v
lemma sands (q:Bf) : Tendsto (fun i=>coordinates q (Z i)) late (𝓝 (coordinates q v)) := by
  unfold coordinates; refine tendsto_finsetProd _ (fun i _=>?_)
  have h:= continuous_component (q i) (v i) |>.continuousAt (x:=0) |>.tendsto.comp ((P.enough (D i)).comp ht)
  simp only [Function.comp_def, LinearEquiv.symm_apply_apply,map_zero,Submodule.coe_zero,LinearMap.zero_apply] at h
  simp_rw [stood,map_add]; simpa only [add_zero] using! (tendsto_const_nhds (x:=coord (q i) (v i))).add h
lemma refund (j:ℕ) (q:Bf) :
    (fun i:ℝ×Points n=> (coordinates q (Z i.1)-coordinates q v) • iteratedFDeriv ℝ j (measured U none (J i.1) (price (word q)) i.1) i.2)=o[H'T] Pose.home := by
  have h := sands U J Y N t hJ P v hc hz ht q
  have h0 : Tendsto (fun i=>coordinates q (Z i)-coordinates q v) late (𝓝 0) := by simpa only [sub_self] using h.sub (tendsto_const_nhds (x:=coordinates q v))
  exact (((isLittleO_one_iff ℝ).mpr (h0.comp tendsto_fst)).smul_isBigO (holding U J hJ (word q) hc hz j)).congr_right fun _=> one_smul _ _
lemma allotted (j:ℕ) : TendstoUniformlyOn (fun r=>iteratedFDeriv ℝ j (measured U none (Y r) (price v) r)) (iteratedFDeriv ℝ j (WickGoal (price (C:=C) v))) late K := by
  let w r x:= iteratedFDeriv ℝ j (measured U none (J r) (price v) r) x; have h := Filter.eventually_all.mpr (fun i:Fin n=> P.relates (D i))
  have z := IsLittleO.sum (s:=Finset.univ) (fun q (_:q∈(Finset.univ:Finset Bf))=> refund U J Y N t hJ P v hc hz ht j q); rw [outlay]; have h2:=outlay.mp (hJ.lead n D (price v) j K hc hz)
  have hu : (fun i:ℝ×Points n=> iteratedFDeriv ℝ j (measured U none (Y i.1) (price v) i.1) i.2 - w i.1 i.2)=o[H'T] Pose.home := z.congr' ?_ (EventuallyEq.refl ..)
  · have V:= ((isLittleO_one_iff ℝ).mp hu).add h2; rw [zero_add] at V; exact V.congr (fun i=> sub_add_sub_cancel ..)
  filter_upwards [tendsto_fst.eventually h,tendsto_fst.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ))), placed] with i hi e z
  have he : measured U none (Y i.1) (price v) i.1 = measured U none (J i.1) (price (Z i.1)) i.1 := by
    funext x; unfold measured; congr 1; funext j; exact hi j (v j)
  unfold w; rw [he,jets U J (Z i.1) e j (hz z),jets U J v e j (hz z),← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _=>sub_smul ..)
omit hc hz v D
theorem Realized.leading : Leading U Y := by
  have e (d:ℕ) := (reapply U J Y N t hJ P d).mono fun r h=> And.intro (earned_leads U Y h).1 (earned_leads U Y h).2
  constructor; exact fun d => (e d).mono fun r h=> h.1
  exact fun {d} {a} h=> (e a).mono fun r he=> he.2.1 d h
  exact fun d=> (e d).mono fun r h=>h.2.2
  intro n d v j K h hz
  let u i := Free.fields C.labels (d i) (v i); rw [show v= price u from funext fun i=> Eq.symm ( (Free.fields C.labels _ ).symm_apply_apply _ ) ]; exact allotted U J Y N t hJ P u h hz ht j
end YM.FVA2.GradedFar259.Quotes
