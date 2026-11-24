import YM.GradedFar.Batch
import YangMills.WilsonProof.NativeSupport.Commissioned140.AppointedOrdinaryScope.Subarray
/-!
# Special cases for the *physical inputs* of the PoseFit data

It suffices to have supplies at positive caps & arity. Prove normal-order
unity/empty cases on the ACTUAL W assuming only unit convention. Doesn't
use any operator estimates. `gg` etc reported in this file require same
weeks. cf. paper's final conclusion prologue.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Neighbor
open YM.Integration.GradedFar.Tariff
open YM.Integration.GradedFar.Tariff.Playbill
open YM.Integration.GradedFar.Tariff.Crosser
open YM.Integration.GradedFar.Tariff.Billboard
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (J:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
    {t:ℝ→ℝ}{n m h p:ℕ}
local notation "g∴"=> strength G
local notation "After"=> Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "mark"=> Neighbor.stamp G
local notation "wall"=> outgoing RootG
include H
lemma start_small {x:Points n}(hx:x∈conf n)(u:ListInput G n h)(he:∀ i,u i=leaf G h) : sent Before h x u = 1:=by
 ext k; rw [cashed Before u hx]
 let v : Fin 0 ↪ Fin n := ⟨Fin.elim0,fun i=> i.elim0⟩
 let u' : ListInput G 0 h:= fun i=> u (v i)
 let p : Stage 0:= ⟨keptPoints v x,fun i=> i.elim0⟩
 have h₁: Before h n ⟨x,hx⟩ k u=Before h 0 p k u':= start_units v Z H k h u (fun i _=>he i) ⟨x,hx⟩
 have h₂:= congrArg (coeff k) (outlook_empty Z H p u')
 rw [Reg.Point.story, coeff_mk, Scale.Measure.outlook, actMark,status_empty] at h₂
 exact h₁.trans h₂
omit H
include F in
lemma emptyActual (h:ℕ):∀ {n:ℕ}(x:Points n), x∈ conf n → S.useAt S x (fun _=> ⟨h,S.unit h⟩)=1:= by
 intro n; induction n with
 | zero => intro x hx; unfold useAt classMoment; exact F.room.kernel.laws.trivial (fun (i:Fin 0)=>⟨h, S.representative h (S.unit h)⟩) x
 | succ n ih => intro x hx; rw [show (fun (_:Fin (n+1))=> (⟨h,S.unit h⟩:S.Tag))= Fin.cons ⟨h,S.unit h⟩ (fun _=> ⟨h,S.unit h⟩) from funext (fun i=> Fin.cases (Eq.refl _) (fun _=>by rw [Fin.cons_succ]) i), S.at_unit F.room.kernel.laws hx _ h]; exact ih _ (Points.tail_in hx)
lemma frank_empty {r:ℝ}{x:Points 0}(u:ListInput G 0 h): frank F J none h r x u=1:=by
 rw [frank_use]; have hx : r • x ∈ conf 0:= fun i=> i.elim0; exact (congrArg (S.useAt S (r•x)) (Subsingleton.elim (fun i=>(⟨h,assign J r h (u i)⟩:S.Tag)) _)).trans (emptyActual F h _ hx)
lemma frank_unit {r:ℝ}{x:Points n}(hr:0<r)(H:assign J r h (leaf G h)=S.unit h)(hx:x∈conf n): frank F J none h r x (fun _=> leaf G h)=1:=by
 simp_rw [frank_use,H]; exact emptyActual F h _ (Work.A05.smul_conf hr hx)

include F in
lemma sub_grade (hG:G.Simple) {r:ℝ} (hr:assign J r h (leaf G h)=S.unit h)(hv:h<4)(u:Sec G h): ∃ c:ℂ,c • leaf G h=u:= by
    have hT := F.phase.transport.comparator; obtain ⟨_,U⟩ := hT; obtain ⟨X,_⟩ := U h
    have hp : Module.finrank ℂ (S.Field h)=1 := X.finrank_eq.trans (UVNext.FreeStress.dim_before C.book.grid hG hv)
    obtain ⟨c,hc⟩:= (finrank_eq_one_iff_of_nonzero' (S.unit h) (S.alive _ F.room.kernel.laws)).1 hp (assign J r h u)
    exact ⟨c,(assign J r h).injective (by rw [map_smul,hr,hc])⟩

lemma mul_sent (A:Arenas G)(t:ℝ) (l:ℕ) (p:Fin n→ℂ) (x:Points n)(v:ListInput G n h): appointedH140Crop l t (sent A h x (fun i=> p i • v i))=
    (∏ i, p i)*appointedH140Crop l t (sent A h x v):= by
    simp_rw [crop_eq,sent,coeff_mk, MultilinearMap.map_smul_univ]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> by simp only [smul_eq_mul]; ring
lemma crop_one (q:ℕ)(t:ℝ) : appointedH140Crop q t 1=1:=by simpa only [map_one] using constant_crop q t 1
include H
lemma paid_sub {r:ℝ}{x:Points n}(hp:assign J r h (leaf G h)=S.unit h)(hx:x∈conf n)(hr:0<r)(u:ListInput G n h)
    (hz:h<4)(p:ℕ)(t:ℝ): frank F J none h r x u=appointedH140Crop p t (sent Before h x u):=by
 let v : ListInput G n h:= fun i=> leaf G h; choose c hc using fun i=> sub_grade F J hG hp hz (u i)
 have hu:u=(fun i=> c i • v i):=funext fun i=>(hc i).symm; rw [hu,MultilinearMap.map_smul_univ,mul_sent,frank_unit F J hr hp hx,start_small Z M H hx v (fun _=>rfl),crop_one]; rfl
lemma mixed_zero (hv:∀ᶠ r in trail, assign J r 0 (leaf G 0)=S.unit 0): JointTicket F J Z 0:=by
 refine ⟨0,(fun _=>0),fun _=>1,fun _=>1,⟨tendsto_const_nhds,?_,?_,?_⟩⟩
 · rw [show (fun (_:Route)=>mark 0 1)=fun _=>1 from funext (fun _=>stamp_one)]; exact tendsto_const_nhds
 · rw [show (fun (_:Route)=>mark 0 1)=fun _=>1 from funext (fun _=>stamp_one)]; exact tendsto_const_nhds
 intro v w; refine ⟨0,le_rfl,(show ∀ᶠ i in clock, _ from ?_).filter_mono (show upGauge≤ clock from inf_le_left)⟩
 filter_upwards [running.eventually hv,nextPath.eventually hv,running.eventually (show ∀ᶠ r in trail, 0 < r from self_mem_nhdsWithin)] with i hr hs hi
 obtain ⟨c,hc⟩:= sub_grade F J hG hr zero_lt_four v; have hh:adapted J 0 i v = v:= by
    rw [← hc,map_smul]; refine congrArg (fun v:Sec G 0=> c • v) ?_; apply (assign J i.1 0).injective; change assign J i.1 0 (relative J i.1 (next i) 0 (Level.Dial 0 (Real.log (stretch i)) (leaf G 0)))= assign J i.1 0 (leaf G 0); rw [atHome,Level.Dial_leaf, show assign J i.1 0 _=_ from hr,show assign J (next i) 0 _=_ from hs]
 change ‖shared F J 0 i v w - appointedH140Crop 0 0 (sent Before 0 _ (carpet 0 v w))‖ ≤ _; rw [shares,hh,paid_sub F J Z M H hr ok_wall hi _ zero_lt_four 0 0, sub_self,norm_zero,zero_mul]

include H in
private lemma portalVac {X I:Type*} {u:Filter X} {W:X→I→Prop} {r:X→ℝ} {z:X→I→Points n} (hr:Tendsto r u trail)(ht:Coupling G t)
    (he:n=0 ∨ h=0) (hv:∀ᶠ r in trail, assign J r 0 (leaf G 0)=S.unit 0) (hW:∀ᶠ x in u,∀ i,W x i→ z x i ∈ conf n): Portal F J Z u W r z t h p := by
    refine ⟨p,t∘r,fun _=>1,le_rfl, (Coupling.conforms hG ht).comp hr,⟨0,by simp⟩,?_,?_⟩
    · intro v a; exact ⟨0,le_rfl,by simp⟩
    intro v; refine ⟨0,le_rfl,?_⟩; filter_upwards [hr.eventually hv,hW,hr.eventually (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin)] with x hq hz hr' i hi
    rw [show (fun j=> (1:Sec G h→ₗ[ℂ] Sec G h) (v j))=v from rfl, zero_mul]; rcases he with he|he
    · subst n; rw [frank_empty, start_small Z M H (hz i hi) v (fun i=>i.elim0),crop_one,sub_self,norm_zero]
    subst h; rw [paid_sub F J Z M H hq (hz i hi) hr' _ zero_lt_four p (t (r x)),Function.comp_apply,sub_self,norm_zero]
lemma census (ht:Coupling G t) (hv:∀ᶠ r in trail, assign J r 0 (leaf G 0)=S.unit 0)
    (hc:∀ h:ℕ,0<h→ JointTicket F J Z h) (he:∀ (n h:ℕ), 0<n→0<h→fixedPose F J Z t h n) (hz:∀ {n m:ℕ},∀ (K:Set (Points n))(N:Set (Points m)){U B:ℝ}, IsCompact K→ K ⊆ conf n→ IsCompact N→ N ⊆ Outside m→ 0 < U→ 0<B→ 0<n+m→∀ (p h:ℕ),0<h→GridPose F J Z t K N h U B p):
    Pose F J Z t:=by
    refine ⟨ht,?_,?_,?_⟩
    · intro n h; by_cases he': n=0 ∨ h=0
      · intro K _ hx j; exact portalVac F J Z M H tendsto_id ht he' hv (Eventually.of_forall (fun x (i:↥K) _=>hx i.property))
      exact he n h (Nat.pos_of_ne_zero (not_or.mp he').1) (Nat.pos_of_ne_zero (not_or.mp he').2)
    · intro h; rcases h with _|h; exacts [mixed_zero F J Z M H hv,hc _ (Nat.succ_pos _)]
    intro m n h K N U B hU hB hK hx hN h' p; by_cases hp:n+m=0 ∨ h=0
    · -- note {m n} order in structure! check.
      intro K' N' hK' hx' hN' hm _ _ j hj; refine ⟨fun _=>Set.univ,⟨1,zero_lt_one,?_⟩,?_⟩
      · filter_upwards [poses (strength_positive hG)] with p h q _; exact ⟨q,mem_univ _,by rw [one_mul,sub_self,norm_zero]; positivity⟩
      exact portalVac F J Z M H rising ht hp hv (Road.funded_forms hK' hx' hN' hm (fun _ _ h=> h.2))
    exact hz K N hK hx hN h' hU hB (Nat.pos_of_ne_zero (not_or.mp hp).1) _ _ (Nat.pos_of_ne_zero (not_or.mp hp).2)
end YM.Integration.GradedFar.Batch
