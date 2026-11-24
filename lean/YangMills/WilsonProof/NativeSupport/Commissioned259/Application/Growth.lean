import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Lamps
/-!
# Transfer Leading on J to W using the leg identities in the prescription.

Estimates hold for other towers too. No claim to obtain J from UV assumptions here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Application
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2.Register
open Dframe O.Score Original Pose ScaleCost
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J Y : ℝ→PhysMS.tower S) (A:∀ d:ℕ,ℝ→Change G d)
local notation "late" => 𝓝[>] (0:ℝ)

-- shrink lift family inputs.All order coherence from adjacent steps sufficient
structure Charges (J Y:ℝ→PhysMS.tower S) (A:∀ d:ℕ,ℝ→Change G d) : Prop where
    relates (d:ℕ) : ∀ᶠ r in late, ∀ v,
      Original.frame Y r d v= Original.frame J r d (stand (A d r) v)
    close (d:ℕ) : Tendsto (fun i=>guide G d (A d i)) late (𝓝 0)
    includes (d:ℕ) : ∀ᶠ i in late, ∀ v, stand (A (d+1) i) (XSpace.Normalize.step d v)=XSpace.Normalize.step d (stand (A d i) v)
variable {A}
variable (P:Charges J Y A) {d n k:ℕ} (V:Leading F J)
include P
lemma reaches (h:k ≤ d) : ∀ᶠ r in late, ∀ v, stand (A d r) (up h v)=up h (stand (A k r) v) := by
  induction d, h using Nat.le_induction with
  | base=> exact Eventually.of_forall fun _ _=>rfl
  | succ i hi ih=> refine (ih.and (P.includes i)).mono fun r ⟨g,h⟩ v=>?_ ; change stand _ ((XSpace.Normalize.step i) (up hi v))=_; rw [h,g]; rfl
include V
lemma covers : ∀ᶠ r in late, Quotes.Earns F Y r d := by
  have h := Filter.eventually_all.mpr (fun i:Fin (d+1)=> Filter.Eventually.and (P.relates i.val) (reaches J Y P (Nat.le_of_lt_succ i.isLt)))
  filter_upwards [Quotes.earnings F J V d,P.relates d, h] with r e h V
  refine ⟨ fun i hi v=>?_,fun v=>?_,fun s v=>?_,?_⟩
  · rcases V ⟨i,Nat.lt_succ_of_le hi⟩ with ⟨Z,H⟩; rw [h,H,e.rises i]; exact (congr_arg _ (Z v)).symm
  · rw [h, ← stood_reel,e.real,h]
  · rw [h, ← stood_ori,e.signed,h]
  rw [h,solitary,e.unit]
open Quotes
-- readiness (including *actual canonical mixed labels* incl. one slots), Leading h transfer
variable {D:Fin n→ℕ}{K:Set (Points n)}(v:Slots G D) (hK:IsCompact K) (hx:K⊆conf n)
local notation "H'T" => booth K late
local notation "Vx" => fun (r:ℝ)(i:Fin n)=> stand (A (D i) r) (v i)
omit V in
lemma nearby (q:BasisSlots G D) : Tendsto (fun i=>coordinates q (Vx i)) late (𝓝 (coordinates q v)) := by
  unfold coordinates; refine tendsto_finsetProd _ (fun i _=>?_)
  have h:= continuous_component (q i) (v i) |>.continuousAt (x:=0) |>.tendsto.comp (P.close (D i))
  simp only [Function.comp_def, LinearEquiv.symm_apply_apply,map_zero,Submodule.coe_zero,LinearMap.zero_apply] at h
  simp_rw [stood,map_add]; simpa only [add_zero] using! (tendsto_const_nhds (x:=coord (q i) (v i))).add h
open Asymptotics
include hK hx
lemma tall (j:ℕ) : TendstoUniformlyOn (fun r=>iteratedFDeriv ℝ j (measured F none (Y r) (price v) r)) (iteratedFDeriv ℝ j (WickGoal (price (C:=C) v))) late K := by
  let w r x:= iteratedFDeriv ℝ j (measured F none (J r) (price v) r) x; have h := Filter.eventually_all.mpr (fun i:Fin n=> P.relates (D i))
  have e (q:BasisSlots G D) : (fun i:ℝ×Points n=> (coordinates q (Vx i.1)-coordinates q v) • iteratedFDeriv ℝ j (measured F none (J i.1) (price (word q)) i.1) i.2)=o[H'T] ( Pose.home ) := by
    have h := nearby (J:=J) (Y:=Y) P v q
    have h0 : Tendsto (fun i=>coordinates q (Vx i)-coordinates q v) late (𝓝 0) := by simpa only [sub_self] using h.sub (tendsto_const_nhds (x:=coordinates q v))
    exact (((isLittleO_one_iff ℝ).mpr (h0.comp tendsto_fst)).smul_isBigO (holding F J V (word q) hK hx j)).congr_right fun _=> one_smul _ _
  have z := IsLittleO.sum (s:=Finset.univ) (fun q _=> e q); rw [outlay]; have h2:=outlay.mp (V.lead n D (price v) j K hK hx)
  have hu : (fun i:ℝ×Points n=> iteratedFDeriv ℝ j (measured F none (Y i.1) (price v) i.1) i.2 - w i.1 i.2)=o[H'T] Pose.home := z.congr' ?_ (EventuallyEq.refl ..)
  · have V:= ((isLittleO_one_iff ℝ).mp hu).add h2; rw [zero_add] at V; exact V.congr (fun i=> sub_add_sub_cancel ..)
  filter_upwards [tendsto_fst.eventually h,tendsto_fst.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ))), placed] with i hi e z
  have he : measured F none (Y i.1) (price v) i.1 = measured F none (J i.1) (price (Vx i.1)) i.1 := by
    funext x; unfold PhysMS.measured; congr 1; funext j; exact hi j (v j)
  unfold w; rw [he,jets F J (Vx i.1) e j (hx z),jets F J v e j (hx z),← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _=>sub_smul ..)
omit hK hx
theorem growing : Leading F Y := by
  have e (d:ℕ) := (covers F J Y P V (d:=d)).mono fun r h=> And.intro (earned_leads F Y h).1 (earned_leads F Y h).2
  constructor; exact fun d=> (e d).mono fun r h=>h.1
  exact fun {d} {a} h=> (e a).mono fun r he=> he.2.1 d h
  exact fun d=> (e d).mono fun r h=>h.2.2
  intro n d v j K h hz
  let u i := Free.fields C.labels (d i) (v i); rw [show v= price u from funext fun i=> Eq.symm ( (Free.fields C.labels _ ).symm_apply_apply _ ) ]; exact tall F J Y P V u h hz j
end YM.FVA2.GradedFar259.Application
