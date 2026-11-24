import YM.LocalLTE.Sail.Reserve
import YM.LocalLTE.Port.Page
/-!
# Allocating newborn true mark probes on the concrete epoch.

No demand on d labels used. Valid outfits consumed by packing portions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open GridApprox.Nil Extra.Trajectories Progress.DirectedRecipe MergeProof Accent Push.AbsoluteSums Shelf
open Overlay Planned.GuardedAtom Guard
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type} [DecidableEq V] [Fintype V]
variable (B:Census V) {G:Gauge}{n:Side} (P:Rep G n) (o:V→Site n)
section
variable (K:Keeper P.p P.activities)(j₀:V) (F: Box n→ Config G n→Marker.Poly B)
    {w:V→ℝ}{v k :ℝ}
def hull : Bands B P:= ⟨o,0,(fun _=>{o j₀}),fun _=>B.fire j₀,0,fun _ _=>B.fire j₀,0⟩
local notation "L"=> hull B P o j₀
abbrev frontier := XPhase.shelve B P j₀ K F (L)
/-- Forecast at summit on same tag layout, takes F0 in Coat. `shelve`s even empty.` -/
abbrev priorP := XPhase.shelve B P j₀ K (fun _ _=> (0:Poly B)) (L)
local notation "A"=> frontier B P o K j₀ F
local notation "Q"=> priorP B P o K j₀
omit [Fintype V] in
lemma oct_zero : octave (0:Poly B)=0:=by
    ext i; by_cases hi:2≤ i.val.card; exact crest _ _ hi; exact starlet _ _ (lt_of_not_ge hi)
-- purchase at every chosen p.B.C
variable (hp:∀ i,Flow o i (F i) P.p.threshold)(hr:∀ i U,rises (F i U))(he:Towed w Prod.fst F P.p.B P.p.supportExponent (v*k))(hw:∀ i,0<w i)
include hp hr he hw
lemma hull_receipts (hk:0<k): (Q).Active ∧ (Q).Radial w 0 0 0 k ∧ Fan.Tabs P B (A) Q (A) ∧ (A).Active ∧ (A).Radial w 0 0 v k ∧ (∀ i l κ, Port.Shine B Q i l κ) ∧ (∀ U, (∑' i, (A).ray i U)=0) ∧ XPhase.lightF B P (A)=F∧ (A).origins=o ∧ (A).H=0 ∧ (∀ i j,(A).entries i j≠0→ 2 ≤ ((A).marks i j).val.card):=by
    have hL:(L).Active:=by
       refine ⟨fun i=> Finset.singleton_nonempty _,fun i j ht=>?_ ,fun i=>Push.Local.regular_const _,fun i j=> Finset.singleton_nonempty _,fun i j h=> (h rfl).elim,fun i j x y _ _=> rfl,fun i j x h=> False.elim (h rfl),fun i j=> measurable_const,fun i j k U=>rfl⟩
       change _∈{o j₀}; rw [show j=j₀ from Finset.mem_singleton.mp ht]; simp [hull]
    let F₀: Box n→ Config G n→ Marker.Poly B:= fun _ _=>0
    have h0(i):Flow o i (F₀ i) P.p.threshold:=⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun _ h=> False.elim (h rfl)⟩
    obtain ⟨hA,hI⟩:= XPhase.roomH B P j₀ K F (L) hp hL
    have hQ:(Q).Active:= (XPhase.roomH B P j₀ K F₀ (L) h0 hL).1
    have hQQ:(Q).entries=0:=by
       funext i j U; change _ = (0:ℂ); let J:= XPhase.reserveIX B
       by_cases he:j∈Set.range J; swap;· rw [show (Q).entries i j=0 from XPhase.tagged_v B P j₀ K _ (L) _ _ he]; rfl
       obtain ⟨j,rfl⟩:=he; rw [show (Q).entries i _ = _ from (XPhase.tagged_b B P j₀ K F₀ (L) i j).2]; dsimp only
       by_cases he:i∈Set.range (cart K); · obtain ⟨i,rfl⟩:=he; rw [XPhase.cachet,stuffed];rfl
       rw [XPhase.cachet, blank _ _ he];rfl
    have hQ': (Q).Radial w 0 0 0 k:=by
       refine ⟨hw,fun j=>?_,hk,⟨fun _=>0,fun i=>⟨le_rfl,fun j h=> ?_⟩,fun i=>?_⟩,fun _=>0,fun i j=> ⟨le_rfl,fun x=>?_⟩, fun i=>?_⟩
       · change w _* ‖(0:ℂ)‖ ≤(0:ℝ); simp
       · change P.p.supBounds (o j) _ (fun _=> (0:ℂ)) _; simpa only [norm_zero] using! Push.Local.bound_const (G:=G) (B:=P.p) (X:=({o j₀}:Support n)) (o:=o j) (0:ℂ)
       · simp only [BudgetPoint.mass,mul_zero,ite_self]; exact ⟨fun _=>le_rfl,summable_zero,by simp⟩
       · simp [hQQ]
       simp only [BudgetPoint.mass,mul_zero,zero_mul,ite_self]; exact ⟨fun _=>le_rfl,summable_zero,by simp⟩
    have hb: (A).Radial w 0 0 v k:= ⟨hw,hQ'.localU,hk,hQ'.bulk, XPhase.carved B P j₀ K F (L) hp hw he⟩
    have hX:Fan.Tabs P B (A) Q (A):= ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hQQ,(show (0:ℕ→ Config G n→ℂ)-0=0 from sub_zero _)⟩
    refine ⟨hQ,hQ',hX,hA,hb,fun i l κ=> ⟨fun i h=> False.elim (h rfl)⟩,fun U=>?_,XPhase.blazing B P j₀ K F (L) hp hr,rfl,rfl,hI⟩
    refine Eq.trans (tsum_congr (g:=fun _:ℕ=>(0:Poly B)) (fun i=>?_)) tsum_zero; unfold Bands.ray; by_cases he: Healthy P.p.threshold ((A).support i) U; rw [masked_eq _ _ _ _ he]; exact Poly.send_zero _
    rw [masked_ne _ _ _ _ he, Poly.send_zero]
end
section
variable (F:V→ Config G n→ℂ) (χ:V→ MergeProof.Response G n)
    {q w: V→ℝ}{a C t v:ℝ} {φ:V→ Config G n→ℂ}{κ:V→ℕ→ Config G n→ℂ}
local notation "K"=> Accent.closure (Accent.exclaim P.activities B) (Accent.conviction χ B) Prod.snd P.p.threshold
abbrev captain (i:Box n) (U:Config G n):Poly B:= Accent.octave (Accent.closure (Accent.exclaim P.activities B) (Accent.conviction χ B) Prod.snd P.p.threshold i U)
variable (h:Garnish P.p o χ w t C)(hr:P.activities.Valid P.p a v)
    (hp:∀ j, Dominated (κ j))(hC:∀ i,profile P.activities (κ i)=hook P.activities P.p.threshold (χ i))
    (ht:∀ i U,(P.eval U:ℂ)*F i U=Accent.coin P (φ i) (κ i) U)
    (hz:∀ U,P.eval U≠0)
include h hr hp hC ht hz
-- actual (not masked birth object). uses profile stamp role.
lemma restart : Carton o (fun _ _=>(0:Poly B)) (captain B P χ) P.p.threshold ∧ Accent.birth B P F=Accent.restore P φ (fun i=>profile P.activities (κ i)) (fun _ _=>0) (captain B P χ):=by
    let L:= Accent.exclaim P.activities B; let f:= fun U:Config G n=> Accent.Mach B (fun i=> F i U)
    have hv(i):Flow o i (L i) P.p.threshold:= Accent.granular _ _ _ hr _
    have hL: ∀ i U,(L i U).part B.quiet= profile P.activities (fun j=> Complex.ofReal ∘ P.activities.K j) i U:=fun i U=> (Poly.part_send ..).trans (if_pos rfl)
    have hT(i):Flow o i ((K) i) P.p.threshold:= threshed _ _ Prod.snd _ hv (dresses χ B h) _
    have hΩ: birth B P F=play P B (K) (f-kelp χ B):= (starting B _ F hr).trans (funext fun i=> reversal P χ L f h hv i (mute B _))
    let H: Support n→ Config G n→Poly B:= fun _ _=>0
    have hu:∀ i,Burns o i (H i) P.p.threshold:= fun i=> ⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun _ hu=>False.elim (hu rfl),fun _=> rfl⟩
    obtain ⟨he,h⟩:=plank P B (K) (f-kelp χ B) φ κ hr (H:=H) (o:=o) (fun i U=> (wine L (conviction χ B) Prod.snd P.p.threshold U i (fun p=>hv p|>.permits U) (corn_quiet χ B U)).trans (hL i U)) (fun U=>by simp only [Pi.sub_apply,f,part_sub,kelp,Poly.part_sum,mute,corn_quiet χ B,sum_const_zero,sub_zero]) hu hT hp (fun i U j=>by rw [posts P χ _ hv hL hr,hC]; change (Poly.send B.quiet _).part _+_= _; rw [Poly.part_send,if_neg (B.fire_hot i),zero_add]) (fun i U=>by rw [← hΩ]; exact (boot B P F U i).trans (ht i U)) hz (fun U p hz=>by simp only [Pi.sub_apply,part_sub,kelp,corn_light χ p hz U,f,hush _ p hz,sub_zero,H,sum_const_zero,Poly.part_nil])
    have hZ:(fun i U=>octave (H i U))=(fun _ _=>0):= funext fun i=> funext fun U=> oct_zero B
    rw [hZ] at he h; exact ⟨he,hΩ.trans h⟩
end
end YM.LocalLTE.Sail
