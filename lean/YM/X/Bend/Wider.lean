import YM.X.Bend.Weigh
/-!
# regulator X_κ. eventually positive tangent; no assumptions.Field-h.Snapshot. finite n array addresses.Reader proving proper reparameterization and its converging 1-jet. Profile derivative of field renorm unconstrained.House.All under b membership.D.Mon.Attach.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Maxwell Set Function MeasureTheory Lattice Wilson Next.Rank Labels Pert.Position
open Maxwell.Free Filter Metric Chir Sage Tri Ribbon Extra.FD Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d e k m:ℕ} {q:ℕ+}{V I:Type*}{r R:ℝ}
local notation "K"=>(atTop:Filter ℕ)
variable (B:Bare.Shop F) (q:ℕ+)(hg:G.Simple)
local notation "Z"=> Bank F d
local notation "W"=>Word ℝ
abbrev curveF (A:Booth r F) (k:ℕ): W:= metricT A (B.uncut hg q k 6)
def stampT (A:Booth r F)(k:ℕ):= Jet.inverse (curveF B q hg A k)
abbrev renormal (A:Booth r F)(k d:ℕ): Word (Bank F d):= Jet.ren (stampT B q hg A k) (B.uncut hg q k d)
-- Phase.H.State.
variable (A:Booth r F)(hq:1<q.val) (hw:BeaconTest B hq hg A)
local notation "θ"=> renormal B q hg A
local notation "p"=> curveF B q hg A
local notation "U"=> stampT B q hg A
local notation "R₀"=> pureBank F d
local notation "X"=> firstX B q hq hg d
local notation "D"=> nested F hg B d
set_option quotPrecheck false
@[simp] lemma phase_live : light (U k):= Jet.lives ..
include hw
lemma cert : Tendsto (fun i=> p i 1) K (𝓝 1):= meter_tip B hq hg A hw -- issue include
lemma ideal_enter : ∀ᶠ k:ℕ in atTop,p k 1>1/2:= (cert B q hg A hq hw).eventually (lt_mem_nhds (by norm_num))
lemma well : ∀ᶠ k:ℕ in atTop,Genuine (p k):= (ideal_enter B q hg A hq hw).mono fun i hi=> ⟨metric_zero .., ne_of_gt (lt_trans (by norm_num) hi)⟩
lemma inverse_tip : Tendsto (fun i=> U i 1) K (𝓝 1):= by
   have he:= (cert B q hg A hq hw).inv₀ one_ne_zero; rw [inv_one] at he; exact he.congr' ((well B q hg A hq hw).mono (fun i hi=> (tip_inv hi).symm))
lemma canonical : ∀ᶠ i:ℕ in atTop, metricT A (θ i 6) = headway := (well B q hg A hq hw).mono (fun i hi=> Ψcalibrated A _ hi) -- arguments
lemma back_l (v:Pert.Position.Section F d) : ∀ᶠ i:ℕ in atTop,(lookie F v ∘ B.uncut hg q i d) = ren (p i) (lookie F v ∘ θ i d):= by
    filter_upwards [well B q hg A hq hw] with i hi; unfold renormal; rw [ren_writes,Jet.asc hi.1 (phase_live ..),show ren (p i) (U i)= _ from headback hi, ren_head]
omit hw
include hq
lemma θ_up (he:d≤e): ∀ᶠ i:ℕ in atTop,pulls (up F he) ∘ θ i e= θ i d:= by
    filter_upwards [B.uncut_up hg q hq he] with i hi; unfold renormal; rw [ren_writes (pulls _),hi]
-- maintains D-target. commute.
lemma θ_report (d:ℕ) : ∀ᶠ i:ℕ in atTop, (nested F hg B d).D ∘ (θ i d)=just ((nested F hg B d).D (pureBank F d)):= by
     filter_upwards [B.chamber hg q hq d] with i hi; unfold renormal; rw [ren_writes]; change ren _ ((nested F hg B d).D ∘ _) = _; rw [show ((nested F hg B d).D) ∘ B.uncut hg q i d= just ((nested F hg B d).D (pureBank F d)) from hi.1]; exact ren_static ((nested F hg B d).D (pureBank F d)) (phase_live (k:=i) B q hg A)
lemma κ_odd : ∀ᶠ k:ℕ in atTop, turn (p k)= -(p k):=(B.uncut_par hg q hq 6).mono fun i hi=> meter_odd A _ hi
omit hq in
lemma spinCommute {Y:Type*}[AddCommMonoid Y][Module ℝ Y](f:Z→ₗ[ℝ] Y)(w:Word Z): turn (f ∘ w)= f ∘ turn w:= funext (fun i=> Eq.symm (map_smul f ..))
include hw
lemma θ_odd_inv : ∀ᶠ k:ℕ in atTop,turn (U k)=-(U k):= ((well B q hg A hq hw).and (κ_odd B q hg A hq)).mono fun i hi=> invert_odd hi.1 hi.2
lemma θ_par : ∀ᶠ k:ℕ in atTop, pulls (par F d) ∘ θ k d = turn (θ k d):= by
    filter_upwards [θ_odd_inv B q hg A hq hw,B.uncut_par hg q hq d] with k hk hi; unfold renormal; rw [ren_writes,hi]; let w:=B.uncut hg q k d; let v:=U k; have hv: light v:= phase_live ..
    funext i; funext n t; apply MultilinearMap.ext; intro b; let F':=lookie F ⟨n,b,t⟩; have h : F' ∘ ren v (turn w)= F' ∘ turn (ren v w):= by rw [ren_writes, ← spinCommute,ren_turn_v _ hv,←spinCommute,ren_writes, ← hk,ren_turn_x _ hv]
    exact congr_fun h i
local notation "ϵ"=> firstX B q hq hg
omit hw
lemma leading_edge (v:Pert.Position.Section F d): Tendsto (fun i=>lookie F v (θ i d 0)) atTop (𝓝 (lookie F v R₀)):= by
    have h(i):lookie F v (θ i d 0)=_:= (congr_fun (ren_writes (lookie F v) (U i) (B.uncut hg q i d)) 0).trans (ren_light (phase_live ..) _); simp_rw [h]; exact full_stick B hq hg v
omit hq in
lemma θ_real (i n k:ℕ): House (θ i n k):= by
   unfold renormal ren; apply Hscale; let s:= Finset.univ (α:=OrderedFinpartition k); let f(x:OrderedFinpartition k):= Jet.order x (U i) (B.uncut hg q i n); suffices h:∀ t: Finset (OrderedFinpartition k),House (∑ j∈t,f j) by exact @h s
   intro t; induction t using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; apply Hcollect
   | insert j t he ht=> rw [Finset.sum_insert he]; refine @Hplus _ _ _ (f j) _ ?_ ht; unfold f Jet.order; apply Hscale; apply Hscale; apply layout_real
include hw
lemma crown_endpoint (v:Pert.Position.Section F d) : Tendsto (fun i=> lookie F v (θ i d 1)) atTop (𝓝 (lookie F v X)):= by
    have h(i):lookie F v (θ i d 1)=_:= (congr_fun (ren_writes (lookie F v) (U i) (B.uncut hg q i d)) 1).trans (tip (phase_live ..) _); simp_rw [h]; simpa using! (inverse_tip B q hg A hq hw).smul (limit₁ B q hq hg v)
end YM.PositionX.Bend
