import YM.FullVolume.Profiles
import YM.Integration.WilsonMeasuredSpatialModulus
import YM.SignedWilsonExpansion.Homes.Tactics
import YM.Dash.Regular

/-! Recover the generic limits on the auxiliary full UV then eligible periods order.

Strong limits off coincidence on the cover. Include ties in our reading, still
use exactly the microscopic lift and holding periods fixed through UV. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open FullVolume Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open PhysicalNext.Repeat.Legato
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}

section full
variable (hV:PositionsUV C Extraction.Sequence.full)
theorem periodUsable {n p:ℕ} {v : Fin n → C.book.Token}
   {X : Points n→ℂ} (hp: Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p v) X)
   (K:Set (Points n)) (hK:IsCompact K) (hC: K ⊆ NoHit C.S p n) (ε:ℝ) (ep:0<ε):
   ∀ᶠ i in atTop, ∀ r : Fin n → Cover, Order.grid C i r ∈ K →
      ‖(C.numeric i p v (fun j => wrap _ (r j))) - X (Order.grid C i r)‖ < ε := by
   change ∀ᶠ i in atTop, ∀ r : Fin n → Cover, tag (C.S.a i) r ∈ K →
      ‖lifted C i p v r - X (tag (C.S.a i) r)‖ < ε
   by_contra! hi
   obtain ⟨s,hs,h⟩:= extraction_of_frequently_atTop hi; choose y hy hF using h
   obtain ⟨x,hx,w,hw,hW⟩:= hK.tendsto_subseq hy
   have H:=hp.2 x (hC hx) (fun i=>y (w i)) (s ∘ w) (hs.tendsto_atTop.comp hw.tendsto_atTop) hW
   have ht:=((hp.1.mono hC x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hW,Eventually.of_forall (fun i=> hy (w i))⟩))
   have hm: Tendsto (fun i=> ‖lifted C (s (w i)) p v (y (w i))- X (tag (C.S.a (s (w i))) (y (w i)))‖) atTop (𝓝 0) := by
      have HE := (H.sub ht).norm
      rw [sub_self,norm_zero] at HE
      exact HE
   obtain ⟨i,hi⟩:=(hm.eventually (gt_mem_nhds ep)).exists
   exact (hF (w i)).not_gt hi

include hV
theorem whole (Z:f.PointLimits C S) : (track f).PointLimits C S := by
   obtain ⟨P,H,V⟩:=Z; refine ⟨P,⟨H.continuous,?_⟩,V⟩
   intro p n K hK h v ε ep
   obtain ⟨X,hX,-,T'⟩:=hV p n v
   have T : Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p v) X:=(T' []).1
   have he (x) (hx:x∈ Cyclic C.S p n) : x∈NoHit C.S p n :=fun i j hj=> ⟨0,hx i j hj _⟩
   have hu : ∀ x∈ Cyclic C.S p n, (P p).read x v=X x := by
      intro x hx
      have hr:= Extraction.chosen (S:=C.S) x |>.comp f.mesh.cofinal
      have hv:= f.evaluated C H p n v x hx (fun i=> address (C.S.a (f.mesh i)) x) hr
      exact tendsto_nhds_unique hv (T.2 _ (he x hx) _ f.mesh f.mesh.cofinal hr)
   filter_upwards [periodUsable T K hK (h.trans fun x hx=> he x hx) ε ep] with i ht r hr
   rw [hu _ (h hr)]
   exact ht _ hr
end full
open Metric Extra.WeakScaling Integration

/- Proof of measured compact transfer, same as `WilsonMovingCompactTransfer`,
now ONLY needs the full Track Generic. -/
section measured
variable (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book}
include hG in
theorem bright (SM:S.Smooth) (X:f.PointLimits R.family S) (v : Fin n → R.family.book.Token)
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ×ℕ in f.fuse, ∀ z : Positions n, tag (R.family.S.a i.1) z ∈ K →
      dist (lifted R.family i.1 i.2 v z) (S.read (tag (R.family.S.a i.1) z) v) < ε := by
  let C := R.family
  obtain ⟨a,B,ha,hB,all⟩ := WilsonMeasuredSpatialModulus.purchased R hG f v K hk sep
  have near (x : K) : ∃ η : ℝ, 0<η ∧ ∀ᶠ i : ℕ×ℕ in f.fuse, ∀ z : Positions n,
      tag (C.S.a i.1) z ∈ K → dist (tag (C.S.a i.1) z) x.val < η →
      dist (lifted C i.1 i.2 v z) (S.read (tag (C.S.a i.1) z) v) < ε := by
    have c : ContinuousAt (fun u => S.read u v) x.val :=
      ((S.smooth_read SM v).continuousOn x.val (sep x.property)).continuousAt
        ((conf_open _).mem_nhds (sep x.property))
    obtain ⟨δ,hδ,hD⟩ := Metric.continuousAt_iff.mp c (ε/4) (by positivity)
    let η := min (a/4) (min (δ/2) ((ε/16)/(1+B)))
    have hden : 0<1+B := by linarith
    have hη : 0<η := lt_min (by positivity) (lt_min (by positivity) (div_pos (by positivity) hden))
    have aa : η ≤ a/4 := min_le_left _ _
    have dd : η ≤ δ/2 := (min_le_right _ _).trans (min_le_left _ _)
    have small : η*(1+B) ≤ ε/16 :=
      (le_div_iff₀ hden).mp ((min_le_right _ _).trans (min_le_right _ _))
    have density : Dense (generic n) := Dash.full n
    obtain ⟨xg,hg,close⟩ := Metric.mem_closure_iff.mp (density x.val) η hη
    have distg : dist xg x.val < η := by simpa only [dist_comm] using close
    let y (N : ℕ) := address (C.S.a N) xg
    have round : Tendsto (fun N => tag (C.S.a N) (y N)) atTop (𝓝 xg) := chosen xg
    have here := points_approach X hg round v
    have fit := ((round.comp (cofin_fst f)).eventually (Metric.ball_mem_nhds xg hη))
    have moment := here.eventually (Metric.ball_mem_nhds (S.read xg v) (show 0<ε/4 by positivity))
    refine ⟨η,hη,?_⟩
    filter_upwards [all,fit,moment] with i bill landed tested z hz hx
    let t := C.S.a i.1
    have hy : dist (tag t (y i.1)) xg < η := landed
    have hv : dist (lifted C i.1 i.2 v (y i.1)) (S.read xg v) < ε/4 := tested
    have walk : dist (tag t (y i.1)) (tag t z) ≤ 3*η := by
      have via := dist_triangle (tag t (y i.1)) xg x.val
      have back := dist_triangle (tag t (y i.1)) x.val (tag t z)
      rw [dist_comm x.val (tag t z)] at back
      linarith
    have quote := bill z (y i.1) hz (walk.trans (by linarith))
    rw [dist_comm] at quote
    have fee : dist (lifted C i.1 i.2 v z) (lifted C i.1 i.2 v (y i.1)) ≤ B*(3*η) :=
      quote.trans (mul_le_mul_of_nonneg_left walk hB)
    have cx : dist (S.read xg v) (S.read x.val v) < ε/4 := hD (by linarith : dist xg x.val < δ)
    have cz : dist (S.read (tag t z) v) (S.read x.val v) < ε/4 := hD (by linarith : dist (tag t z) x.val < δ)
    have h₁ := dist_triangle (lifted C i.1 i.2 v z) (lifted C i.1 i.2 v (y i.1)) (S.read xg v)
    have h₂ := dist_triangle (lifted C i.1 i.2 v z) (S.read xg v) (S.read x.val v)
    have h₃ := dist_triangle (lifted C i.1 i.2 v z) (S.read x.val v) (S.read (tag t z) v)
    rw [dist_comm (S.read x.val v) (S.read (tag t z) v)] at h₃
    change dist (lifted C i.1 i.2 v z) (S.read (tag t z) v) < ε
    nlinarith only [fee,hv,cx,cz,h₁,h₂,h₃,small,hη,he]
  choose η hη purchased using near
  have covers : K ⊆ ⋃ x : K, ball x.val (η x) := by
    intro z hz; exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (hη _)⟩
  obtain ⟨s,hs⟩ := hk.elim_finite_subcover (fun x : K => ball x.val (η x)) (fun _ => isOpen_ball) covers
  filter_upwards [(eventually_all_finset s).mpr (fun x _ => purchased x)] with i hi z hz
  obtain ⟨x,hxs,he⟩ := mem_iUnion₂.mp (hs hz)
  exact hi x hxs z hz he

end measured
section ties
variable (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} (hS:S.Smooth) (H:f.PointLimits R.family S)
include hG hS H
open Integration
open Extra.WeakScaling
/-- Includes non-generic fixed targets. Still an ordered (not fused) limit. -/
theorem two_approach (hV:PositionsUV R.family Extraction.Sequence.full)
   (x:Points n) (hx:x∈conf n) (r:ℕ→Positions n)
   (hr:Tendsto (fun N=> tag (R.family.S.a N) (r N)) atTop (𝓝 x)) (v : Fin n → R.family.book.Token) :
    (track f).limits
      (fun p=> x∈NoHit R.family.S p n)
      (fun N p=> lifted R.family N p v (r N))
      (S.read x v) := by
   let C:=R.family
   let zv(N):= tag (R.family.S.a N) (r N)
   choose F hf _ hb using fun p => hV p n v
   have FG(p):Cluster C Extraction.Sequence.full p n (fun N=> lifted C N p v) (F p):=hb p []|>.1
   refine Order.from_late (f:=track f) (A:=fun p => x ∈ NoHit R.family.S p n)
     ?_ (W:=fun N p=>lifted R.family N p v (r N)) (fun p=>F p x) ?_ ?_
   · filter_upwards [(track f).per.cofinal.eventually (room R.family.S (K:={x}) isCompact_singleton)] with p hi
     exact (no_wrap_hit C.S (hi (mem_singleton _))).2 hx
   · intro p hp; exact (FG p).2 x hp r id tendsto_id hr
   · intro s hs
     obtain ⟨K,hK,hI,hU⟩:=exists_compact_subset (conf_open n) hx
     have ht: Tendsto (fun N=> S.read (zv N) v) atTop (𝓝 (S.read x v)) :=
       (((S.smooth_read hS v).continuousOn.continuousAt ((conf_open _).mem_nhds hx)).tendsto.comp hr)
     obtain ⟨ε,ep,hε⟩:= Metric.mem_nhds_iff.mp hs
     have hk:= bright R hG hS (whole hV H) v K hK hU (ε/2) (half_pos ep)
     change ∀ᶠ i in (track f).fuse, lifted R.family i.1 i.2 v (r i.1) ∈ s
     filter_upwards [hk,(cofin_fst (track f)).eventually (ht.eventually (Metric.ball_mem_nhds (S.read x v) (half_pos ep))),
       (cofin_fst (track f)).eventually (hr.eventually (mem_interior_iff_mem_nhds.mp hI))] with i e μ ν
     apply hε; apply lt_of_le_of_lt (dist_triangle _ (S.read (zv i.1) v) _)
     have G:= add_lt_add (e _ ν) (show dist (S.read (zv i.1) v) (S.read x v)< ε/2 from μ); rwa [add_halves] at G
end ties

end YM.SignedWilsonExpansion.Homes
