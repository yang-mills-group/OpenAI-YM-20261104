import YM.GradedFar.Round.Gradient

/-!
# Pay any physical oracle at first r-scaled shape gradient
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books
open Scale Dframe
open OPE Orbits Logged OPE.Logged.Deck Horizon
open Logged.Economy (Paint)
open OPE.Log (badge)
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K) (hl: LogTrace U Q.port)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "Φ"=>spectator U
local notation "V"=>U.sector.derivatives
section
variable (D:Deck.Pitch I) (o:I→View U) {M' δ:ℝ}(hm:0≤M')(hd:0<δ)(x:I→Points n)(y:I→Points m)
    (hx:∀ᶠ i in D.p,Terracing (D.r i) (D.s i) M' δ (x i) (y i))
set_option quotPrecheck false
local notation "σ"=>D.s
local notation "ρ"=>D.r
local notation "Ω"=>fun i=>forest (x i) ((σ i/ρ i) • y i)
lemma unscale {x:Points n}{r:ℝ}(hx:r • x∈conf n) : x∈conf n:=fun _ _ h=> hx (congrArg (r • ·) h)
include H hq he hl hm hd hx
lemma lane_gradient (a:I→Tags G h (n+m)) (ha : ∀ i,Paint D.toSmall (fun _=>1) (fun l=>chair G h (a l i))) :
    Paint D.toSmall (fun _=>1) (fun i=> fderiv ℝ (fun z=> painted U K (o i).1 (fun _:Fin (n+m)=>h) (ρ i) z (a i)) (Ω i)) := by
    let L (i:I): Points (n+m) →L[ℝ] ℂ:= fderiv ℝ (fun z=> painted U K (o i).1 (fun _:Fin (n+m)=>h) (ρ i) z (a i)) (Ω i)
    have hh (j:Fin (n+m) × Axis) : Paint D.toSmall (fun _=>1) (fun i=> L i (Points.direction j.1 j.2)) := by
       let V' i:=transferred U K j.1 (a i) j.2 (D.r i)
       have hs v : Paint D.toSmall (fun _=>1) (fun i=> chair G (h+1) (V' i v)) := by
          by_cases hv:v=j.1
          · rw [hv]; unfold V' transferred; simp_rw [update_self]; exact crew N M H U Q J K θ hq he D.toSmall h j.2 (fun i=> a i j.1) (ha _)
          unfold V' transferred; simp_rw [Function.update_of_ne hv]
          let R' := (chair G (h+1)).toLinearMap ∘ₗ up (Nat.le_succ h) ∘ₗ (chair G h).symm.toLinearMap
          exact (Paint.linear_c R' (ha v)).assists (Eventually.of_forall fun i=> by dsimp [R']; rw [LinearEquiv.symm_apply_apply])
       have he' := (cost_lane N M H U Q J K θ hq he hl D o hm hd x y hx V' hs).2
       refine he'.assists ?_
       filter_upwards [D.leaps.eventually (he.raises h (h+1) (Nat.le_succ h)),hx] with i H hp
       exact (fit_slot U K j.1 _ hp.pos (a i) j.2 (unscale (landed_slots _ _ hp hd)) (fun j=> H _)).symm
    apply (Paint.sum Finset.univ (fun j _=> (hh j).norm)).of_le; filter_upwards with i; rw [Real.norm_of_nonneg (by positivity)]; exact Work.B10.norm_le_direction_sum _

structure LaneCosts (a:Tags G h (n+m))(o:View U)(r s:ℝ)(x:Points n)(y:Points m)(C k:ℝ) : Prop where
   magnitude : ‖painted U K o.1 (fun _:Fin (n+m)=>h) r (forest x ((s/r) • y)) a‖ ≤ C*g r^(-k)
   phase : let z:= forest x ((s/r) • y); let D q:= painted U K q (fun _:Fin (n+m)=>h) r z a; ‖D o.1-D none‖ ≤ C*g r^(-k)*s
   rate : ‖fderiv ℝ (fun z=> painted U K o.1 (fun _:Fin (n+m)=>h) r z a) (forest x ((s/r) • y))‖ ≤ C*g r^(-k)

lemma lanes (a:I→Tags G h (n+m)) (ha : ∀ i,Paint D.toSmall (fun _=>1) (fun l=>chair G h (a l i))) :
    ∀ᶠ k:ℝ in atTop, ∃ C:ℝ,0<C ∧ ∀ᶠ i in D.p,LaneCosts U K (a i) (o i) (ρ i) (σ i) (x i) (y i) C k := by
    obtain ⟨hv,hz⟩:=cost_lane N M H U Q J K θ hq he hl D o hm hd x y hx a ha
    filter_upwards [flagged simple hv.norm,flagged simple hz.norm,flagged simple (lane_gradient N M H U Q J K θ hq he hl D o hm hd x y hx a ha).norm] with k ⟨C1,h1,hx⟩ ⟨C2,h2,hy⟩ ⟨C3,h3,hz⟩
    refine ⟨C1+C2+C3,by positivity,?_⟩; filter_upwards [hx,hy,hz,D.leaps.eventually (positive_g simple),D.outer.positive] with i hi hx hz ht (hh:0<σ i); rw [abs_one,mul_one] at hx hz; rw [abs_of_nonneg hh.le] at hi; have hw:= Real.rpow_pos_of_pos (show 0<g (ρ i) from ht) (-k); exact ⟨hx.trans (mul_le_mul_of_nonneg_right (by linarith only [h1,h2,h3]) hw.le), hi.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [h1,h2,h3]) hw.le) hh.le),hz.trans (mul_le_mul_of_nonneg_right (by linarith only [h1,h2,h3]) hw.le)⟩
end
section
-- uniform budget (even all ratios). D independent of B.
include H hq he hl
structure Placard (M' δ C:ℝ) (n m h:ℕ) where
   r:ℝ
   s:ℝ
   x:Points n
   y:Points m
   hd:Terracing r s M' δ x y
   o:View U
   u:Tags G h (n+m)
   pages: ∀ i,Ball C (u i)

/-- Prices in G.9: physical value part and first derivative.
 Can translate the positions all at once any o (`painted_cost`). -/
theorem placarded (M' δ L:ℝ)(hm:0≤M')(hd:0<δ)(n m h:ℕ) :
    ∀ᶠ k:ℝ in atTop, ∃ C:ℝ,0<C ∧ ∀ᶠ s in τ, ∀ (r:ℝ)(x:Points n)(y:Points m), Terracing r s M' δ x y →
      ∀(o:View U) (u:Tags G h (n+m)), (∀ i,Ball L (u i)) → LaneCosts U K u o r s x y C k := by
   let T:= Placard U M' δ L n m h; let r:=fun i:T=> i.r; let s:=fun i:T=> i.s
   let p:=comap s τ; have hr:Tendsto s p τ:=tendsto_comap
   have hx i:0<r i:= i.hd.pos
   have hy i:r i ≤ s i:= i.hd.younger
   let D:Pitch T:=⟨⟨p,r,(tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (Eventually.of_forall (fun i=>(hx i).le)) (Eventually.of_forall hy) (tendsto_nhdsWithin_iff.mp hr|>.1),Eventually.of_forall hx⟩)⟩,s,hr,Eventually.of_forall hy⟩
   let K':= max 0 L; have hK:0≤K':=le_max_left ..
   have hh:= lanes N M H U Q J K θ hq he hl D Placard.o hm hd Placard.x Placard.y (Eventually.of_forall fun i=>i.hd) Placard.u
      (fun i=> Paint.bounded K' (Eventually.of_forall fun j=>(chair_ball (j.u i) hK).mp (fun k=> (j.pages i k).trans (le_max_right 0 L))))
   filter_upwards [hh] with k ⟨C,hC,h⟩
   refine ⟨C,hC,?_⟩
   filter_upwards [eventually_comap.mp h] with s h r x y hp i u hv
   exact h (⟨r,s,x,y,hp,i,u,hv⟩:T) rfl

lemma expected {X:Set (Points n)}{Y:Set (Points m)}(hx:IsCompact X)(hX:X⊆conf n)(hy:IsCompact Y)(hY:Y⊆ O.Enh.Outside m)(L:ℝ)(h:ℕ):
    ∀ᶠ k:ℝ in atTop,∃ C:ℝ,0<C ∧ ∀ B H:ℝ, 0<B → 0<H→ ∀ᶠ (w:Window) in windows (upper G H B), ∀ x∈X,∀y∈Y,
      (forest x (w.Stretch • y))∈conf (n+m) ∧ ∀(o:View U)(u:Tags G h (n+m)), (∀ i,Ball L (u i)) →
        LaneCosts U K u o w.len w.Coarse x y C k := by
   obtain ⟨M',δ,hM,hδ,hA⟩:= terrain hx hX hy hY
   filter_upwards [placarded N M H U Q J K θ hq he hl M' δ L hM.le hδ n m h] with k ⟨C,hC,hq⟩
   refine ⟨C,hC,fun B T hb ht=>?_⟩; filter_upwards [(coarse_motion simple ht hb).eventually hq,(windows_short _).eventually self_mem_nhdsWithin,(windows_separation _).eventually hA] with w h hC hW x hx y hy
   have hh:0<Window.len w:=hC; have hp : Terracing (Window.len w) (Window.Coarse w) _ _ _ _:= hW _ hh x hx y hy
   have he (v:Window)(hf:0<v.len): v.Coarse/v.len=v.Stretch:= by change (v.len * _)/_=_; field_simp
   have hi:= unscale (landed_slots (Window.len w) (Window.Coarse w) hp hδ); rw [he w hh] at hi; exact ⟨hi,h _ _ _ hp⟩
end
end
end YM.FVA2.GradedFar.Physical.Round

