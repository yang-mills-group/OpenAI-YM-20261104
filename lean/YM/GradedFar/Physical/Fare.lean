import YM.GradedFar.Physical.Cost
import YM.GradedFar.Physical.Lease

/-!
# (G.6)
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open Scale Dframe
open OPE Orbits Logged OPE.Logged.Deck Horizon
open OPE.Log (badge)
open Economy (Paint)
open Continuation Continuation.Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} {I:Type} (d : Fin n → ℕ)(e: Fin m→ℕ) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K)(hl : LogTrace U Q.port)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
structure Tab (C C' M' δ:ℝ) where
    r : ℝ
    s : ℝ
    x : Points n
    y : Points m
    landscape : Terracing r s M' δ x y
    u : Inputs G d
    hu : Within C u
    v : Inputs G e
    hv : Within C' v
    a : Sec G h
    ha : Ball 1 a
    o : View U

include H hq he hl
/-- Stronger history-independent G.6 option: *all* `s` small and all `0<r≤s`
on physical geometry. Exponent chosen even before B. No `Y-D` comparisons
here against a different exterior, and use scenes with exact viewer and center
(any phases admitted in Spec.Final). The `Owed` price is as explained, ℓ¹ price on
response coefficients on actual dual through h. At these `r,s`, `r/s=T⁻¹,
w=(r,log T)` fits `receive U K` (as true linear D, `far_operator_r`). -/
theorem all_owing (h : ℕ) (C C' M' δ:ℝ) (hm:0≤M')(hδ:0<δ) : ∀ᶠ k:ℝ in atTop,∃ D:ℝ,0<D ∧ ∀ᶠ s:ℝ in τ,
    ∀ (r:ℝ) (o:View U)(x:Points n)(y:Points m), Terracing r s M' δ x y →
     ∀ (u:Inputs G d),Within C u →∀ (v:Inputs G e),Within C' v →∀ a:Sec G h,Ball 1 a→ Owed U Q K k D h r s o x y u v a := by
   let T := Tab d e U (h:=h) C C' M' δ; let r:=fun i:T=> i.r; let s:=fun i:T=> i.s
   let p:=comap s τ; have hr:Tendsto s p τ:=tendsto_comap
   have hx:∀ i:T,0<r i:= fun i=> i.landscape.pos
   have hy:∀ i:T,r i ≤ s i:= fun i=> i.landscape.younger
   let D:Pitch T:=⟨⟨p,r,(tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (Eventually.of_forall (fun i=>(hx i).le)) (Eventually.of_forall hy) (tendsto_nhdsWithin_iff.mp hr|>.1),Eventually.of_forall hx⟩)⟩,s,hr,Eventually.of_forall hy⟩
   have h := rooms N M H U Q J K θ hq he D Tab.u Tab.v hm hδ Tab.x Tab.y Tab.o (Eventually.of_forall fun (i:T)=> i.landscape)
      (Eventually.of_forall fun (i:T)=> i.hu) (Eventually.of_forall fun (i:T)=> i.hv) hl h Tab.a (Eventually.of_forall fun (i:T)=> i.ha)
   filter_upwards [h] with k ⟨D',hD,h⟩
   refine ⟨D',hD,?_⟩
   filter_upwards [eventually_comap.mp h] with s h r o x y hp u hu v hv a ha
   exact h (⟨r,s,x,y,hp,u,hu,v,hv,a,ha,o⟩:T) rfl
omit H hq he hl in
-- from realizations to the T-window
lemma far_operator_r (x y:ℝ)(hx:0<x)(hy:x ≤ y) (o:View U)(z:Points m)(v:Inputs G e)(a:Sec G h) :
    receive U K (x,Real.log (y/x)) o z v h a=Dactual U K x y o z v a := by
   have h : 0 < y:=hx.trans_le hy
   rw [receive_leg]; unfold Dactual Dwide Ywide Yactual; rw [show  Window.Coarse (x,Real.log (y/x))=y from (by unfold Coarse Window.Stretch; change x*_=_; rw [exp_log (show 0 < y/x from by positivity)]; field_simp)]; rfl

omit H hq he hl in
lemma owing_span {r:Window}(hp:0<r.len) (k C:ℝ)(o:View U)(x:Points n)(y:Points m)(u:Inputs G d)(v:Inputs G e)(a:Sec G h):
    Owed U Q K k C h r.len r.Coarse o x y u v a ↔
     let T i:= Ywide U K r i x y u v; let W':=packet U K Q d h r.len o x u
     let D i (b:Sec G h):=Dwide U K r i y v b; let E b:=D o b-D (none,o.2) b; let X:=C*g r.len ^(-k)
     ‖T o-D o W'‖ ≤ X*(r.Coarse+r.Stretch⁻¹^(h+1)) ∧
       ‖T o‖+‖chair G h W'‖+‖D o a‖+weigh h (D o) ≤ X ∧
       ‖T o - T (none,o.2)‖+‖E a‖+ weigh h E ≤ X*r.Coarse := by
   unfold Owed; dsimp only
   rw [show r.len / r.Coarse=r.Stretch⁻¹ from (by change r.len / (r.len*exp _)=(exp _)⁻¹; field_simp)]; rfl
omit H hq he hl in
lemma coarse_motion {C B:ℝ}(simple:G.Simple)(hc:0<C)(hb:0<B) :
    Tendsto Window.Coarse (windows (upper G C B)) τ := by
  let D:Loft G Window:=⟨windows (upper G C B),Window.len,C,hc,B,hb,Window.windows_short _⟩
  refine D.soon simple (s:=Window.sep) ?_
  filter_upwards [(windows_separation (upper G C B)).eventually_ge_atTop 0, windows_span _,D.nearing.eventually (positive_g simple)] with i hi hx hp
  refine ⟨hi,(Real.exp_le_exp.mp ?_)⟩; unfold Loft.height; rw [Real.exp_log (mul_pos (show 0<D.C from hc) (Real.rpow_pos_of_pos hp _))]; exact hx

/-- Physical residual, fields and phase estimates (G.6). All large T, all small r with
T in `upper`. Obtain D before B is even supplied (and before `C` in its upper).
-/
theorem horizon_lease {X:Set (Points n)}{Y:Set (Points m)}(hx:IsCompact X)(hX:X⊆conf n)(hy:IsCompact Y)(hY:Y⊆O.Enh.Outside m) (h:ℕ)(L R':ℝ) :
    ∀ᶠ k:ℝ in atTop,∃ D:ℝ,0<D ∧ ∀ C B:ℝ,0<C→ 0<B→ ∀ᶠ (w:Window) in windows (upper G C B),
      ∀ o:View U,∀x∈X,∀y∈Y,∀(u:Inputs G d),Within L u →∀(v:Inputs G e),Within R' v →∀(a:Sec G h), Ball 1 a →
       Owed U Q K k D h (Window.len w) (Window.Coarse w) o x y u v a := by
   obtain ⟨M',δ,hM,hδ,hT⟩:= terrain hx hX hy hY
   filter_upwards [all_owing d e N M H U Q J K θ hq he hl h L R' M' δ hM.le hδ] with k ⟨D,hD,h⟩; refine ⟨D,hD,fun C B hc hb=> ?_⟩
   filter_upwards [(coarse_motion simple hc hb).eventually h,(windows_separation _).eventually hT,(windows_short _).eventually self_mem_nhdsWithin]
     with w hi hp (hh:0<(Window.len w)) o x hx y hy u hu v hv a ha
   exact hi (Window.len w) o x y (hp (Window.len w) hh x hx y hy) u hu v hv a ha
-- specialize
lemma paid_history : OldCost U K Q := by
   intro _ _ _ d e h X Y hx hX hy hY L R C hc
   obtain ⟨k,h0,D,hD,hF⟩:= ((eventually_ge_atTop 0).and (horizon_lease d e N M H U Q J K θ hq he hl hx hX hy hY h L R)).exists
   refine ⟨k,h0,fun B hb=> ⟨D,hD,?_⟩⟩
   filter_upwards [hF C B hc hb,(windows_short _).eventually self_mem_nhdsWithin] with w hw (hr:0<(Window.len w)) i x hx y hy u hu v hv
   have he:Ball 1 (0 : Sec G h):= fun q=> (by rw [map_zero,norm_zero]; exact zero_le_one)
   rw [← full_same, ← center_same]
   exact ((owing_span d e U Q K hr k D ..).mp (hw i x hx y hy u hu v hv 0 he)).1
end
end YM.FVA2.GradedFar.Physical

