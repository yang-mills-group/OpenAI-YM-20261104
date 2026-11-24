import YM.X.Dock.Stout
import YM.X.Bend.Weigh
/-!
# contour on sharp momentum phis, translates.Latt.Sight.FOR ALL q. intrinsic.Gen.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot Fund
open Maxwell Maxwell.Free Extra.FD Labels Pert.Position Pert.RawLabels
open Interval Size Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare Tri Pulse
open Chir.Dock Ribbon
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {m k d:ℕ} {n:Side} {q a:ℕ+}{r R e c:ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
local notation "T"=> Fin 3
lemma crossJ {X Y Z:Fielding.Walk}{J K:Ter}(h:RootJ q X Y Z J)(he:RootJ q X Y Z K):J=K:= funext (fun i=> funext (fun j=> funext (fun k=> funext (fun l=> tendsto_nhds_unique (h i j k l) (he i j k l)))))
variable (hq:1<q.val)
include hq in
lemma greenCrowd (ha:1<a.val)(h:Avoid q c): Avoid a c:= by
   intro x y z J hJ he; obtain ⟨h0,X,Y,Z,hX,hY,hZ,hj⟩:= hJ; apply h x y z J (Crowd.mk h0 ?_) he; have hr: Search x y z 4:= ⟨h0.wow.1,h0.wow.2.2,norm_sub_rev z x ▸ h0.wow.2.1⟩; obtain ⟨χ⟩:=Floor.make (R:=1) (by norm_num);
   rw [crossJ hj (rooters ha χ (by norm_num : (1:ℝ)<4) X Y Z hX hY hZ hr|>.2)]; exact ⟨_,_,_,entrant hq x,entrant hq y,entrant hq z, (rooters hq χ (by norm_num : (1:ℝ)<4) _ _ _ (entrant hq x) (entrant hq y) (entrant hq z) hr).2⟩
variable (B:Bare.Shop F) (hg:G.Simple) (χ:Floor R)(hr:R<r)
local notation "M"=> Aspect B hq hg χ hr
abbrev earshot (G:Gauge)(χ:Floor R) (x:Points 3) : ℝ:= 4*Sage.count G * SpinLimit (overall χ (x 1) (x 2) (x 0)) (x 1) (x 2) (x 0)
include hr
lemma exhibition {x:Points 3}(hx:x∈Pulse.Region 3 r): M x= ↑(earshot G χ x) ∧ stableJ χ (x 1) (x 2) (x 0) := by
    let X(k):= Grid.signal q k x; have hp:= Grid.choose_sample hq x; obtain ⟨J,hj,h⟩:= cut_view B hq hg χ hr hx X hp; have he(i:T): plot q (foamy X i) (x i):= sample_i hq X x hp i; have H: Search (x 1) (x 2) (x 0) r:= by refine ⟨?_,?_,?_⟩ <;> apply hx <;> first|decide|simp
    obtain ⟨h0,ht⟩:= rooters hq χ hr _ _ _ (he 1) (he 2) (he 0) H; rw [crossJ hj ht] at h; exact ⟨h,h0⟩
local notation "X"=> firstX B q hq hg 6
local notation "v"=> beaconLabels F (Nat.le_refl 6)
def euclideanFunction (G:Gauge)(χ:Floor R)(T':Test 3):ℂ:= ↑(boostB*boostU*boostU)* T'.applyTo (Complex.ofReal ∘ earshot G χ)
lemma approved (t:Test 3)(w: ready B hg r)(ht: Curve t ⊆ Pulse.Region 3 r): Integrable ((t:Points 3→ℂ)*(Complex.ofReal ∘ earshot G χ))∧ X 3 t v=euclideanFunction G χ t:= by
    have h : (t:Points 3→ℂ) * M = t * (Complex.ofReal ∘ earshot G χ) := by
        ext1 x; by_cases he: t x=0; · simp only [Pi.mul_apply,he,zero_mul]
        exact congr_arg (t x * ·) (exhibition hq B hg χ hr (ht (Subcell.includes _ (show x ∈ tsupport t from subset_closure he)))|>.1)
    refine ⟨?_,?_⟩; · rw [← h]; exact (inside B t (xAway B q χ) hq hg (fun p=> robust B χ p hq) (light_res B χ hr hq) (talent F (Nat.le_refl 6)) ht).1
    unfold euclideanFunction; rw [price_eq, has_tip B hq hg χ hr t w ht, show t.applyTo M=t.applyTo (Complex.ofReal ∘ earshot G χ) from integral_congr_ae (Eventually.of_forall (congr_fun h ·))] -- maybe shape
omit hr
lemma phase_allq {c:ℝ}(v0:Booth c F)(hx: BeaconTest B hq hg v0)(ha:1<a.val): BeaconTest B ha hg v0 := by
    let t:= mainT c v0.r1; obtain ⟨R,hR,ht,h⟩:=prepare_v B hg t; obtain ⟨χ⟩:=Floor.make (R:=R/2) (by linarith); have hr:R/2 < R:= by linarith
    exact (approved ha B hg χ hr t h ht).2.trans ((approved hq B hg χ hr t h ht).2.symm.trans hx)
lemma can_booth : ∃ (c:ℝ)(A:Booth c F),∀ q:ℕ+,∀ hq:1<q.val,Avoid q c ∧ BeaconTest B hq hg A:= by obtain ⟨c,A,h,hx⟩:=raised B (q:=2) (by decide) hg; exact ⟨_,A,fun _ hq=>⟨greenCrowd (q:=2) (by decide) hq h,phase_allq (q:=2) (by decide) _ _ _ hx hq⟩⟩ -- args
end YM.PositionX.Bend
