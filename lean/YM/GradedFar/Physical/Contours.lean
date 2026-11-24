import YM.GradedFar.Physical.Ownership
import YM.GradedFar.Physical.Hill
import YM.GradedFar.Logged.Office
/-!
# (G.6) apply leases for these exact receiving fields, part I
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open Scale Dframe
open OPE OPE.Orbits OPE.Logged OPE.Logged.Deck Horizon
open OPE.Log (badge)
open Economy (Paint)
open Continuation
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable (D : Deck.Pitch I) (u:I→Inputs G d)(v:I→Inputs G e)
lemma log_cost (q:ℝ):badge q=1+Horizon.degrees q:=by unfold badge OPE.run Horizon.degrees; rw [Real.log_inv]
include hq he H
lemma landing (D: Economy.Small I) {C:ℝ} (hx : ∀ᶠ i in D.p, Within C (u i)) :
    Synthesis.Samples U Q D D.r d (fun i=> here K (D.r i) (u i)) := by
    intro i j hj; obtain ⟨k,C',hc,hA⟩:= brought N M H U Q J K θ hq he (d i) j
    let c:=max C 1; have hc':0<c:=lt_of_lt_of_le zero_lt_one (le_max_right ..)
    refine Paint.from_cost (C'*c) (mul_pos hc hc') k ?_
    filter_upwards [hx,D.leaps.eventually hA,D.positive,D.ran] with x hx hp ht h
    have hb : ‖chair G (d i) (u x i)‖≤c:= (chair_ball (u x i) hc'.le).1 (fun b=> (hx i b).trans (le_max_left ..))
    let t:= D.r x
    change ‖Q.cutTest j (d i) (K t (d i) (u x i))‖ ≤ _
    rw [← mapK_apply]
    change ‖extracted U Q K (d i) j (D.r x) (chair G (d i) (u x i))‖ ≤ _
    refine le_trans (ContinuousLinearMap.le_opNorm (extracted U Q K (d i) j _) _) ((mul_le_mul hp hb (norm_nonneg _) ?_).trans_eq ?_)
    · have hl : 0≤ 1+Horizon.degrees (D.r x):= (log_cost (D.r x)) ▸ zero_le_one.trans h
      positivity
    rw [log_cost]; ring

-- switch two physical radii eventually before reading estimates
variable {C C' M' δ:ℝ}(hm:0 ≤ M')(hδ:0<δ)(x:I→Points n)(y:I→Points m)(o:I→View U)
    (hl:∀ᶠ i in D.p,Terracing (D.r i) (D.s i) M' δ (x i) (y i))
    (hu:∀ᶠ i in D.p,Within C (u i))(hv:∀ᶠ i in D.p,Within C' (v i))
    (hc:LogTrace U Q.port)
set_option quotPrecheck false
local notation "X"=>fun i=>(x i).ofLp
local notation "Y"=>fun i=>(y i).ofLp
local notation "ζ"=>fun i=>(o i).2
local notation "Z"=>fun i=>(o i).1
local notation "V"=>fun i=> here K (D.s i) (v i)
local notation "A"=>fun i=> here K (D.r i) (u i)
local notation "radius"=> Deck.radius D
local notation "stamp"=>D.toSmall
omit hq he H in
include hl in
private lemma well_pitched : ∀ᶠ i in D.p, Fork.Landed (D.r i) (D.s i) M' δ (X i) (Y i) :=hl.mono fun _ h=> ⟨h.pos,h.younger,h.xcap,h.ycap,h.ynear,h.xsep,h.ysep,h.together⟩

-- use two separate radii to allow even independent R positions
-- exact unit-weight dollar in estimator; `c_W` defined earlier. preserve placements (x,y).
def Yactual (r s:ℝ) (i : View U) (x : Points n) (y : Points m) (u:Inputs G d)(v:Inputs G e) :=
  OPE.Orbits.whole (OPE.spectator U i.1) (atPos r i.2 x) (here K r u) (atPos s i.2 y) (here K s v)
def Dactual (r s:ℝ) (i : View U) (y:Points m) (v:Inputs G e)(a : Sec G h) :=
  Yactual U K r s i (0:Points 1) y (d:=fun _=>h) (fun _=>a) v
include hm hδ hl hu hv hc

lemma mixed_story (h:ℕ) :
    Paint stamp (Deck.radius D h) (fun i=> Yactual U K (D.r i) (D.s i) (o i) (x i) (y i) (u i) (v i) -
       Dactual U K (D.r i) (D.s i) (o i) (y i) (v i) (packet U K Q d h (D.r i) (o i) (x i) (u i))) ∧
    Paint stamp D.s (fun i=> Yactual U K (D.r i) (D.s i) (o i) (x i) (y i) (u i) (v i) -
       Yactual U K (D.r i) (D.s i) (none,(o i).2) (x i) (y i) (u i) (v i)) ∧
    Paint stamp (fun i=> 1+ Deck.radius D h i)
       (fun i=> Yactual U K (D.r i) (D.s i) (o i) (x i) (y i) (u i) (v i)) := by
   have hr:=well_pitched D x y hl
   have hz:= landing N M H U Q J K θ hq he u stamp hu
   have hy0:=landing N M H U Q J K θ hq he v D.outer hv
   have hy : Synthesis.Samples U Q stamp D.s e V:= fun i j h=> (hy0 i j h).pull («g»:=fun i=>i) (P:=stamp) tendsto_id D.cost
   refine ⟨?_, Office.phased D X Y ζ M' δ hm hδ hr U Q A V Z hc simple hz hy, Office.rated D X Y ζ _ _ hm hδ hr U Q A V Z hc simple h hz hy⟩
   apply Paint.assists (Office.replaced D X Y ζ M' δ hm hδ hr U Q A V Z hc simple h hz hy)
   filter_upwards [hr] with i hi
   unfold Office.total_gap Office.actorD Office.total Dactual Yactual
   apply congrArg (Yactual U K (D.r i) (D.s i) (o i) (x i) (y i) (u i) (v i) - ·)
   let q:=Q.packet h (atPos (D.r i) (o i).2 (x i)) (A i) (o i).2
   have hp:here K (D.r i) (d:=fun _:Fin 1=>h) (fun _=>packet U K Q d h (D.r i) (o i) (x i) (u i))=(fun _=>q) := funext fun _=> LinearEquiv.apply_symm_apply ..
   rw [hp, show atPos (D.r i) (o i).2 (0:Points 1)=(fun _:Fin 1=>(o i).2) by ext1 j; simp [atPos]]
   have hh := whole_perm (S:=P) (spectator U (Z i)) (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl _) (x:=sole (o i).2) (d:=fun _:Unit=>h) (v:=fun _=>q) (w:=V i) (spectate U (Z i)) (Fork.unique_root hi (o i).2 hδ)
   exact hh.symm
end
end YM.FVA2.GradedFar.Physical
