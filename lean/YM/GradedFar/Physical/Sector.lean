import YM.GradedFar.Physical.Contours

/-!
# Meter units of the (G.6) physical packet
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
local notation "r"=> D.r
local notation "stamp"=>D.toSmall
open private well_pitched from YM.GradedFar.Physical.Contours
include H hq he hm hδ hl hu hc
/-- Keep projection & price on each label; output through h in S basis then purchased
by `H_r`. -/
theorem packet_fee : Paint stamp (fun _=>1) (fun i=> chair G h (packet U K Q d h (D.r i) (o i) (x i) (u i))) := by
   let T k i:=Q.fresh k (inlay D X ζ i) (ζ i) (A i)
   have ht k : Paint stamp (fun i=> D.r i^k) (T k) := Office.paid_packet D X Y ζ M' δ hm hδ (well_pitched D x y hl) U Q A hc k
     (landing N M H U Q J K θ hq he u stamp hu)
   let L (k:ℕ) i:= (mapK K (D.r i) k).symm.toContinuousLinearMap
   have he' k : Paint stamp (fun i=> (D.r i)⁻¹^k) (L k) := by
      obtain ⟨p,C,hC,H⟩:= inverse_books N M H U J K θ hq he k
      refine Paint.from_cost C hC p ((D.toSmall.leaps.eventually H).mono (fun i h=>?_)); rw [log_cost]
      apply h.trans_eq; ring
   have hh k : Paint stamp (fun _=>1) (fun i=> L k i (T k i)) := by
      apply Paint.eases (Paint.times_cost (he' k) (ht k) (Eventually.of_forall (fun i=>(L k i).le_opNorm (T k i))))
      filter_upwards [D.toSmall.positive] with i hi; rw [inv_pow, inv_mul_cancel₀ (pow_pos hi k|>.ne')]
   let A' (j:Fin (h+1)): RowSpace G j.val →ₗ[ℂ] RowSpace G h:= (chair G h).toLinearMap ∘ₗ up (Nat.le_of_lt_succ j.isLt) ∘ₗ (chair G j.val).symm.toLinearMap
   let E i:= ∑ j:Fin (h+1), A' j (L j.val i (T j.val i))
   have hx : Paint stamp (fun _=>1) E:= Paint.sum _ (fun i _=> Paint.linear_c (A' i) (hh i.val))
   apply hx.assists
   have hA (i:Fin (h+1)):=D.toSmall.leaps.eventually (he.raises _ _ (Nat.le_of_lt_succ i.isLt))
   filter_upwards [ eventually_all.mpr hA ] with i hi
   unfold E packet Reader.packet; rw [map_sum,map_sum]
   refine Finset.sum_congr rfl fun j _=>?_ ; let m:=j.val; let v:=T j.val i; change chair G h (up (Nat.le_of_lt_succ j.isLt) ((chair G m).symm _))= chair G h ((K (D.r i) h).symm (U.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) v))
   apply congr_arg; apply (K (D.r i) h).injective; rw [hi j, LinearEquiv.apply_symm_apply]; apply congr_arg; exact ContinuousLinearEquiv.apply_symm_apply (mapK K ..) _

omit hu in
include hv in
lemma response_value (a:I→Sec G h)(B:ℝ)(ha:∀ᶠ i in D.p,Ball B (a i)) :
    Paint stamp D.s (fun i=> Dactual U K (D.r i) (D.s i) (o i) (y i) (v i) (a i)-
      Dactual U K (D.r i) (D.s i) (none,(o i).2) (y i) (v i) (a i)) ∧
    Paint stamp (fun i=> 1+Deck.radius D h i) (fun i=> Dactual U K (D.r i) (D.s i) (o i) (y i) (v i) (a i)) := by
   let X' (_ : I):Points 1:= 0; let A' i:Inputs G (fun _:Fin 1=>h):= fun _=>a i
   have ht:= (mixed_story N M H U Q J K θ hq he D A' v hm hδ X' y o
     (hl.mono fun i hi=> (show Terracing (D.r i) (D.s i) M' δ (X' i) (y i) from
       ⟨hi.1,hi.2,(fun _=>by simpa [X'] using hm),hi.ycap,(fun _ _ h=> (h (Subsingleton.elim ..)).elim),hi.ysep,hi.ynear,hi.together⟩))
     (ha.mono (fun i hi => (show Within B (A' i) from (fun _=>hi)))) hv hc h).2
   exact ht
end
end YM.FVA2.GradedFar.Physical
