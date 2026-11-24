import YM.GradedFar.Round.Buy
/-!
# RoundMeter value, in terms exactly of G.9 at any fixed cap(s)
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
    (E : (d:ℕ)→ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ:ℝ→ℝ)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (W : Bookshelf N U J K E Y θ) (D : Earned N M U J K θ) (hD:oriented U K)
    (ht: LogTrace U Q.port) (he:∀ h:ℕ,∀ᶠ r in τ, ∀ u : Sec G h,K r h u=J r h (E h r u))
    (hGrid : Grid N U J)
variable {C B:ℝ}(hC:0<C)(hB:0<B)
local notation "Q₀"=> upper G C B
local notation "Γ"=>windows Q₀
local notation "g₀"=>gYM G ∘ Window.len
section
variable (T:Filter I)(w:I→ Continuation.Window)(hw:Tendsto w T (windows (upper G C B)))
variable {X:Set (Points n)}{Y':Set (Points m)}(hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y')(hy:Y'⊆Outside m)
    (o:I→View U)(S:I→ XSet X Y') (hH : 6≤h)
local notation "b₀"=> Duly Q₀ T w hw simple
local notation "F"=> familyPoint U K h
local notation "r"=>Window.len∘w
local notation "L0"=>contour w S
include H W D ht he hD hGrid hX hx hY hy hB hC hw o hH
set_option maxHeartbeats 400000 in
lemma each_fee (p : ℕ) (a : Tags G h (n+m)) : Priced b₀ p (θ∘r) 0 (fun i=> painted U K (o i).1 (fun _:Fin (n+m)=>h) (r i) (contour w S i) a)
   (fun i=>boundary N a (contour w S i)) := by
   have hh:=receipt_lane N M H U J K E Y θ Q W D hD ht (he h) hGrid hC hB T w hw hX hx hY hy o a S hH (p+1) (Nat.succ_le_succ (Nat.zero_le _))
   have hr := (((windows_short _).comp hw).eventually (paid_reading simple θ D.clock)).mono fun i h=> h.2.2.2
   refine ⟨hh.1.monotone p.le_succ,?_⟩; exact ((hh.2.mono_fee le_rfl (p+1|>.le_succ)).plus (hh.1.below hr p.le_succ)).apply_eq (Eventually.of_forall fun i=> by simp only [Function.comp_apply]; abel)

def outfit (s:Points (n+m))(t:ℝ)(p:ℕ):Point G h (n+m):= ∑ j∈Finset.range (p+1),(t:ℂ)^j • Jury.fxt (book N h) s j
omit H W D ht he hD hGrid hX hx hY hy hB hC hw o hH in
lemma outfitted (s: Points (n+m))(t:ℝ) (u:Tags G h (n+m)):
    outfit (n:=n) (m:=m) N s t p u=crop p t (boundary N u s) := by unfold outfit boundary shop Reg.Point.story; simp only [crop_eq]; simp
lemma precision (p:ℕ) (a:I→Tags G h (n+m)) (L:ℝ)(hA:∀ᶠ i in T, Within L (e:=fun _=>h) (a i)) :
    Bill b₀ (p+1) 0 (fun i=> painted U K (o i).1 (fun _:Fin (n+m)=>h) (r i) (contour w S i) (a i)-crop p (θ (r i)) (boundary N (a i) (contour w S i))) := by
   let d:=fun _:Fin (n+m)=>h
   let Y' i:=painted U K (o i).1 d (r i) (L0 i) - outfit N (L0 i) (θ (r i)) p
   have he' (x:Choices G d): Bill b₀ (p+1) 0 (fun i=> combo (d:=fun _=>h) (a i) x * Y' i (basisInputs x)) := by
      have ht':Bill b₀ (p+1) 0 (fun i=>Y' i (basisInputs x)):= by
        unfold Y'; simp_rw [sub_apply, outfitted]; exact (each_fee N M H U J K E Y θ Q W D hD ht he hGrid hC hB T w hw hX hx hY hy o S hH p _).2
      have hw' : Bill b₀ 0 0 (fun i=> combo (d:=fun _=>h) (a i) x):= Bill.of_bounded _ _ (hA.mono fun i h=> combo_ball _ _ h)
      simpa only [zero_add] using hw'.times ht'
   apply (Bill.sum Finset.univ (fun i _=> he' i)).apply_eq (Eventually.of_forall _); intro i
   rw [show ∑ (x:Choices G d),combo (a i) x * Y' i (basisInputs x)=Y' i (a i) from (basis_spelling ..).symm]; simp_rw [Y',sub_apply,outfitted]; rfl
end
end
end YM.FVA2.GradedFar.Physical.Round
