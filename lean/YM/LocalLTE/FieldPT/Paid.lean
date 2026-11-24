import YM.LocalLTE.FieldPT.Atlas
/-!
 Full E.Exponent preservation at rendering error, preserving ledger and moves.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n L : Side} {j z k m i M:ℕ} {W κ K U C V t H u v ε: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
open Scene Song Ovens Rack
variable (X:Listing G n)(p:BudgetPoint)(R:PathData G)
-- Gram start layers.J.
def inkPt (M:ℕ) (f:ℕ→ EKey n→ Pot G n) (i:Fin (M+2) × EKey n): Pot G n:= if i.1.val ≤ M then (if i.1.val =0 then f 0 i.2 else f i.1.val i.2-f (i.1.val-1) i.2) else 0
-- full output UNIT.
def operas (M:ℕ)(f:ℕ→ EKey n→ Pot G n) := stuff (Rack.upE (Price.bells p R X M)) (Song.choir (Price.inkPt M f) ∘ numbering (Price.Rol M n))
variable (M:ℕ)
local notation "U'"=> Price.tubeX R p X
section rotate
-- unit.Support.Masks.E.K invariant true weights.Use for delta estimates flags interactions.
variable (a₀ : Activities G n) (hA:a₀.reg=(drawer G n|>.reg)) (F : Fin (M+2) × EKey n→Pot G n) (G' G0: ℕ → EKey n→ Pot G n)
include F hA
local notation "U#" => bells p R X M
local notation "f!" => operas X p R M G'
local notation "f0" => operas X p R M G0
lemma gyros (s:Signed)(a:Site n) (h:a₀.E=stuff (Rack.upE U#) (Song.choir F ∘ numbering (Price.Rol M n))) (hp:Nonempty (a₀.Moves s a)) : ∃ W:a₀.Moves s a,(∀ i,f! (W.ep i)= f! i ∘ pull s a) ∧∀ i,f0 (W.ep i)=f0 i∘ pull s a:=by
    let K:=Song.whirl (ι:=Fin (M+2) × EKey n) s a; let e:= numbering (Price.Rol M n); let f:=(e.trans K).trans e.symm; let u':=destination s a
    have he i: e (f i)= K (e i):= Equiv.apply_symm_apply ..
    let Z:= Price.sands p R X M; let Q:= Rack.upE U#
    let u:= regMap u'; let V:= rearrange (regularKeys n) u f
    have hx i:a₀.reg (V i)=u (a₀.reg i):=by rw [hA]; exact congr_arg Prod.fst (Progress.DirectedRecipe.stocked ..)
    have hQ (i):V (Q i)= Q (f i):=by
       apply move_stock _ _ f (U#).reg _ i; intro i; symm
       change Song.revolve Z (e _)= _; rw [he]; refine Progress.DirectedRecipe.reg_ext (Song.spirit _ F s a (e i)|>.1) (Song.spirit _ F s a (e i)|>.2.1)
    have h' (F:Fin (M+2) × EKey n→ Pot G n) i: let g:=stuff Q (choir F ∘ e); g (V i)=g i∘ pull s a:=by
       intro g; by_cases he':i∈Set.range Q
       · obtain ⟨i,rfl⟩:=he'; unfold g; rw [hQ,stuffed,stuffed,Function.comp_apply]; rw [he]; exact Song.spirit Z _ s a (e i)|>.2.2
       unfold g; rw [blank _ _ (unused hQ he'), blank _ _ he']; rfl
    let A:= hp.some; refine ⟨{A with ep:=V, reg_site:= fun i=> congr_arg RegularAddress.site (hx i), reg_support:= fun i=> congr_arg RegularAddress.support (hx i), valuesE:=fun i U=> ?_},h' _ ,h' _⟩
    rw [h]; exact congr_fun (h' F i) U
end rotate
section bills
variable (F G₀:ℕ→ EKey n→ Pot G n) (hG:G.Simple) (hp:20<n.val)
local notation "f1!"=> operas X p R M F
local notation "g!"=> operas X p R M G₀
local notation "T"=> (bells p R X M)
local notation "U"=> Price.sands p R X M
-- extra cost formula; Γ from next accuracy post.Loosen
include hG hp
lemma upper (C:ℝ)(hF:∀ i≤ M,∀ a:EKey n,Comic G (U' a) p (F i a))(hG':∀ i≤ M,∀ a:EKey n,Comic G (U' a) p (G₀ i a))(he:∀ i≤ M,Stocked p U' (F i-G₀ i) C)(hC:0 ≤ C) : (∀ i, Comic G ((drawer G n).reg i) p (f1! i) ∧ Comic G ((drawer G n).reg i) p (g! i)) ∧ ∃ v:ℕ→ℝ,(∀ i, p.supBounds ((drawer G n).reg i).site ((drawer G n).reg i).support ((f1!-g!) i) (v i)) ∧ anchored p (drawer G n).reg v ((M+2:ℕ)*(turnFee p*(2*C))):=by
    let V:=numbering (Price.Rol M n); let f':= Price.inkPt M F; let y:=Price.inkPt M G₀; let X':= Price.sands p R X M
    have h₁ (D:ℕ→ EKey n→ Pot G n)(h:∀ i ≤ M,∀ a:EKey n, Comic G (U' a) p (D i a)) (i:Fin (M+2) × EKey n): Comic G (U i) p (Price.inkPt M D i):= by unfold inkPt; split_ifs with H J; exact h 0 (Nat.zero_le _) _; exact (h _ H _).pair (h _ (by omega) _); exact flick _
    have hx (i:Fin (M+2)): Stocked p U' (fun k=> (f'-y) (i,k)) (2*C) := by
       let j:=i.val; by_cases hp:j≤ M
       · by_cases hu:j=0
         · rw [show (fun k=> (f'-y) (i,k))=F 0 - G₀ 0 from (funext fun k=>by unfold f' y Price.inkPt; simp only [Pi.sub_apply]; rw [if_pos hp,if_pos hu,if_pos hp,if_pos hu])]; exact (he _ (by omega)).cheaper (by linarith)
         rw [show (fun k=> (f'-y) (i,k))= (F j-G₀ j)-(F (i.val-1)-G₀ (i.val-1)) from (funext fun k=>by unfold f' y Price.inkPt; simp only [Pi.sub_apply]; rw [if_pos hp, if_pos hp, if_neg hu,if_neg hu]; unfold j; abel)]; rw [two_mul]; exact (he _ hp).minus (he _ (show j-1≤ M by omega))
       rw [show (fun k=> (f'-y) (i,k))=0 from (funext fun k=>by unfold f' y Price.inkPt; dsimp only [Pi.sub_apply]; rw [if_neg hp,if_neg hp,sub_self]; rfl)]; refine ⟨fun _=>0,fun k=>⟨reg_const _,sup_le (sup_const 0) abs_zero.le⟩,fun x=>budget_loosen (show SumBudget _ 0 from ?_) (by positivity)⟩; simp [BudgetPoint.mass,RG.SumBudget]
    let Q:= T; let Q':=Rack.upE Q
    have hp(D:ℕ→EKey n→ Pot G n)(h:∀ i≤ M,∀ a',Comic G (U' a') p (D i a'))(i): Comic G ((drawer G n).reg i) p (Price.operas X p R M D i):= by
       unfold Price.operas; by_cases he:i∈ Set.range Q'; swap; · rw [Progress.DirectedRecipe.blank _ _ he]; exact flick _
       obtain ⟨i,rfl⟩:= he; rw [stuffed,show (drawer G n).reg (Q' i)=Q.reg i from Rack.reg_up Q i]; let v:=V i; exact Comic.weight (Comic.move hG hp (h₁ D h v.2) v.1 _ rfl rfl) _
    refine ⟨fun i=>⟨hp F hF i,hp _ hG' i⟩,?_⟩
    unfold Stocked at hx; choose v hp' hV using hx
    let g (i:Fin (M+2) × EKey n):= v i.1 i.2; have hA(t:ℕ):t=t:=rfl
    have hf (i:Seat n × (Fin (M+2) × EKey n)): (Song.choir f'-Song.choir y) i = Rim n • (((f'-y) i.2) ∘ i.1.view):= by funext x; exact (mul_sub ..).symm
    let N i:= |Rim n| *( (turnFee p)*g (V i).2)
    have hK: anchored p X' (fun i=>turnFee p*g i) ((↑(M+2:ℕ):ℝ)*(turnFee p*(2*C))):= by
      intro x; refine Cost.product ?_ fun i=> Quotes.anchored_scale (turnFee_pos p).le (hV i) x
      simpa only [Fintype.card_fin] using! Cost.finite (α:=Fin (M+2)) _ (show 0≤turnFee p*(2*C) from (by have hp:=turnFee_pos p; positivity))
    have hQ': anchored p Q.reg N ((M+2:ℕ)*(turnFee p*(2*C))):= fun i=> Cost.equiv V (Weft.playsB _ hK i)
    let g':=stuff Q' N
    refine ⟨g',fun i=>?_,fun i=>?_⟩
    · unfold g'; by_cases hv:i∈ Set.range Q'; swap; · simp_rw [Pi.sub_apply]; rw [show f1! _=0 from blank _ _ hv,show g! _=0 from blank _ _ hv, blank _ _ hv,sub_self]; exact sup_le (sup_const 0) abs_zero.le
      obtain ⟨i,rfl⟩:= hv; rw [stuffed,show (drawer G n).reg (Q' i)=Q.reg i from Rack.reg_up Q i]; rw [Pi.sub_apply]; unfold operas; rw [stuffed Q', stuffed Q']; change p.supBounds _ _ ((Song.choir f'-Song.choir y) (V i)) _; rw [hf]; let v':=(V i); exact AnalyticBridge.CouplingShape.sup_scale _ (Song.transSup v'.1 (hp' v'.2.1 v'.2.2|>.1) (hp' v'.2.1 v'.2.2|>.2)) -- edit hv shadow
    apply transfer_budget Q' _ _ (hQ' i)
    · intro j; rw [show (drawer G n).reg (Q' j)=Q.reg j from Rack.reg_up Q j,show g' (Q' j)=N j from stuffed ..]
    intro j hj; rw [show g' j=0 from blank _ _ hj]; simp [BudgetPoint.mass]
end bills
end YM.AnalyticBridge.VerifiedReset.Collection.Price
