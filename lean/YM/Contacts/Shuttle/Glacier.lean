import YM.Contacts.Shuttle.Trinkets
/-! # Deterministic response for ANY offsets; preblock contraction -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Shuttle.Trace
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Pulse.Spine Origin
open Milling Milling.Steam Milling.Forge Tensor MultiNext.SignedSource Pattern Tide Morning Trace.Quill
open Pulse.Spine.Quill (Balanced)
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {G:Gauge}{h d k r n u:ℕ}{X Y:Type}{s t δ:ℝ≥0} {F: Field (Fin k) (Node X)}{b c:ℝ}{L:Side}
section
local notation "NY"=>Node Y
local notation "NX"=>Node X
def wreath (z:Cover)(A:NX→NY→ℝ)(F:Field (Fin k) NX) := allAt (fun _:Fin k=> fun x y=> A (backpack z x) y) F
def pier (k:ℕ)(X:Type): (Hood k X × Tailor k)≃ Hood k (Node X):=⟨fun x=> play x.1 x.2,fun x=> (fun i=> (x i).2, fun i=> (x i.1).1 i.2),fun _=> rfl,fun _=> rfl⟩
lemma relocate (z:Cover)(b:Hood k X)(o:X)(v: Tailor k)(i:Fin k): publish z (Fin.cons o b) v i.succ= backpack z (play b v i):= by change (z+lap v i,b i)= (lap v i + z,b i); rw [add_comm]
private lemma preprice (z:Cover)(s:ℝ≥0)(n:ℕ)(b:Hood k X)(o:X)(v:Tailor k) : (bath s n X).bill (publish z (Fin.cons o b) v)= fee (bath s n X) (0,o) (play b v) := by
   rw [fee_basis]; have he (x : Hood (k+1) (Node X)) : (bath s n X).bill (backpack z ∘ x)= (bath s n X).bill x:= by
      have he (i j:Fin (k+1)):(bath s n X).fee ((backpack z ∘ x) i) ((backpack z ∘ x) j)=(bath s n X).fee (x i) (x j):= by
         unfold bath; dsimp only [Function.comp_apply,backpack, Equiv.prodCongr_apply,Prod.map_apply,Equiv.coe_addRight,Equiv.refl_apply]; simp
      unfold Pulse.Range.bill Pulse.Range.height; simp_rw [he]
   rw [show publish z (Fin.cons o b) v=backpack z ∘ (Fin.cons (α:=fun _=>Node X) (0,o) (play b v)) from funext fun x=> Fin.cases (show publish z _ v 0=_ from (by simp [publish,backpack,legLane])) (fun i=>relocate ..) x,he]
variable {R: Cross L X Y}{z:Cover}{x:X}{y:Y}
def hear (C:ℝ)(δ : ℝ≥0)(k n r:ℕ)(L:Side) := ((mist δ n 6)*(r+1)*(k+1:ℝ)^n)*(C/(L.val:ℝ))^k/(L.val:ℝ)^r
theorem dawn [Fintype X] (hs : rent L z=0) (hL: Odd L.val) (H:∀ (v:List Axis), v.length≤ r →∀ x, Balanced (install (advanceC L R v) x) (hook t n L x) (c/(L.val:ℝ)^(1+v.length))) (hk:r≤n)(hv:t≤δ) (he:(2*(t:ℝ)/(L.val:ℝ))*(k+1)≤ s) (hc:0 ≤ c) (hu: Rest (bath s n X) (0,x) F b) (hf:silenced F r) : Rest (bath t n Y) (0,y) (wreath z (install R) F) (hear c δ k n r L*b) := by
   let e:=pier k X; let C:=Hood k X × Tailor k; let W(p:C):= (F (e p)); let A:=install R; let P (b:Hood k X)(q:Hood k NY)(v:Tailor k):= network (fun _:Fin k=>A) z (Fin.cons x b) v q; let K (q:Hood k NY) (p:C):= W p * Spine.Quill.tail r (P p.1 q) p.2; let G:=fee (ι:= Fin k) (bath t n Y) (0,y); let f(p:C):= fee (bath s n X) (0,x) (e p); let B:= hear c δ k n r L
   have hr (p:C): SumBudget (fun q=>‖K q p‖ * G q) (B*(‖W p‖* f p)):= by
      let I:= play p.1 p.2; have ht: hook t n L (z,(Fin.cons (α:=fun _: Fin (k+1)=> X) x p.1) 0) (0,y)=1:= by unfold Spine.hook; change mist t n (size ((0:Cover)-rent L z)) = 1; rw [hs]; simp [Laurent.size]
      have hz:= plume (R:=fun _:Fin k=>R) (z:=z) (b:=Fin.cons x p.1) hL s t δ (fun i=>H) hk hv he hc (0,y) p.2; rw [ht, mul_one, preprice] at hz; apply budget_loosen (budget_mono (budget_scale (norm_nonneg (W p)) hz) (fun i=> mul_nonneg (norm_nonneg _) (fee_plus i)) (fun i=> ?_)) ((le_of_eq (?_)))
      · change ‖W p‖ * (((mist δ n 6)*(r+1)*(k+1:ℝ)^n)*(f p)* (c/(L.val:ℝ))^k/(L.val:ℝ)^r)=_
        unfold B hear; ring
      apply le_of_eq; unfold K; rw [norm_mul,fee_basis, mul_assoc]; apply congr_arg; exact mul_comm ..
   have hb:0 ≤ B:= by unfold B hear; have hz:= mist_one (a:=6) (σ:=δ) (n:=n) (by positivity); positivity
   have hu': SumBudget (fun p:C=> ‖W p‖*f p) b:= budget_map hu _ e.injective (fun _=> rfl)
   have hw : SumBudget (fun p:Hood k NY × C=> ‖K p.1 p.2‖ * G p.1) (B*b):= budget_comm (Cost.product (budget_scale hb hu') hr)
   suffices he : ∀ q,wreath z A F q= ∑' p,K q p by change SumBudget (fun q=> ‖wreath z A F q‖ * G q) _; simp_rw [he]; exact budget_join fee_plus hw
   intro q
   have hp(P:Tailor k→ℝ)(c:Hood k X) : HasSum (fell F c (Spine.Quill.zen r P)) 0:= by
       cases r
       · unfold Spine.Quill.zen fell; simp
       next r=> exact hf c _ (by omega: r+1-1< r+1) _ (whist P _)
   let N(x:Hood k NX):= ∏ i,A (backpack z (x i)) (q i)
   have hr b a : N (play b a)= P b q a:= by unfold N P network; simp_rw [relocate]
   rw [wreath,allAt,←e.tsum_eq]; change (∑' p:C,W p*N (play p.1 p.2))= _; simp_rw [hr]
   have hy: Summable (K q) := by apply Summable.of_norm; exact ( (hw.2.1.prod_factor q)).of_nonneg_of_le (fun _=> norm_nonneg _) (fun a=> le_mul_of_one_le_right (norm_nonneg _) (fee_one q))
   -- can assume Fintype X? for arbitrary copies all heights.Fcount yes.Level. Want use Fintype to avoid estimates.K.End. Include.
   suffices he : Summable (fun p:C=> W p*P p.1 q p.2) by
      rw [he.tsum_prod,hy.tsum_prod]; apply tsum_congr; intro c
      unfold K Spine.Quill.tail; simp_rw [Pi.sub_apply, mul_sub]; rw [(he.prod_factor c).tsum_sub]; change _= _-∑' v,fell F c (Spine.Quill.zen r (P c q)) v; rw [(hp _ c).tsum_eq,sub_zero]; exact (hp _ c).summable
   let P' (p:C):= W p* Spine.Quill.zen r (P p.1 q) p.2; have hh : Summable P':= Summable.of_norm ((summable_prod_of_nonneg (f:=fun x=>‖P' x‖) (fun i=> norm_nonneg _)).2 ⟨fun i=> (hp (P i q) i).summable.norm, Summable.of_finite⟩) -- name
   refine (hy.add hh).congr (fun i=>?_); unfold K P' Spine.Quill.tail; simp [mul_sub]
end
end YM.Contacts.Shuttle.Trace
