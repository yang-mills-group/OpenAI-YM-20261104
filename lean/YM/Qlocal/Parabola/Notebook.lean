import YM.Qlocal.Parabola.Pollen
import YM.Qlocal.Service
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Parabola
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Bank Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
open Publishing Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories RG3.Forms
variable {G:Gauge}{n:Side}{w t v c d b δ κ:ℝ}{k:ℕ}{V Ω ι:Type}[DecidableEq V]{R:Census V}
    {A:Activities G n} {P:BudgetPoint}{s:V→Support n}{o:V→Site n} {Z:Support n}
    {L':ι→Ray R}{U:ι→Support n}{q:Ray R}
variable {J J':Type}
-- Ledger with quiet unmarked PLEASE (including active.Hot), force reconciliation.
variable {r : RG.Rep G n}
variable (L:Ledger Ω J G n R)
set_option quotPrecheck false
local notation "E"=> r.activities
local notation "P₀"=> r.p
local notation "α"=> Ledger.painted L r
local notation "Y!"=> L.taste r o s
variable (h:Ethics r o s L)
include h
lemma regard (x:Ω): Authority r.p r.activities s (L.forced x):= by
 let f:=L.forced x; have he(k i):=h.hard x k i; refine ⟨fun i=> ?_,fun i U hv=> ?_, h.base x⟩
 · exact ⟨fun U V hb hs=>Marker.Poly.ext (fun j=>(he i j).1 _ _ hb hs),fun j=>(he i j).2.1,fun g U=>Marker.Poly.ext (fun j=>(he i j).2.2.1 g U),fun U=>fun j=> h.hosts x i U j⟩ -- last eta ∀
 by_contra hp; apply hv; exact Marker.Poly.ext fun j=> not_not.mp (fun ht=> hp ((he i j).2.2.2 U ht)) -- type check
lemma reshaped (g: Ω→ Policy G R n) (hg:∀ x,Authority r.p r.activities s (g x)): Ethics r o s {L with forced:=g}:= by
 refine { h with hard:=?_, hosts:=?_,base:=?_ }
 · intro x i j; let f:=g x; have ht:=(hg x).align i; refine ⟨fun U V hi hv=> congr_arg (fun z:Poly R=> z.part j) (ht.travel U V hi hv), ht.visible _,fun k U=> congr_arg (Poly.part · j) (ht.worth k U), fun U hv=> (hg x).beacon i U (fun h=> hv (by dsimp only; rw [h]; rfl))⟩
 · exact fun x i U j hj=> ((hg x).align i).owns U j hj
 exact fun x=>(hg x).quiet
omit h
variable (p:Rental q) (ht:0 ≤ t)
include p
lemma trimP {Y:ℕ→Support n} {Z: ℕ→Ray R} {g: Ω→ ℕ → Config G n→ Poly R} (he:Haze Y k t Z q v) (hs:∀ x i U,lives (g x i U) (Y i) s)
    (hz:∀ i x U,CoverP (Z i) (g x i U)) : ∃ u:ℕ×R.Mode→ℝ,(∀ i, 0≤u i)∧ (∀ i j, (∃ v∈ j.val,¬s v⊆Y i)→ u (i,j)=0)∧ (∀ i x U j, ‖(g x i U).part j‖≤u (i,j))∧ Ac.Hit Y k (Tons q u) t v:=by
 let u(i:ℕ)(j:R.Mode):= if speech j (Y i) s then Z i j else 0; have hu i j:0≤u i j:=by unfold u; split; exact he.1 i j; rfl
 refine ⟨(fun i=> u i.1 i.2),fun i=> hu ..,?_,?_,fun x=>?_⟩ -- binder ∃ j type
 · intro i j; rintro ⟨v,hv,h⟩; exact if_neg (fun h0=>h (h0 _ hv))
 · intro i x U j; change ‖_‖ ≤ u i j; unfold u; split
   next hj=> exact hz i x U j
   next hj=> rw [not_not.mp (fun H=>hj (hs x i U j H)), norm_zero]
 refine budget_mono (he.2 x) (fun i=>?_) (fun i=> ?_)
 · split; exact mul_nonneg (sum_nonneg fun j _=> mul_nonneg (p.pos _).le (hu i j)) (Real.exp_nonneg _); rfl
 split; refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _); apply Finset.sum_le_sum; intro j _; exact mul_le_mul_of_nonneg_left (show u i j ≤ _ from by unfold u; split; rfl; exact he.1 i _) (p.pos _).le; exact le_rfl
lemma trims {t' : ℝ} (hg: Bulk r s L q (t+δ) t' b) (hd:0≤δ) {g: Ω→ Policy G R n}{Z:ℕ→ Ray R}(h: ∀ i,Authority r.p r.activities s (g i))(he:Haze (fun i=>((E).forced i).support) r.p.B t Z q v)(hv:∀ i x U,CoverP (Z i) (g x i U)): Bulk r s {L with forced:=g} q t t' v:= by
 constructor
 · obtain ⟨f,hF,hX,hV⟩:=hg.regular; refine ⟨f,hF,hX,fun x=> budget_mono (hV x) (fun i=>?_) (fun i=>?_)⟩
   · split; exact mul_nonneg (sum_nonneg (fun j _=> mul_nonneg (p.pos _).le (hF (i,j)))) (Real.exp_nonneg _); exact le_rfl
   change (if x∈L.region i then Tons q f i * Real.exp _ else _) ≤ _; split; apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun j _=> mul_nonneg (p.pos _).le (hF (i,j)))); apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd) (Nat.cast_nonneg _); exact le_rfl
 obtain ⟨u,hU,hu,hv,h⟩:= trimP p he (fun x i U=>(h x|>.align i|>.owns U)) hv; exact ⟨u,hU,hu,fun x i=>hv i x,h⟩
lemma tab (hf:Bulk r s L q t v b) : ∃ Y', Haze (fun i=>((E).forced i).support) (P₀).B t Y' q b ∧ ∀ x i U,CoverP (Y' i) (L.forced x i U):= by obtain ⟨f,hF,H',hr,h⟩:=hf.forced; exact ⟨fun i j=>f (i,j),⟨fun i j=>hF (i,j),h⟩,hr⟩
-- output.Norm connection. 
variable [Countable J]
include p ht h
noncomputable abbrev markRead (x:Ω)(U:Config G n):= ∑' i: J, Ledger.painted L r x U i
set_option quotPrecheck false
local notation "Λ"=> markRead (r:=r) L
lemma Weather (hf:Bulk r s L q t v b)(x:Ω)(U:Config G n) : (∀ j, Publishing.lives (L.painted r x U j) (L.region j) s ∧ (L.painted r x U j).part R.quiet=0) ∧ Summable (L.painted r x U) := by
 obtain ⟨f,hF,hX,hV⟩:=hf.regular; constructor
 · intro i; unfold Ledger.painted; split; exact ⟨fun j=>h.owns x i j U, h.quiet ..⟩ -- eta
   next hp=> by_cases hh: Healthy r.p.threshold (L.region i) U; rw [masked_eq _ _ _ _ hh]; exact ⟨fun j=>h.owns x i j U,h.quiet ..⟩; rw [masked_ne _ _ _ _ hh]; exact ⟨lives_zero _ _,rfl⟩
 let Y i:= L.painted r x U i; let Z(i:J)(j:R.Mode):= f (i,j); have hz: Haze (L.region) r.p.B t Z q v:= ⟨fun i j=> hF (i,j),hV⟩; let q₁:=fun _:V=>(1:ℝ); refine (Marker.Poly.budgeted (fun x:V=>zero_lt_one) (f:=Y) (hz.summable_units p ht h.branch (fun i j=>?_) q₁ (fun i=> zero_lt_one)) (fun i=>le_rfl)).1
 obtain ⟨v,hv⟩:= h.branch i; have hm:= (hX i j x).2 v hv; unfold Y Ledger.painted; split
 next ht=> rw [h.constant x i U ht]; exact hm.2 1 (by unfold Healthy; rw [UVNext.CouplingReset.flags_one]; simp) [] (Nat.zero_le _) (by simp)
 next ht=> by_cases hh: Healthy r.p.threshold (L.region i) U
           · rw [masked_eq _ _ _ _ hh]; exact hm.2 U hh [] (Nat.zero_le _) (by simp)
           rw [masked_ne _ _ _ _ hh,Poly.part_nil,norm_zero]; exact hF (i,j)
-- Comm.Attach references moment.Weighs.
variable [Nonempty V] [Fintype V]
lemma published (hf:Bulk r s L q t v b)(x:Ω)(U:Config G n): (((Y!).leaf x).density U) = (Real.exp (r.exponent U):ℂ) • session r.p r.activities (L.forced x) (Λ x) U := by
 obtain ⟨he,hP⟩:= Weather L h p ht hf x U
 let F:=L.painted r x U; have hL: ((Y!).leaf x).log U = markRead (r:=r) L x U:= L.log_sum r o s x U hP (fun j hi=> h.constant x j U hi) (fun k hk=> not_not.mp (fun hp=> hk ((he k.1).1 k.2.val hp))) (fun i=>(he i).2)
 rw [RG3.Forms.Deck.density,hL]; congr 2; exact L.forced_cluster r o s x U (fun i=>h.base x i U)
end YM.Qlocal.Parabola
