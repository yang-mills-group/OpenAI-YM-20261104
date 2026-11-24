import YM.QuadraticLocal.Lamps
import YM.Integration.SpinalCoefficientPrice
/-!
Transport strong Spinal rates to qlocal for arbitrary REF dictionaries, markers z at disjoint
modes (Birth laws from caller), α test population sup throughout. Fresh (connected marked output,
*remove only quiet*, don't renormalize aside) assembly. Builds actual test-uniform log entries
in a common fixed layout; charge EXACT same field stencil, masks and all root issues carried in
`root` outside before expansion. Disconnected products accounted downstream by evaluation via the
same polynomial. Uses Anchors.tallyI summation lemma and `spinal_jet_cost`.

For each `z`: controls allowed to rely on every mark address; supply `Width.LocalCharge` (only
nontrivial clause is in controlled ancestry). This bill alone doesn't bind test points, links or
vacuum field factors of Marks in fromRun; it permits moving stencils only if later certified to
satisfy actual address conventions. We prune only syntactic roots not at the given supports,
proving all such dropped rows had `wet` model identically zero on ALL units first; no dependence
on `x` in that layout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Pane
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Serif RemainderComparison.Mosaic RemainderComparison.WickReps
open AnalyticBridge.VerifiedReset Next.Foundations GridRenewal.Rain Integration RemainderComparison.CoefficientPrices
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι V J:Type}{p:BudgetPoint}{k:ℕ}{T:Type*} {G:Gauge}{n:Side}
variable [DecidableEq V] {R:Census V}{w:V→ℝ} (o:V→Site n)
variable (A:Manor G n ι T J)(Z:Set ι)(z:ι→ Poly R)(S:Set J)(root:ι→Support n) {σ b:ℝ}
-- Sup with S restriction before tally
abbrev Table := { i : J× R.Mode // i.1∈ S ∧ i.2≠R.quiet ∧ (∀ v∈i.2.val,o v∈ A.halls i.1) }
def prepare (j:J) : Poly R:= Verse.controls Z z (A.marks j)
local notation "Tab"=> Table (R:=R) o A S
variable (H:A.Spinal S root p σ b)
local notation "C"=>prepare A Z z
include H in
lemma fame (j:J)(hj:j∈S) : A.Sees p root j := by obtain ⟨s,h,hg,hH⟩:=H.grants; exact (hg j hj).1 -- include
-- same coefficient in every panel, include rows even when mask is always zero if enough roots.
def printBulbs : Lamps T (Table (R:=R) o A S) G p o R where
 mode i:= i.val.2
 live i:= i.property.2.1
 address i := A.rooms i.val.1
 roots i:= i.property.2.2
 nominal t i:= ((C i.val.1).part i.val.2) • (fun U=> ((A.solvent t i.val.1 U:ℝ):ℂ))
 legal t i:= regular_smul _ (regular_mapped Complex.ofRealCLM ((fame A S root H i.val.1 i.prop.1).angle t)) -- comp reducible?
 clear i:= A.total i.val.1
 pure _ i _ h:= congr_arg (fun r:ℝ=>( (C i.val.1).part i.val.2) • (r:ℂ)) ((fame A S root H _ i.prop.1).stall _ h _)
local notation "Bulbs"=> printBulbs o A Z z S root H
local notation "P"=> (A.paint p Z z)
lemma lights (t:T)(i:Tab)(U:Config G n): (Bulbs).light t i U=((A.paint p Z z t U i.val.1).part i.val.2):=by
   unfold Lamps.light; dsimp only [printBulbs,Lamps.ground]; rw [Manor.paint,Poly.part_smul]; unfold Manor.wet; split
   next ht=> exact mul_comm _ _
   next hn=> by_cases hx:Healthy p.threshold (A.halls i.val.1) U
             · dsimp only [Manor.halls] at hx ⊢; rw [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ hx]; exact mul_comm _ _
             dsimp only [Manor.halls] at hx ⊢; rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ hx]; simp
lemma lightsPaid (h:Chorus R w Z z k): (Bulbs).Paid w p.B σ b:=by
   obtain ⟨hf,hg,hH⟩:= spinal_jet_cost H
   let f (i:J×R.Mode):= ‖(C i.1).part i.2‖*jetCost A S p i.1; have ht i:0≤ f i:=mul_nonneg (norm_nonneg _) (hf ..)
   have H' (j:Tab) t x (hx:x∈ A.halls j.val.1): p.supBounds x (A.halls j.val.1) ((Bulbs).nominal t j) (f j.val):= bound_smul (a:=jetCost A S p j.val.1) _ ((sup_real ((fame A S root H _ j.property.1).angle t)).2 (hg _ j.property.1 t x hx))
   have hk : Hit (fun i:J×R.Mode=> A.halls i.1) p.B (fun i=> Poly.toll w i.2 * f i) σ b:= by
      let f' (i:J)(j:R.Mode) := Poly.toll w j * f (i,j); apply tallyI (p:=p) _ _ hH f' (fun i j=> mul_nonneg (Poly.worth h.votes _).le (ht _)); intro i
      have he : ∑ j,f' i j= Poly.price w (C i)*jetCost A S p i:= by simp [Poly.price,f',f,Finset.sum_mul,mul_assoc]
      exact he.trans_le (mul_le_of_le_one_left (hf i) (bought h _))
   refine ⟨fun i=> f i.val,fun i=>ht _,H',fun i=>budget_pull _ (show Injective (Subtype.val (p:=fun i : J× R.Mode=> i.1∈ S ∧ i.2≠R.quiet ∧ (∀ v∈i.2.val,o v∈ A.halls i.1))) from Subtype.val_injective) (hk i)⟩
-- exact Hot projections with halo cuts.
variable (hz:∀ j, Width.LocalCharge (G:=G) p o (root j) (fun _=> z j))
include hz H
private lemma authority (j:J)(hj:j∈S)(i:R.Mode)(t:T)(U:Config G n)
    (he : (A.paint p Z z t U j).part i ≠0): ∀ v∈i.val, o v∈ A.halls j:=by
  have hc (s:Multiset ι)(hk:∀ a∈s, Width.LocalCharge (G:=G) p o (A.halls j) (fun _=> z a)) : Width.LocalCharge (G:=G) p o (A.halls j) (fun _=> Verse.controls Z z s):= by
    induction s using Multiset.induction_on with
    | empty => simp only [Verse.controls, Multiset.map_zero, Multiset.prod_zero]; simpa only [Finset.prod_empty] using (Width.product_local (G:=G) (X:=A.halls j) (∅:Finset ℕ) (p:=p) (R:=R) (a:=o) (fun _=>0) (by simp))
    | cons i q ih => simp only [Verse.controls,Multiset.map_cons, Multiset.prod_cons]; split
                     next => exact (hk i (Multiset.mem_cons_self ..)).mulCharges (ih fun j hj=> hk j (Multiset.mem_cons_of_mem hj))
                     next => rw [one_mul]; exact ih fun j hj=> hk j (Multiset.mem_cons_of_mem hj)
  rw [Manor.paint,Poly.part_smul] at he
  exact (hc (A.marks j) (fun i hi=> (hz i).widen ((fame A S root H j hj).travels t i hi U (fun h=>left_ne_zero_of_mul he (by rw [h]; simp))))).carry U _ (right_ne_zero_of_mul he)

lemma lit (t:T)(U:Config G n)(h:Chorus R w Z z k)(ha:0≤σ): (Bulbs).log t U= GridRenewal.Rain.fresh (A.basin p S Z z t U):=by
    have hb : Summable (fun i:Tab=> (Bulbs).frame i t U):= (lightsPaid o A Z z S root H h).sums ha h.votes ..
    let a (i : Tab):= (Bulbs).frame i t U; let g:= A.paint p Z z t U; let F (i:S):= g i.val; have hv:Summable F:= Manor.standing t U Z z H.templary h ha
    ext q; by_cases hh:q=R.quiet; subst q; · exact (Lamps.quiet_of_hasSum t U hb).trans (unwritten _).symm
    have he : (GridRenewal.Rain.fresh (A.basin p S Z z t U)).part q=∑' i:S,(F i).part q := by
       change ((tsum F).part q)- (Poly.send R.quiet _).part q= _; rw [Poly.share hv,Poly.part_send,if_neg hh,sub_zero]
    rw [he, Lamps.log,Poly.share hb];
    let s: Set Tab:= {i| i.val.2=q}
    let f: ↑s → S:=fun i=> ⟨i.val.val.1,i.val.prop.1⟩
    have hi:Injective f:= fun i j h=> Subtype.ext (Subtype.ext (Prod.ext (congr_arg Subtype.val h) ((i.prop : i.val.val.2=q).trans (show j.val.val.2=q from j.prop).symm)))
    have hM : Function.support (fun i:S=> (F i).part q) ⊆ Set.range f :=by
       intro i hx; exact ⟨⟨(⟨(i.val,q),i.prop,hh,authority o A Z z S root H hz i.val i.prop q t U hx⟩: Tab),rfl⟩,rfl⟩
    have ht : Function.support (fun i:Tab=> ((Bulbs).frame i t U).part q) ⊆ s:=by
       intro i hx; change i.val.2=q; contrapose! hx; unfold Function.support; rw [Set.mem_setOf_eq]; push Not; rw [Lamps.frame,Poly.part_send,if_neg (show q≠(Bulbs).mode i from hx.symm)]
    calc
       _ = ∑' i:s,(a i.val).part q := (tsum_subtype_eq_of_support_subset ht).symm
       _ = ∑' i:s,(F (f i)).part q := tsum_congr fun i=> by
              change (Poly.send i.val.val.2 _).part q= _; rw [Poly.part_send,if_pos (show q=i.val.val.2 from (i.prop : i.val.val.2=q).symm),lights o A Z z S root H]; exact congr_arg (g i.val.val.1|>.part) (i.prop : i.val.val.2=q)
       _ = _ := Function.Injective.tsum_eq hi hM
end YM.QuadraticLocal.Pane
