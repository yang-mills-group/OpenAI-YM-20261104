import YM.LocalLTE.XPre.Boxing
import YM.MergeProof.Plaza
/-! # Collision menus. Genuine low-grade active family at this leaf.

 Every ancestor label uses its original weights. Treat collisions at the same
 Wing by emitting heap entries. Preserve canonical first outputs on the
 turret when making Mercury preflight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof Menu Marker Accent Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
variable {J I N T:Type}[DecidableEq J][Fintype J][Fintype I][Fintype N][Fintype T]
variable {B:Marker.Census J}{d p m l K:ℕ} {κ V:ℝ}
variable (A:T→Hat B R) (h:T→Prop)
-- boost heap powers.
local notation "M"=> Mound A
noncomputable def alphaH : Mound A→Prop:= Sum.elim h (fun i:Σ j:logDeck A,Rock A (.logKey j.val)=> ∀ k ∈ i.snd.val.val,h k)
local notation "A'"=> heap A
local notation "Φ"=> alphaH A h
variable (φ:T→ Config G f→ℝ)
noncomputable def expoH : Mound A→ Config G f→ℝ:= Sum.elim φ (fun i U=>∏ k∈ i.snd.val.val, φ k U)
local notation "Tq"=> expoH A φ
variable (he:∀i,h i→ (SoloInk (A i).M (φ i) κ p l)∧∀ j, (A i).M.turn=Wing.logKey j→ (R.activities.reg j).support⊆ AbsoluteSums.Animals.neighbors l (R.activities.reg j).site)
variable (hK:p ≤ m)(ht:K*p ≤ m) (hp:K ≤ m)(hx:Fintype.card J≤ K)
include he hK ht hp hx
lemma pres (i:M) (h':Φ i): ProductInk ((A' i).M) (Tq i) κ m l ∧∀ j:ℕ,(A' i).M.turn=Wing.logKey j→ (R.activities.reg j).support⊆ AbsoluteSums.Animals.neighbors l (R.activities.reg j).site:=by
    rcases i with i|i
    · have h:=he _ (show h i from h'); have hv:= h.1
      obtain ⟨j,hj,hV,hX,-⟩:= hv.health
      refine ⟨⟨hv.ink,hv.reads,hX.borel,1,p,?_,hK,by rw [one_mul]; exact hK,fun _=>(A i).M,fun _=>φ i,?_,?_,fun i=>hv⟩,h.2⟩
      · haveI : Nonempty J:= let H:=(A i).shiny; ⟨H.choose⟩; exact ((Fintype.card_pos_iff.mpr this).trans_le (hx.trans hp))
      · rw [Fintype.prod_unique]; rfl
      funext V; rw [Fintype.prod_unique]; rfl
    let P:= i.2.val.val; let k:= i.1.val; have hz j (hj:j∈P):= he j (show h j from h' _ hj); have hP:P.Nonempty:= i.2.val.property.1
    have he(j)(hj:j∈P): (A j).M.turn=.logKey k:= (mem_filter.mp (i.2.val.property.2.1 hj)).2
    let Q:Fin P.card ≃ ↥P := (Fintype.equivFinOfCardEq (show Fintype.card ↥P=P.card from Fintype.card_coe _)).symm
    have hu : P.card ≤ Fintype.card J:=by
       let f(j:↥P):J:=(A j).shiny.choose; suffices hv : Injective f by rw [← Fintype.card_coe]; exact Fintype.card_le_of_injective f hv -- underscore
       intro j v hr; by_contra h; have hg:=(A j).shiny; have hh:=(A v).shiny; exact Finset.disjoint_left.mp ((i.snd.val.property).2.2.1 j.prop v.prop (fun hX=> h (Subtype.ext hX))) hg.choose_spec (show f j ∈ (A v.val).s.val from hr.symm ▸ hh.choose_spec)
    have hv (j)(hj:j∈P): (A j).M.crest=(R.activities.reg k).support:=by unfold Leaf.crest; rw [he _ hj]; rfl
    obtain ⟨a,ha⟩:=hP; let X':=(R.activities.reg k).support; refine ⟨⟨⟨_,show (Menu.heap A (Sum.inr i)|>.M.turn)=Wing.logKey k from rfl⟩,?_,?_,P.card,p,hu.trans (hx.trans hp),hK,(Nat.mul_le_mul_right p (hu.trans hx)).trans ht,fun j=>(A (Q j)).M,fun j=>φ (Q j), ?_,?_,fun j=>(hz _ (Q j).prop).1⟩,fun j hx=>?_⟩
    · funext U; change ∏ j∈ P,(A j).M.ingredient U=masked R.p.threshold X' (fun U=>∏ i∈P,φ i U) U; by_cases h:Healthy R.p.threshold X' U
      · rw [masked_eq _ _ _ _ h]; exact Finset.prod_congr rfl fun i hi=> by rw [(hz i hi).1.reads,hv _ hi,masked_eq _ _ _ _ h]
      rw [masked_ne _ _ _ _ h]; exact Finset.prod_eq_zero ha (by rw [(hz a ha).1.reads,hv _ ha,masked_ne _ _ _ _ h])
    · exact Finset.measurable_fun_prod _ (fun j hj=> let hp:=(hz _ hj).1.health; hp.choose_spec.2.2.1.borel)
    · exact (le_of_eq ((Equiv.prod_comp Q (fun j:↥P=>(A j).M.weight)).trans (Finset.prod_coe_sort P (fun j=>(A j).M.weight))))
    · funext V; exact ((Equiv.prod_comp Q (fun j:↥P=>φ j.val V)).trans (Finset.prod_coe_sort P (fun j=> φ j V))).symm
    obtain rfl : j=k := (Wing.logKey.inj hx).symm
    exact (hz a ha).2 _ (he _ ha)
end YM.LocalLTE.XPre
