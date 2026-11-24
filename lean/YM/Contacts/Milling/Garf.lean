import YM.Contacts.Pulse.Buoy
import YM.Contacts.Milling.Sill
namespace YM.Contacts.Milling.Garf
open Lattice RG Wilson Tree Stationary PertExtension.Series Pulse Pulse.Spine Push.AbsoluteSums Function Finset Filter Set Bloch Exterior
open scoped BigOperators Topology NNReal ContDiff Classical
noncomputable section
variable {n p k:ℕ}{α β L V: Type}{X: Type}{m:Side}
section name
variable {ι: Type}[Fintype ι]
local notation "θ" => terrain
lemma fee_ride (x: ι→ Node α)(z:Cover)(s:ℝ≥0) : (θ s _).bill (backpack z ∘ x) = (θ s _).bill x := by unfold Range.bill Range.height; simp [backpack,terrain] -- inspect
def carry (x:ι→ Node α) : Pulse.Field ι (Node α) := fun v=> if ∃ (z:Cover), backpack z∘x=v then 1 else 0
def road (q:Node α)(i:Site m):Co m α := (wrap m q.1+i,q.2)
def carried (m:Side)(x:ι→Node α): Pulse.Field ι (Co m α):= fun v=>∑ i:Site m, if (fun j=> road (x j) i)=v then 1 else 0
lemma carry_quote (x:ι→Node α)(s:ℝ≥0): Rooted (θ s _) (carry x) ((θ s _).bill x):= by
  refine ⟨by positivity,fun i b=>?_⟩; change SumBudget _ _; let w:Cover:= b.1-(x i).1; let g:= backpack w ∘ x
  have h q (hq : (q:Locked (Node α) i b).val≠ g) : carry x q.val= 0 := if_neg fun ⟨z,hz⟩=> hq (by rw [←hz]; let he:= congr_arg Prod.fst (Eq.trans (congr_fun hz i) q.property); change (x i).1+z=b.1 at he; change backpack z ∘ x=g; rw [show z=w from by unfold w; rw [←he]; abel])
  by_cases hi:g i=b; swap; · refine budget_mono (budget_loosen (budget_zero (α:=Locked (Node α) i b)) (by positivity)) (fun _=>by positivity) (fun p=>?_); change _≤ (0:ℝ); simp [h p (fun e=> hi (show _ from by rw [←e]; exact p.property))]
  let t:Locked (Node α) i b:=⟨g,hi⟩; have hx: carry x t.val=1:= if_pos ⟨w,rfl⟩
  have he : HasSum (fun p:Locked (Node α) i b=> ‖carry x p.val‖*(θ s _).bill p.val) ((θ s _).bill x):= by
    convert hasSum_single (f:=fun p:Locked (Node α) i b=> ‖carry x p.val‖*(θ s _).bill p.val) t (fun p hp=> by rw [h p fun e=> hp (Subtype.ext e)]; simp) using 1; rw [hx,(show t.val=g from rfl)]; simp [g,fee_ride]
  exact ⟨fun _=>by positivity,he.summable,he.tsum_eq.le⟩
lemma carry_shadow (x:ι→ Node α)(m:Side): Shadow (lower m) (carry x) (carried m x):= by
  intro i b y; change carried ..= _; rw [MergeProof.expand_eq]; let w:= b.1-(x i).1; let g:= backpack w ∘ x; let z:= wrap m w; let l d:ι→Co m α:=fun j=> road (x j) d; let B:= Node α; let Y:= lower (α:=α) m; have he p (h : (p:Locked B i b).val≠g) : carry x p.val=0:= if_neg fun ⟨v,hv⟩=> h (by rw [←hv]; let hu:= congr_arg Prod.fst ((congr_fun hv i).trans p.property); change _+v=b.1 at hu; rw [show v=w from by unfold w; rw [← hu]; abel])
  have hL: l z= lower m ∘ g:= by funext; exact Prod.ext (map_add (wrap m) _ _).symm rfl
  have hl (d)(h:l d=y.val): d=z ∧ g i=b:= by
    have H:= (congr_fun h i).trans y.property; refine ⟨?_,Prod.ext (by change _+(b.1- _) = _; abel) (congr_arg (fun x:Co m α=>x.2) H)⟩; have hh := congr_arg Prod.fst H; change wrap m ((x i).1)+d= wrap m b.1 at hh; unfold z w; rw [map_sub]; rw [← hh]; abel
  change (∑ d:Site m, if l d=y.val then 1 else (0:ℝ))= ∑' u: Locked B i b, if roll _ i b u=y then carry x u.val else 0; rw [Finset.sum_eq_single z]; rotate_left; · intro d _ hd; exact if_neg fun v=> hd (hl _ v).1
  · simp
  by_cases hi : g i=b; swap; · rw [if_neg fun e=> hi (hl _ e).2]; symm; convert tsum_zero (α:=ℝ) (β:=Locked B i b) using 1; congr! 1; ext p; rw [he p fun e=> hi (e ▸ p.property),ite_self]
  let q:Locked B i b:= ⟨g,hi⟩; rw [tsum_eq_single q]
  · have hhx : l z=y.val ↔ roll (lower m) i b q=y:= by rw [← Subtype.val_inj,hL]; rfl
    simp [hhx,show carry x q.val=1 from if_pos ⟨w,rfl⟩]
  intro d hd; rw [he d fun e=> hd (Subtype.ext e),ite_self]
lemma slot_invoice [Fintype α](u:Co m α→ℝ)(x:ι→ Node α): House.design (carried m x) u= ∑ i:Site m, ∏ j:ι,u (road (x j) i):= by rw [House.design_spec]; simp_rw [carried,Finset.sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp [ite_mul] -- sum
lemma carry_hold (z:Cover)(x:ι→ Node α): Mirrored (backpack z) (carry x):= by
  intro p; unfold carry; refine if_congr ?_ rfl rfl; constructor
  · rintro ⟨u,h⟩; use u-z; ext1 i; have hp:= congr_fun h i; have hk := congr_arg Prod.snd hp; refine Prod.ext ?_ (show (x i).2 = (p i).2 from hk); have hh:= congr_arg Prod.fst hp; change _= (p i).1+ z at hh; change (x i).1+(u-z)= (p i).1; rw [← add_sub_cancel_right (p i).1 z,← hh]; change _=( (x i).1+u) - z; abel
  rintro ⟨u,h⟩; use u+z; rw [← h]; ext1 i; refine Prod.ext (add_assoc _ _ _).symm rfl
end name
section stencils
open House
variable [Fintype L] {m:Side}
local notation "V" => (House.Dir L)
def words (Q : V →ℝ)(j:ℕ) : Pulse.Field (Fin j) L:= fun x=> (j.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ j Q 0 (fun i=> Pi.single (x i) (1:ℝ))
lemma hash (Q:V→ℝ)(j:ℕ)(v:V): House.design (words Q j) v= Radial.jet Q j v := by
   unfold words Radial.jet; rw [design_spec]; let w i : V := v i • Pi.single i (1:ℝ)
   have h : v = ∑ i:L,w i:= by ext x; simp [w,Pi.single_apply]; -- orient
   rw [show iteratedFDeriv ℝ j Q 0 (fun _=>v)=_ from (congr_arg _ (show (fun _:Fin j=>v)=fun _: Fin j=>∑ i,w i from funext fun i=>h)).trans ((iteratedFDeriv ℝ j Q 0).toMultilinearMap.map_sum (fun _ i=>w i)),Finset.mul_sum]; let e:= iteratedFDeriv ℝ j Q 0; apply sum_congr ?_
   · intro t ht; change _=_*e.toMultilinearMap (fun i=> w (t i)); unfold w; rw [MultilinearMap.map_smul_univ (c:=fun i:Fin j=>v (t i))]; change _=_*(_*e _); rw [mul_assoc, mul_comm (iteratedFDeriv ℝ j Q 0 _)]
   congr!
variable (T:L→ Node α)
def aboard (q:Pulse.Field (Fin k) L): Pulse.Field (Fin k) (Node α):= printRun (∑ i,q i • carry (T∘ i))
def cargo (s:ℝ≥0)(q:Pulse.Field (Fin k) L):=∑ i, ‖q i‖*(terrain s _).bill (T∘ i)
def ashore (q:Pulse.Field (Fin k) L)(m:Side): Pulse.Field (Fin k) (Co m α) := printRun (∑ i,q i • carried m (T∘i))
lemma aboard_summed (s:ℝ≥0)(q:Pulse.Field (Fin k) L): Rooted (terrain s _) (aboard T q) (cargo T s q):= (Rooted.aggregate Finset.univ (fun i _=> Rooted.smul (carry_quote _ _) (q i))).even
lemma aboard_desc (q:Pulse.Field (Fin k) L)(m:Side) : Shadow (lower m) (aboard T q) (ashore T q m):= (Shadow.aggregate _ Finset.univ (fun i _=> Rooted.smul (carry_quote (T∘ i) 0) (q i)) (fun i _=> (carry_shadow (T∘i) m).scale _)).even (Rooted.aggregate Finset.univ (fun i _=> Rooted.smul (carry_quote (T∘ i) 0) (q i))) -- maybe argument order
def load [Fintype α](x : Site m): House.Dir (Co m α) →L[ℝ] V:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (road (T i) x)
lemma words_read [Fintype α](q:Pulse.Field (Fin k) L)(x:House.Dir (Co m α)): House.design (ashore T q m) x= ∑ i:Site m,House.design q (load T i x):= by
   unfold ashore House.design; simp_rw [verse_print,verse_sum,verse_scale',map_sum,map_smul]; change (∑ i:(Fin k→L), q i • House.design (carried m (T∘ i)) x)=∑ i,House.design q (load T i x); simp_rw [slot_invoice,smul_eq_mul,mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [House.design_spec]; exact sum_congr (by congr!) fun _ _=> rfl
lemma aboard_hold (z:Cover)(q:Pulse.Field (Fin k) L): Mirrored (backpack z) (aboard T q):= by apply print_mirror; intro x; simp only [Finset.sum_apply,Pi.smul_apply]; exact Finset.sum_congr rfl fun i _=> congr_arg (fun s:ℝ=> q i • s) (carry_hold z _ _)
end stencils
end
end YM.Contacts.Milling.Garf
