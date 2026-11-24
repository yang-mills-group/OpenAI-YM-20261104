import YM.SchemeConversionRG11.FirstW.Vane.FreeTide
/-! Each individual Wick slot may be deleted, not just a sum over slots.
No nondegeneracy of the coordinate Gaussian used. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators
section algebra
variable {I : Type*} [DecidableEq I]
variable (e : I→I→ℂ) (f : Finset I→ℂ)
abbrev Deb (s : Finset I) (i : I) := ∑ j∈s.erase i,e i j * f ((s.erase i).erase j)
lemma ledger {s : Finset I} {i j : I} (hd : i ≠ j) (hi : i∈s) (hj : j∈s)
    (H : ∀ q:Finset I, q ⊂ s → ∀ i∈q, f q = Deb e f q i) :
    Deb e f s i = e i j * f ((s.erase i).erase j) + ∑ k∈(s.erase i).erase j, ∑ l∈((s.erase i).erase j).erase k, e i k * e j l * f ((((s.erase i).erase j).erase k).erase l) := by
  have ha : j∈s.erase i := Finset.mem_erase.mpr ⟨hd.symm,hj⟩
  unfold Deb; rw [← Finset.add_sum_erase _ _ ha]; apply congrArg _; refine Finset.sum_congr rfl (fun b hb=>?_)
  rw [H ((s.erase i).erase b) (lt_of_le_of_lt (Finset.erase_subset ..) (Finset.erase_ssubset hi)) j (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1.symm,ha⟩)]; unfold Deb; simp_rw [Finset.mul_sum,Finset.erase_right_comm (s:=s.erase i) (a:=b) (b:=j), ← mul_assoc]
lemma loopEq (a b : I→ℂ) (u : Finset I) : (∑ i∈u, ∑ j∈u.erase i, a i*b j*f ((u.erase i).erase j)) = ∑ j∈u,∑ i∈u.erase j,b j*a i*f ((u.erase j).erase i) := by
  have he (i k : I) : ((u.erase i).erase k)=((u.erase k).erase i) := Finset.erase_right_comm ..
  let P (i j:I):=if i=j then 0 else a i*b j*f ((u.erase i).erase j)
  have ha i (hi : i∈u) : (∑ j∈u,P i j)=∑ j∈u.erase i,a i*b j*f ((u.erase i).erase j) := by rw [← Finset.add_sum_erase _ _ hi,show P i i=0 from if_pos rfl,zero_add]; exact Finset.sum_congr rfl fun j hj=> if_neg (Ne.symm ((Finset.mem_erase.mp hj).1))
  have hh j (hj:j∈u) : (∑ i∈u,P i j)=∑ i∈u.erase j,b j*a i*f ((u.erase j).erase i) := by rw [← Finset.add_sum_erase _ _ hj,show P j j=0 from if_pos rfl,zero_add]; exact Finset.sum_congr rfl fun i hi=> by unfold P; rw [if_neg ((Finset.mem_erase.mp hi).1),he, mul_comm (b j)]
  exact (Finset.sum_congr rfl ha).symm.trans (Finset.sum_comm.trans (Finset.sum_congr rfl hh))
lemma chosen (ht : ∀ i j,e i j=e j i) (H : ∀ s : Finset I,s.card • f s=∑ i∈s,Deb e f s i) (s : Finset I) (i : I) (hi : i∈s): f s=Deb e f s i := by
  induction s using Finset.strongInduction generalizing i with
  | H s ih=>
    have he (j : I) (hj : j∈s) : Deb e f s j = Deb e f s i := by
      by_cases hx : i=j; · rw [hx]
      rw [ledger e f (Ne.symm hx) hj hi ih, ledger e f hx hi hj ih, Finset.erase_right_comm (s:=s) (a:=j) (b:=i), ht j i]; exact congrArg _ (loopEq f (e j) (e i) _)
    have hh : (s.card:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Finset.card_pos.2 ⟨i,hi⟩)
    have h:= (H s).trans ((Finset.sum_congr (g:=fun _=> Deb e f s i) rfl he).trans (Finset.sum_const _)); simp_rw [nsmul_eq_mul] at h; exact mul_left_cancel₀ hh h
end algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsGaussian μ]
abbrev Query (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E→L[ℝ] ℂ
def coins (a b : Query E) := ∫ x,a x * b x ∂μ
def Laugh (a : Query E) := (∫ x,a x ∂μ)=0
def team {I : Type*} (z : I→Query E) (s : Finset I) := ∫ x,∏ a∈s,z a x ∂μ
lemma task {I : Type*} [DecidableEq I] (L : I→Query E) (s : Finset I) (i : I) (hi : i∈s) (h : ∀ a,Laugh μ (L a)) : team μ L s=Deb (fun a b=>coins μ (L a) (L b)) (team μ L) s i := by
  -- extend to any finite chosen.
  apply chosen _ _ (fun i j=>congrArg (fun F:E→ℂ=>∫ x,F x ∂μ) (funext (fun x=>mul_comm (L i x) (L j x)))) _ s i hi
  intro s'; let P:=fun i:↥s'=>L i.val; let a:Finset ↥s':=Finset.univ
  have e := exchange_s μ a P (fun i _=>h i.val); unfold kick at e
  have hr : s'.card • team μ L s'=∑ b : ↥s',Deb (fun a b=>coins μ (P a) (P b)) (team μ P) a b := by
    rw [show s'.card = a.card by simp [a],show team μ L s'=team μ P a from congrArg (fun f:E→ℂ=>∫ x,f x ∂μ) (funext (fun x=>(Finset.prod_coe_sort s' (fun a=>L a x)).symm))]; exact e
  unfold Deb; rw [hr, ← Finset.sum_coe_sort (s:=s')]; unfold Deb; refine Finset.sum_congr rfl fun b _=> Finset.sum_bij (fun c _=> c.val) (fun c hc=>?_) (fun j _ i _ he=>?_) (fun i hi=> ?_) (fun i hi=> congrArg _ ?_)
  · exact Finset.mem_erase.mpr ⟨Subtype.val_injective.ne (Finset.mem_erase.mp hc).1,c.property⟩
  · exact Subtype.ext he
  · obtain ⟨hh,hx⟩:=Finset.mem_erase.mp hi
    exact ⟨⟨i,hx⟩,Finset.mem_erase.mpr ⟨fun e=>hh (congrArg Subtype.val e), Finset.mem_univ _⟩,rfl⟩
  apply congrArg (fun f:E→ℂ=>∫ x,f x ∂μ); ext1 y; refine Finset.prod_bij (fun c _=> c.val) (fun c hc=> ?_) (fun d _ e _ h=>Subtype.ext h) (fun d hd=>?_) (fun d _=>rfl)
  · rw [Finset.mem_erase,Finset.mem_erase] at hc ⊢; exact ⟨Subtype.val_injective.ne hc.1,Subtype.val_injective.ne hc.2.1,c.property⟩
  rw [Finset.mem_erase,Finset.mem_erase] at hd; refine ⟨⟨d,hd.2.2⟩, Finset.mem_erase.mpr ⟨fun h=> hd.1 (congrArg Subtype.val h), Finset.mem_erase.mpr ⟨fun h=>hd.2.1 (congrArg Subtype.val h),Finset.mem_univ _⟩⟩,rfl⟩
lemma term_add (L : ℕ→Query E) (Y : Query E) (s : Finset ℕ) (hY : Laugh μ Y) (h : ∀ n,Laugh μ (L n)) : (∫ x,Y x * ∏ a∈s,L a x ∂μ) = ∑ a∈s,coins μ Y (L a) * team μ L (s.erase a) := by
  obtain ⟨z,hz⟩ := Infinite.exists_notMem_finset s
  let P:=update L z Y; let S:=insert z s
  have he : ∀ n,Laugh μ (P n) := fun i=> by
    unfold P; by_cases ht:i=z
    · rw [ht,update_self]; exact hY
    rw [update_of_ne ht]; exact h i
  have hp(s' : Finset ℕ) (h': z∉s') x : (∏ i∈s',P i x)=∏ i∈s',L i x := Finset.prod_congr rfl fun i hi=>by rw [show P i=L i from update_of_ne (ne_of_mem_of_not_mem hi h') _ _]
  rw [show _=team μ P S from congrArg (fun f:E→ℂ=>∫ x,f x ∂μ) (funext (fun x=> (by rw [show S=insert z s from rfl, Finset.prod_insert hz,hp s hz,show P z=Y from update_self ..]))),task μ P S z (Finset.mem_insert_self ..) he]
  unfold Deb; rw [show S.erase z=s from Finset.erase_insert hz]
  exact Finset.sum_congr rfl fun i hi=> by dsimp only; rw [show P z=Y from update_self .., show P i=L i from update_of_ne (ne_of_mem_of_not_mem hi hz) _ _]; unfold team; simp_rw [hp (s.erase i) (fun hh=>hz (Finset.erase_subset i s hh))]
end YM.RG11.FirstW.Deck
