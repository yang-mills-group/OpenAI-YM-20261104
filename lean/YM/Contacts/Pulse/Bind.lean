import YM.Contacts.Pulse.Pluck
/-! Rank-preserving norm with soft zero. Under true A0 bounds of Stacks in
raw advance. After Fourier division no period constants. Our representation
uses the full LOG link components. Their transversality can also be read in
profileDatum/ray normalization; not asserting whole tree transport is this map. -/
noncomputable section
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal ENNReal
variable {α β X Y Z: Type}{t n:ℕ}
variable {L:Side}{σ η τ:ℝ≥0} {s:Tailor t}{f: Shift (Keys t)→ℝ}
def backpack (v:Cover) : Equiv.Perm (Node α) := Equiv.prodCongr (Equiv.addRight v) (Equiv.refl _)
def shuttle (u: Fin (t+1)) (v:Cover) : Equiv.Perm (Breed t (Node α)) := Equiv.piCongrRight fun i=> if i=u then backpack v else Equiv.refl _
lemma shuttle_rule (u:Fin (t+1))(v:Cover)(p:Breed t (Node α))(j: Fin (t+1)): shuttle u v p j=(if j=u then ((p j).1+v,(p j).2) else p j) := by unfold shuttle; by_cases h:j=u <;> simp only [Equiv.piCongrRight_apply,Pi.map_apply,h,↓reduceIte] <;> rfl
lemma shuttle_alpha (u: Fin (t+1))(v:Cover)(p:Breed t (Node α)): alphabet (shuttle u v p)=alphabet p:= by funext; simp only [alphabet, comp_apply,shuttle_rule]; split <;> rfl
lemma shuttle_deg (i:Keys t)(p:Breed t (Node α)): degree (shuttle i.1.succ (Lattice.step i.2) p)=degree p+arc i:= by
  ext k; rcases i with ⟨i,j⟩; rcases k with ⟨u,v⟩; by_cases he:u=i <;> by_cases hx:v=j <;> simp [degree,shuttle_rule,he,hx,arc,Ne.symm (Fin.succ_ne_zero i)] <;> omega
lemma rail_pack (G:Fin (t+1)→ X→Y→ℝ)(p:Fin (t+1)→ X)(q:Fin (t+1)→ Y)(s:Fin (t+1)): ∏ j:Fin (t+1),G j (p j) (q j)=G s (p s) (q s)*(∏ j∈univ.erase s, G j (p j) (q j)):= (mul_prod_erase univ (fun j => G j (p j) (q j)) (mem_univ _)).symm
variable [Fintype α][Fintype β]
-- gate proof as thought.
variable {R:Fin (t+1)→Cross L α β}{ρ:ℝ≥0}{c d: Fin (t+1)→ℝ}{C D: ℝ}
lemma waltz (H:Ripple (terrain σ α) (terrain η β) (access L η)) (hz:(2*σ:ℝ)≤τ) (i:Keys t) (h:Width τ C f) (ho:Odd L.val) (hR:∀ j, Weirs (access L η) (install (R j)) (c j) (d j)) (b:Breed t α):
    allAt (install ∘ R) (flag b (counter i f))=allAt (install ∘ (update R i.1.succ (forwardC L (R i.1.succ) i.2))) (flag b f) := by
  let s:= i.1.succ; let H0:= install ∘ R; let F:= flag b f; let A:= flag b (ascend i f)
  have hu (p): flag b (counter i f) p=A p-F p:= by dsimp [A,F,flag,counter]; split <;> simp
  funext y
  let t (G:Fin _ → Node α→ Node β→ℝ) (F: Breed t (Node α)→ℝ) p:= F p*∏ i,G i (p i) (y i) -- local def name shadows!!!
  have hs : Summable (t H0 F):= (all_summable (flag_price h hz) H hR y).of_norm
  have he : Summable (t H0 A):= (all_summable (flag_price (upward i h) hz) H hR y).of_norm
  let e:= shuttle s (Lattice.step i.2) (α:=α)
  have hx : t H0 A∘ e - t H0 F = t (install ∘ (update R i.1.succ (forwardC L (R i.1.succ) i.2))) F := funext fun x=> by
    have hp : A (e x)=F x := by rw [show e=shuttle i.1.succ (Lattice.step i.2) from rfl]; simp only [A,F,flag,shuttle_alpha,shuttle_deg,ascend,add_sub_cancel_right]
    simp only [Function.comp_apply,Pi.sub_apply,t,hp]; rw [← _root_.mul_sub]; congr 1
    simp only [e]; rw [rail_pack H0 _ _ s,rail_pack H0 _ _ s,rail_pack (fun j=> install (update R i.1.succ (forwardC L (R i.1.succ) i.2) j)) _ _ s]; dsimp only [H0,s,comp_apply]; rw [shuttle_rule,if_pos rfl,update_self,install_forward _ ho,_root_.sub_mul]; simp only [Prod.mk.eta]
    apply congr_arg₂ (·-·); · congr 1; apply prod_congr rfl; intro j hj; rw [shuttle_rule,if_neg (mem_erase.mp hj).1,update_of_ne (mem_erase.mp hj).1]
    congr 1; apply prod_congr rfl; intro j hj; rw [update_of_ne (mem_erase.mp hj).1]
  change _=tsum _; unfold allAt
  change _=tsum (t (install ∘ update R _ _) F)
  rw [← hx]; change _=∑' i, ((t H0 A ∘ e) i - t H0 F i); rw [(e.summable_iff.mpr he).tsum_sub hs]
  simp_rw [hu,_root_.sub_mul]; exact (he.tsum_sub hs).trans (by rw [show ∑' i,(t H0 A ∘ e) i=∑' i,t H0 A i from e.tsum_eq _])

lemma dryrail {F: Breed t (Node α)→ℝ}{c':ℝ} (h:Rooted (terrain σ α) F c') (hl: (η:ℝ)/(L.val:ℝ)≤σ) (a:ℝ)(ha:0≤a)(H:∀ i : Fin (t+1), Weirs (access L η) (install (R i)) (a*d i) (d i)) : Rooted (terrain η β) (allAt (install ∘ R) F) (a*c'*∏ i,d i) := by
  have hc := h.cash; have hv := fun i=>(H i).right; refine all_root h (influx hl) H (fun i=> ?_) (by exact mul_nonneg (mul_nonneg ha hc) (prod_nonneg fun j _=> hv j))
  letI : DecidableEq (Fin (t+1)) := fun a b=>Classical.propDecidable (a=b); apply le_of_eq; rw [← Finset.mul_prod_erase univ d (mem_univ i)]; ring
lemma Weirs_reserve {x:X→Y→ℝ}{u v a b:ℝ}{F:X→Y→ℝ} (h:Weirs x F u v)(ha:u≤a)(hb:v≤b) : Weirs x F a b:= ⟨h.left.trans ha,h.right.trans hb,fun y=>budget_loosen (h.columns y) ha,fun x=>budget_loosen (h.rows x) hb⟩
def foot (α β:Type)[Fintype α][Fintype β] :ℝ:= max (Fintype.card α:ℝ) ↑(Fintype.card β)
lemma straight (h : (R i).strip η C)(hC:0≤ C): Weirs (access L η) (install (R i)) ((L.val:ℝ)^4*(foot α β * beamPrice η C)) (foot α β*beamPrice η C):= by
  have hu := Real.exp_pos ((η:ℝ)*2); have ha : 0≤ beamPrice η C:= mul_nonneg hu.le hC
  refine Weirs_reserve (flow_price h hC) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) ha); rw [mul_assoc ((L.val:ℝ)^4) ↑(Fintype.card α) (beamPrice η C)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left ..) ha) (by positivity)
lemma runway (b:Breed t α)(hz:(2*σ:ℝ)≤τ) (H:Ripple (terrain σ α) (terrain η β) (access L η)) (hL:(η:ℝ)/(L.val:ℝ)≤σ)(ho:Odd L.val) (h: Width τ C f) (l:Fin n→Keys t)(hc:0≤ D)
    (u:Fin (t+1)→List Axis) (hs:∀ i (k:List Axis), k.length ≤ (u i).length+n → Row.strip (advanceC L (R i) k) η (D/(L.val:ℝ)^(1+k.length))):
    Rooted (terrain η β) (allAt (fun i=> install (advanceC L (R i) (u i))) (flag b (torn l f)))
      ((((L.val:ℝ)^4*C)* (∏ i,foot α β*beamPrice η (D/(L.val:ℝ)^(1+(u i).length)))) / (L.val:ℝ)^n) := by
  let d (k:List Axis) := foot α β*beamPrice η (D/(L.val:ℝ)^(1+k.length)); let a := ((L.val:ℝ)^4)
  have hu (v:List Axis) (i) (hv: v.length≤(u i).length+n) : Weirs (access L η) (install (advanceC L (R i) v)) (a*d v) (d v):= by
    exact straight (R:=fun i : Fin (t+1)=>advanceC L (R i) v) (hs i v hv) (by have := side_pos L; positivity)
  have hx j:= hu (u j) j (Nat.le_add_right ..)
  induction n generalizing u with
  | zero=> rw [torn_zero,pow_zero,div_one]; exact dryrail (flag_price h hz) hL a (by unfold a; positivity) hx
  | succ k IH=>
    let j:= l 0; let s:= j.1.succ; let v i:= update u s (j.2::u s) i
    have hh (i:Fin (t+1)): (v i).length+k ≤ (u i).length+(k+1):= by by_cases he:i=s <;> simp [v,he] <;> omega
    have hr : update (fun i=> advanceC L (R i) (u i)) s (forwardC L (advanceC L (R s) (u s)) j.2) = (fun i=> advanceC L (R i) (v i)) := by funext i; by_cases he:i=s <;> simp [he,v,advanceC]
    change Rooted _ (allAt (install ∘ (fun i=> advanceC _ _ _)) _) ((a*C*(∏ i,d (u i))) / _)
    rw [torn_succ,waltz H hz _ (tear_cap h _) ho (R:=fun i => advanceC _ _ (u i)) hx b,hr]; change Rooted _ (allAt (fun i=> install (advanceC L (R i) (v i))) _) _
    have hc (i):0 < (L.val:ℝ)^i := pow_pos (side_pos L) i
    have he : (∏ i,d (v i))= (∏ i,d (u i))/(L.val:ℝ):= by
      rw [← mul_prod_erase univ (fun i=>d (v i)) (mem_univ s),← mul_prod_erase univ (fun i=>d (u i)) (mem_univ s),mul_div_right_comm]; apply congr_arg₂ _
      · change d (v s)=_; unfold d v; simp only [Function.comp_apply,update_self,List.length_cons,beamPrice]; rw [← add_assoc,pow_succ]; field_simp
      exact prod_congr rfl fun i hi=> congr_arg d (update_of_ne (mem_erase.mp hi).1 ..)
    have hw := IH (Fin.tail l) v (fun i k he=> hs i k (he.trans (hh i))) (fun k i he=> hu _ _ (by have:=hh i; omega)) (fun i=> hu _ _ (by have:=hh i; omega))
    change Rooted _ _ ((a*C*(∏ i,d (v i))) / (L.val:ℝ)^k) at hw
    rw [he] at hw; convert hw using 1; field_simp; ring
end YM.Pulse.Spine
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal ENNReal
variable {α β X Y Z E ι: Type}{t n:ℕ}
def softRank (n:ℕ) (F:Breed t (Node α)→ℝ) := ∀ b:Breed t α, Rays n (Laurent.read (pale (extract F b)) ∘ axes)
section sums
variable [Fintype Z][Fintype ι][NormedAddCommGroup E]{F:Z→(ι→X)→E} {c: Z→ℝ}
lemma massSum {l:Range X}(h:∀ z,Rooted l (F z) (c z)): Rooted l (fun x=>∑ z,F z x) (∑ z,c z):= ⟨sum_nonneg fun i _=> (h i).cash, fun i a=> budget_collect (s:=univ) (v:=fun x:Locked X i a=>l.bill x.val) (fun _=>by positivity) (fun z _=>(h z).row i a)⟩
variable [Nonempty ι]{l:Range X} {m:Range Y}{t:X→Y→ℝ}{V:ι→X→Y→ℝ}{a b:ι→ℝ}{F: Z→Field ι X}
lemma spillSum (H:Ripple l m t)(hW:∀ i,Weirs t (V i) (a i) (b i)) (h:∀ i,Rooted l (F i) (c i)): allAt V (fun x=>∑ z,F z x)=(fun y=>∑ z,allAt V (F z) y):= funext fun y=> by unfold allAt; simp_rw [sum_mul]; rw [Summable.tsum_finsetSum (fun i _=> (all_summable (h i) H hW y).of_norm)]
end sums
/-! Before-length, before-period, independent even of inherited budget C. Rank t+1 ≤ r.
 Choose RHS width at coarser scale satisfying the given Mean strip (h); the input demands ν from
 the output length-to-width conversion. -/
theorem panorama {σ η:ℝ≥0}(t n : ℕ) (α β: Type)[Fintype α][Fintype β] (hs:0<σ){D:ℝ}(hD:0≤D) : ∃ ν:ℝ≥0,0<ν ∧ ν≤σ ∧ ∃ K:ℝ,0≤K ∧ ∀ (L:Side), Odd L.val → (η:ℝ)/(L.val:ℝ)≤ν → ∀ (R: Fin (t+1)→Cross L α β),
    (∀ i (l:List Axis), l.length ≤ n → Row.strip (advanceC L (R i) l) η (D/(L.val:ℝ)^(1+l.length))) → ∀ (C:ℝ)(F:Breed t (Node α)→ℝ),
    Rooted (terrain σ α) F C → author (extract F)=F → softRank n F → Rooted (terrain η β) (allAt (install ∘ R) F) (C*K*(L.val:ℝ)^4/(L.val:ℝ)^(t+1+n)) := by
  let x:ℝ≥0:= σ / (t+1); have hx : 0<x:= div_pos hs (by positivity); obtain ⟨τ,hτ,ht,K,hK,H⟩:= pry x t n hx; let ν:= τ/2
  let p:= foot α β*beamPrice η D
  let k:= Fintype.card (Breed t α × (Fin n→Keys t))
  have hp : 0≤ p:= mul_nonneg ((Nat.cast_nonneg _).trans (le_max_right ..)) (by unfold beamPrice; positivity)
  have hz : 2* (ν:ℝ)≤ τ:= by simp only [ν,NNReal.coe_div,NNReal.coe_ofNat]; linarith
  refine ⟨ν,div_pos hτ (by norm_num),(div_le_self (by positivity) (by norm_num)).trans (ht.trans (div_le_self (by positivity) ?_)),↑k*K*p^(t+1),by positivity,fun L hL hu R h C F hf hf' hw=>?_⟩; · simp
  have hQ : 0 < (L.val:ℝ) := side_pos L; have he i:= export_price (η:=x) hf i (show (t:ℝ)*x≤ σ from by
    have ht : (t:ℝ)*x≤ (t+1:ℝ)*x := by gcongr; linarith
    simp only [x,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at *; exact ht.trans (le_of_eq (by field_simp)))
  choose G HG hG using fun b => H C _ (he b) (hw b)
  let A:= Breed t α× (Fin n→Keys t)
  let g (q:A):= torn q.2 (G q.1 q.2); let U (q:A):=flag q.1 (g q)
  have hm : F=(fun i=>∑ q:A,U q i):= funext fun i=> by
    rw [←congr_fun hf' i,authors,Fintype.sum_prod_type]; apply sum_congr rfl; intro b _
    unfold U flag g; rw [hG]; split_ifs <;> simp [Finset.sum_apply]
  have hv i:= (h i [] (by simp)); have hh : ∀ i, Weirs (access L η) (install (R i)) ((L.val:ℝ)^4*(foot α β*beamPrice η (D/(L.val:ℝ)^1))) (foot α β*beamPrice η (D/(L.val:ℝ)^1)):= fun i=> straight (hv i) (by positivity)
  rw [hm,spillSum (F:=U) (V:=install ∘ R) (influx (α:=α) (β:=β) hu) hh (fun q:A=> flag_price (b:=q.1) (tear_cap (HG q.1 q.2) q.2) hz)]
  have hq (q:A): Rooted (terrain η β) (allAt (install ∘ R) (U q)) (((L.val:ℝ)^4*(C*K))* (p/L.val)^(t+1)/(L.val:ℝ)^n):= by
    have hr := runway q.1 hz (influx (β:=β) hu) hu hL (HG q.1 q.2) q.2 hD (fun _=>[]) (fun i k he => h i k (by simpa using he))
    have he : foot α β * beamPrice η (D/(L.val:ℝ))=p/L.val := by unfold beamPrice p; field_simp
    simpa only [advanceC,U,g,Function.comp_def,List.length_nil,add_zero,pow_one,he,prod_const,card_univ,Fintype.card_fin] using hr
  convert massSum hq using 1; simp only [sum_const, card_univ,nsmul_eq_mul,k,div_pow,pow_add]; field_simp; ring
-- Deduct common L^-1 if horizon threshold
lemma angled (α β: Type)[Fintype α][Fintype β] {σ η:ℝ≥0}(t : ℕ)(hs:0<σ){D:ℝ}(hD:0≤D) : ∃ ν:ℝ≥0,0<ν ∧ ν≤σ ∧ ∃ K:ℝ,0≤K ∧ ∀ L:Side, Odd L.val → (η:ℝ)/(L.val:ℝ)≤ν → ∀ R: Fin (t+1)→Cross L α β,
    (∀ i (l:List Axis), l.length ≤ 4-t → Row.strip (advanceC L (R i) l) η (D/(L.val:ℝ)^(1+l.length))) → ∀ (C:ℝ)(F:Breed t (Node α)→ℝ), Rooted (terrain σ α) F C → author (extract F)=F → softRank (4-t) F → Rooted (terrain η β) (allAt (install ∘ R) F) (C*K/(L.val:ℝ)) := by
  obtain ⟨ν,hν,hu,K,hK,H⟩:= panorama (σ:=σ) (η:=η) t (4-t) α β hs hD; refine ⟨ν,hν,hu,K,hK,fun L hL hw R h C F hf hf' hv=> (H L hL hw R h C F hf hf' hv).weaken (fun _=> le_rfl) ?_⟩
  have hh := side_pos L; have ha := hf.cash; apply le_trans _ (le_of_eq (show C*K*(L.val:ℝ)^4/(L.val:ℝ)^5=C*K/L.val from by field_simp))
  gcongr; · exact_mod_cast L.pos
  omega
end YM.Pulse.Spine
