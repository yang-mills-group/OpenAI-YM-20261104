import YM.WilsonCoeffUV.Vacuum.Gain.Share
/-!
# Choose an internal label, telescope without a fiber cardinal ratio
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r:ℕ}{α β V J :Type*}{s t t' σ B C D E:ℝ}{L:Side}

def reverseK (i:Fin (r+1)): Equiv.Perm (Fin (r+1)):= Equiv.swap i 0
def enlist (i: Fin (r+1))(u:J)(p:Fin r→J): Fin (r+1)→J:= Fin.cons u p ∘ reverseK i
def aside (i:Fin (r+1))(p:Fin (r+1) → J): Fin r→J:= Fin.tail (p ∘ (reverseK i).symm)
lemma enlist_it (i:Fin (r+1))(u:J)(p:Fin r→J): enlist i u p i=u:=by simp [enlist,reverseK]
lemma leaves (i:Fin (r+1))(p:Fin (r+1)→J): enlist i (p i) (aside i p)=p:=by unfold enlist aside; rw [show p i=(p ∘ (reverseK i).symm) 0 by simp [reverseK], Fin.cons_self_tail]; exact funext fun i=>by simp
lemma outside (i:Fin (r+1))(p:Fin r→J)(u:J): aside i (enlist i u p)=p := by unfold aside enlist; simp only [Function.comp_assoc, Equiv.self_comp_symm, comp_id, Fin.tail_cons]
def visitJ (J:Type*) (i:Fin (r+1)): ((Fin r→J)× J) ≃ (Fin (r+1)→J) where
   toFun p:=enlist i p.2 p.1
   invFun x:=(aside i x,x i)
   left_inv _:=Prod.ext (outside ..) (enlist_it ..)
   right_inv _:=leaves ..
lemma remote {i b:Fin (r+1)}(h:b≠i)(p:Fin r→J)(u z:J): enlist i u p b=enlist i z p b:=by
    unfold enlist; simp only [Function.comp_apply]; have he : reverseK i b ≠0:=by rw [← show reverseK i i=0 by unfold reverseK; rw [Equiv.swap_apply_left]]; exact (reverseK i).injective.ne h
    obtain ⟨x,hx⟩:=Fin.exists_succ_eq.mpr he; rw [← hx, Fin.cons_succ,Fin.cons_succ]

abbrev Talus (G:Gauge)(β:Type*)(r:ℕ):= Grazing (Hooks G) r→Cover→G.ColorIndex→Cloth β→ℝ

def apex (i:Fin (r+1))(U:Talus G β r): Roof (Hooks G) β (r+1):= fun p=> U (aside i p) (p i).1 (p i).2.2

def reedG (i:Fin (r+1))(U:Talus G β r): Roof (Hooks G) β (r+1):= fun p x=> U (aside i p) ((p i).1+step (axisEquiv.symm (p i).2.1)) (p i).2.2 x - apex i U p x

def dormant {α:Type*}(i:Fin (r+1))(P:Roof α β (r+1)):Prop:= ∀ p:Grazing α r,∀ u v : Cloth α,P (enlist i u p)=P (enlist i v p)

-- one color-direction column over ALL sites.
def booths (G:Gauge): ((G.ColorIndex × Axis) × Cover) ≃ YForest G where
  toFun p:= waive p.2 p.1.2 p.1.1
  invFun p:= ((p.2.2, axisEquiv.symm p.2.1),p.1)
  left_inv _:= by simp only [waive,stone, ← coord_map, Equiv.symm_apply_apply]
  right_inv p:= by simp only [waive,stone, ← coord_map, Equiv.apply_symm_apply]

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def ledger (P: Ten V (YForest G) (r+1))(i: Fin (r+1)) : Ten V (YForest G) (r+1):= fun x=> if (x i).2.1=coord 0 then windsL (x i).1 (x i).2.2 P (aside i x) else 0
omit [NormedSpace ℝ V] in
lemma ledger_pay {P: Ten V (YForest G) (r+1)}(p:Draft P s B)(i): Amber terrain s B (ledger P i):=by
   refine ⟨p.1,fun x=>?_⟩; unfold ledger; split; swap; · rw [norm_zero]; exact mul_nonneg p.1 (by positivity)
   refine ((p.2 ..).2 (aside i x)).trans_eq ?_; congr 3
   rw [show port_d (x i).1 _=soar terrain (enlist i (x i) (aside i x)) from ?_, leaves]
   unfold enlist; unfold soar; rw [← comp_assoc,league_equiv]; exact (port_soar _ _).symm

private lemma by_talus {P:Ten V (YForest G) (r+1)}(i:Fin (r+1))(U:Talus G β r){R : Fin (r+1)→ Roof (Hooks G) β (r+1)} (h:R i=reedG i U)(x y)(a:Axis)(b:G.ColorIndex)(v:Cover)(Z) (he:(∏ j∈Finset.univ.erase i, R j (enlist i (waive v a b) y) (x j))=Z):
    spinJob P R x (enlist i (waive v a b) y)= (Z*(U y (v+step a) b (x i)-U y v b (x i))) • P (enlist i (waive v a b) y):=by
   rw [spinJob,update_prod _ i, he,h,reedG,apex, enlist_it,outside]; simp only [waive,stone, ← coord_map, Equiv.symm_apply_apply,mul_comm Z]

private lemma tally1 {P: Cover→ Axis→ V}{t: Cover→ℝ}{u:Cover→Axis→ V}
    (h:∀ x j, u x j=(t (x+step j)- t x) • P x j) (e:∀ j : Axis,Summable fun x: Cover=> u x j) (g:∀ j : Axis, Summable fun x:Cover=>t x • P x j):
   ∑ j,∑' x,u x j= -(∑' x,t x • ∑ j:Axis,(P x j-P (x-step j) j)):= by
   have hv (j): Summable fun x: Cover=> t (x+step j) • P x j:= by
      apply ((e j).add (g j)).congr
      intro x; rw [h, sub_smul, sub_add_cancel]
   have hx (j) : Summable fun x: Cover=> t x • P (x-step j) j:= by
      apply (Equiv.addRight (step (S:=ℤ) j)).summable_iff.mp; refine (hv j).congr fun x=> by simp
   simp_rw [Finset.smul_sum, smul_sub]
   rw [Summable.tsum_finsetSum (fun j _=> (g j).sub (hx j)), ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _
   simp_rw [h,sub_smul]; rw [(g j).tsum_sub (hx j),(hv j).tsum_sub (g j),neg_sub]; rw [← (Equiv.addRight (step (S:=ℤ) j)).tsum_eq (fun x=> t x • P (x-step j) j)]; simp

variable [CompleteSpace V]
lemma tally2 {P: Ten V (YForest G) (r+1)}(i:Fin (r+1))(H:Smooth P)(U: Cover→G.ColorIndex→ℝ) (u:Grazing (Hooks G) r)
    (F Q:YForest G→ V)(h:Summable F)(g:Summable Q)(hx:∀ x:Cover,∀ k d, F (waive x d k)=(U (x+step d) k-U x k) • P (enlist i (waive x d k) u))
    (hv:∀ j: YForest G,Q j= U j.1 j.2.2 • ledger P i (enlist i j u))(hp:Summable (fun y:YForest G=> U y.1 y.2.2 • P (enlist i y u))) : ∑' y,F y= -(∑' y,Q y):= by
   let K:= booths G; have he:= K.summable_iff.mpr h; have H':= K.summable_iff.mpr g; have ht:= K.summable_iff.mpr hp
   unfold Function.comp at *
   rw [← K.tsum_eq F,← K.tsum_eq Q, he.tsum_prod,H'.tsum_prod,tsum_fintype,tsum_fintype,Fintype.sum_prod_type,Fintype.sum_prod_type,← Finset.sum_neg_distrib]
   apply Finset.sum_congr rfl; intro j _
   let p (x:Cover) (v:Axis):= P (Fin.cons (waive x v j) u)
   have hm (x:Cover)(v): P (enlist i (waive x v j) u)=p x v:= H (reverseK i) _
   have hc x v:F (K ((j,v),x))=(U (x+Lattice.step v) j-U x j) • p x v := by specialize hx x j v; rw [hm x v] at hx; exact hx
   have hS (v:Axis) : Summable fun x:Cover=> U x j • p x v:= by
      apply (ht.prod_factor (j,v)).congr; intro x; change U x j • P _= _; exact congr_arg (U x j • ·) (hm x v)
   have hz:=tally1 (u:=fun x v=>F (K ((j,v),x))) (P:=p) (t:=fun x=> U x j) hc (fun v=> he.prod_factor (j,v)) hS
   apply hz.trans; congr 1; symm
   rw [Finset.sum_eq_single (0:Axis)]
   · apply tsum_congr; intro x; change Q (waive x 0 j)=_
     rw [hv (waive _ _ _),ledger,enlist_it,outside,if_pos (show (waive x 0 j).2.1= coord 0 from rfl)]; congr 1
   · intro k _ h'
     have hz x : Q (K ((j,k),x))=0:= by rw [hv,ledger,enlist_it,if_neg, smul_zero]; exact mt (coord_iff ..).mp h'
     simp_rw [hz,tsum_zero]
   simp

omit [NormedSpace ℝ V] in
lemma eyeY (i:Fin (r+1))(F Q:Grazing α (r+1)→V)(h:Summable F)(g:Summable Q)(e:∀ p:Grazing α r,(∑' a: Cloth α, F (enlist i a p))= -(∑' a: Cloth α,Q (enlist i a p))): ∑' x,F x= -(∑' x,Q x):=by
   let L:=visitJ (Cloth α) i
   have hv:= L.summable_iff.mpr h; have hq:=L.summable_iff.mpr g; unfold Function.comp at hv hq; rw [← L.tsum_eq F,← L.tsum_eq Q,hv.tsum_prod,hq.tsum_prod,←tsum_neg]
   exact tsum_congr fun p=>e p

-- analytic contraction oracle (gradient column permitted polynomial in inputs)
theorem sling {P: Ten V (YForest G) (r+1)}(i:Fin (r+1))(U:Talus G β r){R: Fin (r+1)→ Roof (Hooks G) β (r+1)}(e:R i=reedG i U)(h:∀ j,sells L s B (R j))(w:∀ j,j≠i→dormant i (R j)) (H:Smooth P) (tK:Amber terrain t C P) (g:Draft P t E) (k : ℕ)(d:sells L s D (Tolled k (apex i U)))(ht:t'<t)(hp:s/L.val≤t')(hv:0≤σ)(ha:σ<s):
    Amber terrain σ ((max B D ^(r+1)*(E*ceilPoly k (t-t')*Real.exp (8*s)))*tiePay (Co L (Hooks G)) (r+1) (s-σ)) (pump P R):= by
    let M:= Function.update R i (apex i U); let F:=ledger P i
    have hc: sells L s D (Tolled k (M i)):= by unfold M; rw [Function.update_self]; exact d
    have he j (hp:j≠i): sells L s B (M j) := by unfold M; rw [Function.update_of_ne hp]; exact h j
    obtain ⟨hl,H'⟩:= chargeToll he hc (ledger_pay g i) ht hp hv ha
    have hw:= (chargeToll he hc tK ht hp hv ha).1
    cases isEmpty_or_nonempty (YForest G)
    case inl he'=>
      have hm:pump P R=0:=by ext1 x; unfold Bank.pump; exact tsum_empty
      rw [hm]; exact Amber.zero.le H'.1
    rename_i hQ
    let K:= visitJ (YForest G) i
    rw [show pump P R= -(pump F M) from ?h]; exact H'.neg
    case h=>
      funext x
      apply eyeY i (spinJob P R x) (spinJob F M x) ((pump_sum h tK (lt_of_le_of_lt hv ha) (hp.trans ht.le) x).of_norm) (hl x)
      intro p
      set A:= ∏ j ∈ Finset.univ.erase i,R j (enlist i (Classical.arbitrary (YForest G)) p) (x j)
      have hx (y:YForest G) : ∏ j∈Finset.univ.erase i,R j (enlist i y p) (x j)=A:= Finset.prod_congr rfl fun j hj=> congr_fun (w j (Finset.mem_erase.mp hj).1 p _ _) _
      let T y k:= A * U p y k (x i)
      have hz (F: Ten V (YForest G) (r+1)) y: spinJob F M x (enlist i y p)= T y.1 y.2.2 • F (enlist i y p):= by
        unfold M T; rw [spin_replace (Z:=apex i U),hx,apex,enlist_it,outside,mul_comm]
      refine tally2 i H T p (fun a=> spinJob P R x (enlist i a p)) (fun a=>spinJob F M x (enlist i a p)) ((K.summable_iff.mpr ((pump_sum h tK (lt_of_le_of_lt hv ha) (hp.trans ht.le) x).of_norm)).prod_factor p) ((K.summable_iff.mpr (hl x)).prod_factor p) (fun y k d=>?_) (hz F) ?_
      · rw [by_talus i U e _ _ d k y A (hx _)]; unfold T; rw [mul_sub]
      exact ((K.summable_iff.mpr (hw x)).prod_factor p).congr (hz P)
end YM.WilsonCoeffUV.Bank
