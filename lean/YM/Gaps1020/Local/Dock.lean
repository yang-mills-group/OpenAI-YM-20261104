import YM.Gaps1020.Local.Widen
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu.GapsLocal
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge  Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
variable (w':Wing)
    {s:B.Mode}
    (H:Config G f→ℂ)
    (v:V→ℝ){d h e b c':ℝ}{o: V→Site f}

/-! # Proofs adapting Donor Menu Prism & Dock to standard log and forced **all modes**. -/

-- trim to active mode correct locality & plate. statement from W produced when only if f i≠0. land fees.Current
variable [Fintype ι] {X:ι→Support f}{F:ι→ Config G f→Poly B}
lemma alarm (hv:∀ i,0<v i) {g:ι→Wing}
    (h:∀ i,F i≠0→ (g i).support R=X i ∧ (g i).blank R)(ht:∀ i U,F i U≠0→ (g i).qualifies R U)
    (hp:∀ i,Borne o (X i) (F i) R.p.threshold)(hx:∀ i U,(F i U).part B.quiet=0)(he:Towed v X F R.p.B d b):∃ (P:VividId F→ Hat B R),
    (∀ i,WKey (P i)=g i.fst ∧ (P i).s=i.2.1.val) ∧ Offer o P v R.p.B d (2*b) ∧ ∀ i U,∑ j:{i':B.Mode // Vivid F i i'} × Bool, amount (P ⟨i,j⟩) U= F i U :=by
   let A(i):= {p:B.Mode// Vivid F i p}; have hh(i) (x:A i): F i≠0:=by obtain ⟨y,hy⟩:=x.property;exact fun ht=> hy (by rw [ht];rfl)
   obtain ⟨w,hw,hW,hB⟩:=he
   choose f hf hs hP using hB
   have hI(i)(x:A i): 1 ≤ x.val.val.card:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (fun e=> by have he : x.val=B.quiet:=Subtype.ext e; obtain ⟨U,h⟩:=x.property; rw [he,hx] at h; contradiction))
   obtain ⟨P,HP,HQ,Hh⟩ : ∃ (u : ∀ i,A i→ Bool→Hat B R), (∀ i p j,WKey (u i p j)=g i ∧ (u i p j).s=p.val) ∧ (∀ i p,∑ l,fare (u i p l) v = 2*(Poly.toll v p.val*f i p.val))∧∀ i p U,∑ l,amount (u i p l) U=Poly.send p.val ((F i U).part p.val):=by
      have he i (p:A i): UsesFinal R.p.threshold ((g i).support R) (fun U=> (F i U).part p.val):= (h i (hh i p)).1.symm ▸ (fun U V hx ht=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).home U V hx ht))
      choose u hu hU hT using fun i p=> couple (R:=R) (g i) (s:=(p:A i).val) (fun U=> (F i U).part p.val) v (he i p) (fun U hv=> ht i U (fun h=> hv (by rw [h];rfl))) (h i (hh i p)|>.2) (hp i|>.me _) (fun t U=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).turns t U)) (fun U=> hs i U _) (Finset.card_pos.mp (show 0 < p.val.val.card from (hI ..)))
      exact ⟨u,hu,hU,hT⟩
   let P' (i:VividId F): Hat B R:= P i.1 i.2.1 i.2.2
   have hz i (j:A i×Bool): (P' ⟨i,j⟩).M.crest=X i:=by rw [show (P' ⟨i,j⟩).M.crest=(g i).support R from congr_arg (fun i:Wing=>i.support R) (HP i j.1 j.2).1]; exact (h i (hh i j.1)).1
   -- CORE
   refine ⟨P',fun i=>HP ..,⟨fun i=>?_,fun i=>?_⟩,fun i U=>?_⟩
   · rcases i with ⟨i,j⟩; rw [hz,show (P' ⟨i,j⟩).s=j.1.val from (HP ..).2]; exact (hp i).place _ _ j.1.property.choose_spec
   · refine ⟨fun i=>?_,Summable.of_finite,?_⟩
     · dsimp only; split; exact mul_nonneg (Crew v hv) (Real.exp_pos _).le;rfl
     apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap (hW i) univ) zero_le_two)
     rw [tsum_fintype,Fintype.sum_sigma, Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; dsimp only
     by_cases hx:i∈X j
     · let Z:= Real.exp (d*coverNumber R.p.B (X j)); have hN(y : A j × Bool):
           (if i∈ (P' ⟨j,y⟩).M.crest then fare (P' ⟨j,y⟩) v*Real.exp (d*coverNumber R.p.B (P' ⟨j,y⟩).M.crest) else 0)= Z*fare (P j y.1 y.2) v:=by rw [if_pos (show i∈ _ from hz j y|>.symm ▸ hx), hz]; exact mul_comm ..
       rw [if_pos hx,Finset.sum_congr rfl (fun i _=>hN i), ← mul_sum,Fintype.sum_prod_type]; simp_rw [HQ]; rw [← Finset.mul_sum];
       have hu : ∑ i : A j, Poly.toll v i.val*f j i.val≤w j:=by
          rw [← Finset.sum_subtype (p:=Vivid F j) ((univ:Finset B.Mode).filter fun p=> Vivid F j p) (fun i=>by simp) (fun i=> Poly.toll v i*f j i)]; exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _=> mul_nonneg (Poly.worth hv _).le (hf ..)).trans (hP j)
       refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu zero_le_two) (Real.exp_pos _).le).trans_eq ?_; ring
     rw [if_neg hx,mul_zero,sum_eq_zero]; intro y _; exact if_neg ((hz j y).symm ▸ hx) -- cast
   rw [Fintype.sum_prod_type]; simp_rw [P',Hh];
   conv_rhs => rw [← Poly.studs (F i U)]
   classical
   refine (sum_subtype (p:=Vivid F i) (s:= Finset.univ.filter (Vivid F i)) (fun i=>by simp) (fun j=>Poly.send j ((F i U).part j))).symm.trans (sum_subset (subset_univ _) fun j _ h=> ?_)
   have he: (F i U).part j=0:=Classical.byContradiction fun H=> h (mem_filter.mpr ⟨mem_univ _,(show Vivid F i j from ⟨U,H⟩)⟩); simp [he]

section dock
variable {t p a:ℝ}{w:V→ℝ}
variable {T:BudgetPoint} {K:Support f→ Config G f→Poly B} {F':Box f→ Config G f→Poly B}
lemma drydock (h:∀ i,Burns o i (K i) R.p.threshold)(h':∀ i,Flow o i (F' i) R.p.threshold ∧ ∀ U,(F' i U).part B.quiet=0)(he:Towed w id K R.p.B d a)(hq:Towed w (fun i:Box f=>i.1) F' R.p.B d b)(hw:∀ i,0<w i)(hx:Arsenal R):
   ∃ (I:Type) (_:Fintype I)(q:I→Hat B R), Offer o q w R.p.B d (2*a+2*b) ∧ (∀ X U,(∑ i,if (q i).M.crest=X then odour (q i) U else 0)=K X U)∧∀ i U,∑ j,fragrance (q j) U i=F' i U:=by
   have hb(i): K i≠0→i.Nonempty:=by
      intro H; obtain ⟨U,hU⟩:= Function.ne_iff.mp H; obtain ⟨p,hp⟩:= Function.ne_iff.mp (show Poly.part (K i U) ≠ Poly.part 0 from (by intro g; exact hU g)); have ht: p.val.Nonempty:=by apply Finset.nonempty_iff_ne_empty.mpr; intro hv; rw [show p=B.quiet from Subtype.ext hv,(h i).sil] at hp; apply hp; rfl
      exact (ht.image o).mono ((h i).toBorne.place _ _ hp)
   let k(i:Support f) := if H:K i≠0 then (hx.dry i (hb i H)).choose else 0
   let g i:= Wing.logKey (k i); have hK (i)(he:K i≠0): (R.activities.reg (k i)).support=i ∧ R.activities.E (k i)=0:=by unfold k; rw [dif_pos he]; exact (hx.dry i (hb i he)).choose_spec
   have hv(i U)(he:K i U≠0): (g i).qualifies R U:=by change Healthy _ _ U; rw [(hK i (fun hh=> he (congr_fun hh U))).1]; exact ((h i).permits U he)
   obtain ⟨N,hN,H,hn⟩:= alarm w hw (F:=K) (X:=id) (g:=g) (fun i hp=> hK i hp) hv (fun i=>(h i).toBorne) (fun i=>(h i).sil) he
   have hd(i): F' i≠0 → Sure i:=by intro hh; obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; exact ((h' i).1.permits U hU).2
   let L(i: Box f):= if H:F' i≠0 then (hx.wet i (hd i H)).choose else 0
   let l i:= Wing.gasKey (L i); have hF(i)(h:F' i≠0): barcode R.activities (L i)=i ∧ ∀ U,i.1∩RG.flags R.p.threshold U=i.2 → (R.activities.forced (L i)).eligible R.p.threshold U:=by unfold L; rw [dif_pos h]; exact (hx.wet i (hd i h)).choose_spec
   have ht (i U)(he:F' i U≠0): (l i).qualifies R U:=(hF i (fun hh=> he (congr_fun hh U))).2 U (((h' i).1.permits U he).1)
   obtain ⟨M,hM,hB,hm⟩:= alarm w hw (F:=F') (X:=Prod.fst) (g:=l) (fun i hp=> ⟨(Prod.mk.inj (hF i hp).1).1,trivial⟩) ht (fun i=>(h' i).1.toBorne) (fun i=>(h' i).2) hq
   let m:= Sum.elim N M
   have hp(x): (N x).M.turn= .logKey (k x.1):= (hN x).1; have ht(x): (M x).M.turn=.gasKey (L x.1):=(hM x).1
   have hk(i:VividId F'):barcode R.activities (L i.1)=i.1:=(hF _ (fun H=> (show Vivid F' i.1 i.2.1.val from i.2.1.property).elim (fun U hU=> hU (by rw [H]; rfl)))).1
   have hy(U x):odour (N x) U=amount (N x) U:=by unfold odour prose; rw [hp,varnish]
   have hx'(U x):odour (M x) U=0:=by unfold odour prose;simp [ht]
   have hz (U x i):fragrance (N x) U i=0:=by unfold fragrance entry; simp [hp]
   have hs(U x i):fragrance (M x) U i=if x.1=i then amount (M x) U else 0:=by unfold fragrance entry; rw [ht]; dsimp only; rw [hk]; split_ifs; exact (varnish ..).symm; simp
   refine ⟨_,inferInstance,m, H.cross hB,fun x U=> ?_,fun i U=> ?_⟩
   · have hh (j:VividId K): (N j).M.crest=j.1:=by
        have hz := (hK _ (fun H=> (show Vivid K j.1 j.2.1.val from j.2.1.property).elim (fun U hU=> hU (by rw [H];rfl))))
        unfold Leaf.crest; rw [hp]; exact hz.1
     unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl, Sum.elim_inr, hh, hy, hx',ite_self, Finset.sum_const_zero,add_zero]; rw [Fintype.sum_sigma,sum_eq_single x]
     · simpa only [↓reduceIte] using hn x U
     · intro j _ hj; simp only [hj,↓reduceIte,sum_const_zero]
     simp
   unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl,Sum.elim_inr,hz,Finset.sum_const_zero,zero_add,hs]; rw [Fintype.sum_sigma,sum_eq_single i]
   · simpa only [↓reduceIte] using hm i U
   · intro j _ hj; simp only [hj,↓reduceIte,sum_const_zero]
   simp
end dock
end YM.MergeProof.Menu.GapsLocal
