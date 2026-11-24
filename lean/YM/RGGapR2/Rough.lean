import YM.RGGapR2.Harbor
import YM.MergeProof.Biscuit
/-! Rough corridor on full actual density, adapted from `Menu.alarm/drydock` and
  `Duty` clock/purchase. Keep K (all nonconstant modes) WITH the original bar and H as
  a connected log in the standard formula. This interface deliberately doesn’t
  assume that the marked-density ratios are pointwise small at dirty flags.
  No singleton split required to pay this transfer; no restarted StepData kernels.
  The close-step losses may recur (and thus must be charged over a compatible
  **short** window unless new estimates are made).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGGapR2.Rough
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Marker
open MergeProof MergeProof.Menu MergeProof.Accent Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
set_option quotPrecheck false
set_option maxHeartbeats 1300000

section
variable {v:V→ℝ}{d h' e b c':ℝ}{o: V→Site f} [Fintype ι] {X:ι→Support f}{F:ι→ Config G f→Poly B}
lemma alarmPlus (hv:∀ i,0<v i) {g:ι→Wing}
    (h:∀ i,F i≠0→ (g i).support R=X i ∧ (g i).blank R)(ht:∀ i U,F i U≠0→ (g i).qualifies R U)
    (hp:∀ i,Borne o (X i) (F i) R.p.threshold)(hx:∀ i U,(F i U).part B.quiet=0)(he:Towed v X F R.p.B d b):∃ (P:VividId F→ Hat B R),
    (∀ i,WKey (P i)=g i.fst ∧ (P i).s=i.2.1.val) ∧ Offer o P v R.p.B d (2*b) ∧ ∀ i U,∑ j:{i':B.Mode // Vivid F i i'} × Bool, amount (P ⟨i,j⟩) U= F i U :=by
   let A(i):= {p:B.Mode// Vivid F i p}; have hh(i) (x:A i): F i≠0:=by obtain ⟨y,hy⟩:=x.property;exact fun ht=> hy (by rw [ht];rfl)
   obtain ⟨w,hw,hW,hB⟩:=he
   choose f hf hs hP using hB
   have hI(i)(x:A i): 1 ≤ x.val.val.card:=by
      refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_);intro h
      obtain ⟨U,hh⟩:=x.property
      exact hh ((congr_arg ((F i U).part) (show x.val=B.quiet from Subtype.ext h)).trans (hx i U))
   obtain ⟨P,HP,HQ,Hh⟩ : ∃ (u : ∀ i,A i→ Bool→Hat B R), (∀ i p j,WKey (u i p j)=g i ∧ (u i p j).s=p.val) ∧ (∀ i p,∑ l,fare (u i p l) v = 2*(Poly.toll v p.val*f i p.val))∧∀ i p U,∑ l,amount (u i p l) U=Poly.send p.val ((F i U).part p.val):=by
      have he i (p:A i): UsesFinal R.p.threshold ((g i).support R) (fun U=> (F i U).part p.val):= (h i (hh i p)).1.symm ▸ (fun U V hx ht=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).home U V hx ht))
      choose u hu hU hT using fun i p=> Menu.couple (R:=R) (g i) (s:=(p:A i).val) (fun U=> (F i U).part p.val) v (he i p) (fun U hv=> ht i U (fun h=> hv (by rw [h];rfl))) (h i (hh i p)|>.2) (hp i|>.me _) (fun t U=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).turns t U)) (fun U=> hs i U _) (Finset.card_pos.mp (show 0 < p.val.val.card from hI i p))
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
end

structure Ledger (o:V→Site f)(K:Support f→ Config G f→Poly B)(F:Box f→ Config G f→Poly B)(t:ℝ) : Prop where
    exp(i:Support f): Burns o i (K i) t
    flag(i:Box f): Flow o i (F i) t ∧ ∀ U:Config G f,(F i U).part B.quiet=0

variable [Fintype V]
def Freight (A:Rep G f)(B:Census V)(X : Config G f→Poly B) (o:V→Site f)(w:V→ℝ)(e c:ℝ) := ∃ H K, Ledger o H K A.p.threshold ∧ Towed w id H A.p.B e c ∧ Towed w Prod.fst K A.p.B e c ∧ X=play A B (exclaim A.activities B+K) (fun U=>∑ i,H i U)

variable {t d p e a c':ℝ} {o: V→Site f}{w:V→ℝ}
variable {T:BudgetPoint} {K:Support f→ Config G f→Poly B} {F:Box f→ Config G f→Poly B}
omit [Fintype V] in
lemma dockPlus (h : Ledger o K F R.p.threshold)(he:Towed w id K R.p.B d a)(hq:Towed w (fun i:Box f=>i.1) F R.p.B d a)(hw:∀ i,0<w i)(hx:Arsenal R):
   ∃ (I:Type) (_:Fintype I)(q:I→Hat B R), Offer o q w R.p.B d (4*a) ∧ (∀ U,(∑ i,odour (q i) U)=∑ i,K i U)∧∀ i U,∑ j,fragrance (q j) U i=F i U:=by
   have hb(i): K i≠0→i.Nonempty:=by
      intro H; obtain ⟨U,hU⟩:= Function.ne_iff.mp H; obtain ⟨p,hp⟩:= Function.ne_iff.mp (show Poly.part (K i U) ≠ Poly.part 0 from (by intro g; exact hU g)); let y:= h.exp i; have ht: 1 ≤ p.val.card:= (by
         apply Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
         intro he; exact hp ((congr_arg ((K i U).part) (Subtype.ext he : p=B.quiet)).trans (y.sil _))); exact ((Finset.card_pos.mp (by omega : 0 < p.val.card)).image o).mono (y.toBorne.place _ _ hp)
   let k(i:Support f) := if H:K i≠0 then (hx.dry i (hb i H)).choose else 0
   let g i:= Wing.logKey (k i); have hK (i)(he:K i≠0): (R.activities.reg (k i)).support=i ∧ R.activities.E (k i)=0:=by unfold k; rw [dif_pos he]; exact (hx.dry i (hb i he)).choose_spec
   have hv(i U)(he:K i U≠0): (g i).qualifies R U:=by change Healthy _ _ U; rw [(hK i (fun hh=> he (congr_fun hh U))).1]; exact ((h.exp i).permits U he)
   obtain ⟨N,hN,H,hn⟩:= alarmPlus (v:=w) hw (F:=K) (X:=id) (g:=g) (fun i hp=> hK i hp) hv (fun i=>(h.exp i).toBorne) (fun i=>(h.exp i).sil) he
   have hd(i): F i≠0 → Sure i:=by intro hh; obtain ⟨U,hU⟩:= Function.ne_iff.mp hh; exact ((h.flag i).1.permits U hU).2
   let L(i: Box f):= if H:F i≠0 then (hx.wet i (hd i H)).choose else 0
   let l i:= Wing.gasKey (L i); have hF(i)(h:F i≠0): barcode R.activities (L i)=i ∧ ∀ U,i.1∩RG.flags R.p.threshold U=i.2 → (R.activities.forced (L i)).eligible R.p.threshold U:=by unfold L; rw [dif_pos h]; exact (hx.wet i (hd i h)).choose_spec
   have ht (i U)(he:F i U≠0): (l i).qualifies R U:=(hF i (fun hh=> he (congr_fun hh U))).2 U (((h.flag i).1.permits U he).1)
   obtain ⟨M,hM,hB,hm⟩:= alarmPlus (v:=w) hw (F:=F) (X:=Prod.fst) (g:=l) (fun i hp=> ⟨(Prod.mk.inj (hF i hp).1).1,trivial⟩) ht (fun i=>(h.flag i).1.toBorne) (fun i=>(h.flag i).2) hq
   let m:= Sum.elim N M
   have hp(x): (N x).M.turn= .logKey (k x.1):= (hN x).1; have ht(x): (M x).M.turn=.gasKey (L x.1):=(hM x).1
   have hk(i:VividId F):barcode R.activities (L i.1)=i.1:=(hF _ (fun H=> (show Vivid F i.1 i.2.1.val from i.2.1.property).elim (fun U hU=> hU (by rw [H]; rfl)))).1
   have hy(U x):odour (N x) U=amount (N x) U:=by unfold odour prose; rw [hp,varnish]
   have hx'(U x):odour (M x) U=0:=by unfold odour prose;simp [ht]
   have hz (U x i):fragrance (N x) U i=0:=by unfold fragrance entry; simp [hp]
   have hs(U x i):fragrance (M x) U i=if x.1=i then amount (M x) U else 0:=by unfold fragrance entry; rw [ht]; dsimp only; rw [hk]; split_ifs; exact (varnish ..).symm; simp
   refine ⟨_,inferInstance,m,by rw [show 4*a= _ from (show 4*a=2*a+2*a by ring)]; exact H.cross hB,fun U=> ?_,fun i U=> ?_⟩
   · unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl, Sum.elim_inr, hy,hx', Finset.sum_const_zero,add_zero]; rw [Fintype.sum_sigma]; exact sum_congr rfl fun i _=> hn i U
   unfold m; rw [Fintype.sum_sum_type]; simp_rw [Sum.elim_inl,Sum.elim_inr,hz,Finset.sum_const_zero,zero_add,hs]; rw [Fintype.sum_sigma,sum_eq_single i]
   · simpa only [↓reduceIte] using hm i U
   · intro j _ hj; simp only [hj,↓reduceIte,sum_const_zero]
   simp
section
variable {I : Type} {Z₀:I→Support f} {U:I→ Config G f→Poly B} {w':V→ℝ}
omit [Fintype V] in
lemma reduced (h₀:0≤t)(h₁:t≤1)(hU:∀ i V, (U i V).part B.quiet=0)(hw:∀ i,0<w i)(hw':∀ i,0<w' i)(he:∀ i, w' i ≤ t*w i) (hz:Towed w Z₀ U R.p.B e a) : Towed w' Z₀ U R.p.B e (t*a):=by
   obtain ⟨Q,hS,hY,hB⟩:=hz
   refine ⟨(fun i=>t*Q i),(hS.mul_left t),fun i=> ?_,fun i=>?_⟩
   · convert! Extra.Multi.Budget.scale (hY i) h₀ using 1; ext j; dsimp only; split_ifs; ring;rw[mul_zero]
   obtain ⟨v,hv,h,hz⟩:= hB i; let u (b:B.Mode):= if b=B.quiet then 0 else v b; have hu(b):0 ≤ u b:=by unfold u;split;exact le_rfl; exact hv _
   refine ⟨u,fun b=>hu b,fun y b=>?_, le_trans ?_ (mul_le_mul_of_nonneg_left hz h₀)⟩
   · unfold u; split; rename_i hb; rw [hb,hU,norm_zero]; exact h ..
   unfold wordsPrice;rw [Finset.mul_sum]; refine Finset.sum_le_sum fun b _=> ?_; unfold u; split; next h=> rw [mul_zero];exact mul_nonneg h₀ (mul_nonneg (Poly.worth hw _).le (hv _))
   next h=>
     have he': Finset.Nonempty b.val:=Finset.nonempty_iff_ne_empty.mpr (fun h'=>h (Subtype.ext h'))
     have hf:t^b.val.card ≤ t:=by simpa only [pow_one] using pow_le_pow_of_le_one h₀ h₁ (Finset.card_pos.mpr he')
     have hh : Poly.toll w' b ≤ t* Poly.toll w b:=by
       unfold Poly.toll; apply (Finset.prod_le_prod (fun i _=>(hw' i).le) (fun i _=>he i)).trans; rw[Finset.prod_mul_distrib,Finset.prod_const]; exact mul_le_mul_of_nonneg_right hf (prod_nonneg fun i _=>(hw _).le)
     rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hh (hv _)  

lemma Freight.offer {F:Config G f→Poly B}{σ C v u ξ:ℝ} (hx:0 ≤ d) (hw:∀ i,0<w i) (A:Arsenal R)(hp:R.Lawful σ C v u ξ)(S:StepData c f)(h:Freight R B F o w d a) : (∃ (I:Type) (_:Fintype I)(q:I→Hat B R), Offer o q w R.p.B d (4*a+Real.exp (4*a)*(4*a)) ∧ F=Expense q w S):=by
   obtain ⟨U,K,h,hU,hK,he⟩:=h
   obtain ⟨I,it,q,H,h,hL⟩:= dockPlus h hU hK hw A
   refine ⟨Mound q,inferInstance,heap q, counts q w o R.p.B hw H hx,?_⟩; funext z; rw [he,Expense,passIn (heap q) S hp hw z, Menu.golden, banded, perfumes,h]; simp_rw [patron,hL]; rfl -- hL depends i
end

def purge (B:Census V)(p:Poly B): Poly B:=Poly.inject (fun i=> if i=B.quiet then 0 else p.part i)
lemma Flow.purge {b:Box f}{F:Config G f→Poly B}(h:Flow o b F t):Flow o b (fun U=>Rough.purge B (F U)) t:=by
  refine ⟨⟨fun U V' hy hV'=>congr_arg (Rough.purge B) (h.home _ _ hy hV'),fun m U=>congr_arg _ (h.turns m U),fun i=>?_,fun V i hi=>?_⟩,fun U hU=>h.permits U (fun hf=> hU ?_)⟩
  · change Measurable (fun u=>if i=B.quiet then 0 else (F u).part i); by_cases hq:i=B.quiet; simpa only [if_pos hq] using (show Measurable (fun _:(Config G f)=> (0:ℂ)) from measurable_const); simpa only [if_neg hq] using h.me i
  · change (if _ then _ else _)=_; split; rfl; exact h.scope V _ hi
  rw [hf]; ext i; change (if i=B.quiet then (0:ℂ) else (0:ℂ))=0; split <;> rfl
lemma Towed.purge {I : Type} {Z₀:I→Support f} {U:I→ Config G f→Poly B} (h:Towed w Z₀ U R.p.B d a) :
   Towed w Z₀ (fun i u=> Rough.purge B (U i u)) R.p.B d a:=by
    obtain ⟨Q,hS,hY,hB⟩:=h; refine ⟨Q,hS,hY,fun i=>?_⟩; obtain ⟨v,hv,ht,hx⟩:= hB i
    refine ⟨v,hv,fun u y=>?_,hx⟩; change ‖(if y=B.quiet then (0:ℂ) else _)‖ ≤ _;  split; rw [norm_zero]; exact hv ..; exact ht ..

section
variable {I : Type} [Fintype I] {S:StepData c f}{F0:Rep G c}{G0:GaugeDoor R F0}{q:I→Hat B R}{d y s v δ u:ℝ}{w:V→ℝ}{o:V→Site c}
lemma Canopy.freight (h:Canopy S G0 o w (d+1/2) (d+1) 1 u q)(ht:F0.activities.Valid F0.p s v)(hw:∀ i,0 < w i)(hu:u ≤ 1): Freight F0 B (S.push R.beta (Expense q w S)) o w d 1:=by
   obtain ⟨F,K,hF,hE,hB,hK,hY,hP,hL⟩:= h.buyer
   have hp : exclaim F0.activities B+ (fun i U=> Rough.purge B (K i U))=K:=by
      funext i z; ext b; change (Poly.send B.quiet _).part b + (if b=B.quiet then _ else _)= _; rw [Poly.part_send]; split_ifs with h; rw [add_zero]; apply Eq.symm; exact h.symm ▸ hP i _
      exact zero_add _
   refine ⟨F,(fun i U=> Rough.purge B (K i U)),⟨hE,fun i=>⟨Rough.Flow.purge (hK i),fun U=>(show (ite (B.quiet=B.quiet) (0:ℂ) ((K i U).part B.quiet)) = 0 from if_pos rfl)⟩⟩,hF.shrink (by linarith : d ≤ d+1/2) le_rfl hw,(Rough.Towed.purge hB).shrink (by linarith : d ≤ d+1) hu hw,?_⟩
   rw [hp]; exact hY
end

section
variable (A:History G) (r:ℕ→ℕ) (N m p:ℕ)
local notation "f0"=> A.S.side (m+1) p
local notation "c0"=> A.S.side m p
local notation "X0"=> A.rep N p m
local notation "X1"=> A.rep N p (m+1)
local notation "Z"=> A.levels.clock.op m p
local notation "P0"=> (A.levels.budget m)
local notation "P1"=> (A.levels.budget (m+1))
variable {θ:Config G (A.S.side (m+1) p)→Poly B}{D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
lemma reducedStep {d v t u:ℝ} {o:V→Site (A.S.side (m+1) p)} {I J:V→ℝ} (h:A.Selected)(hm:m < N)(hu:Duty A r m d t u)(H:Volant Z D (r m) ((P1|>.supportExponent)-4) t ((P0|>.supportExponent)+1/2) ((P0|>.supportExponent)+1) 1 u)
    (hI:∀ i,0< I i)(hJ:∀ i,0<J i)(h':Freight X1 B θ o I v 1)(hX:(P1|>.supportExponent)-4 ≤ v)
    (hO:Occupancy ((Z).ratio.parent ∘ o) (r m)) (hy:∀ i,J i ≤ d*I i): Freight X0 B ((Z).push (X1).beta θ) ((Z).ratio.parent ∘ o) J (P0|>.supportExponent) 1:=by
     obtain ⟨U,K,hL,hE,hQ,hθ⟩:=h'; let y:=(P1|>.supportExponent)-4; have he : (X1|>.p)=P1:= (h.represents _ _ _ hm).vac; have he':Rough.Ledger o U K (X1|>.p).threshold :=hL
     have hY: Freight X1 B θ o J y d:= ⟨U,K,hL,(reduced (w':=J) hu.hats.1.le hu.hats.2 (fun i=>(he'.exp i).sil) hI hJ hy hE).shrink hX (mul_one _).le hJ,(reduced (w':=J) hu.hats.1.le hu.hats.2 (fun i=>(he'.flag i).2) hI hJ hy hQ).shrink hX (mul_one _).le hJ,hθ⟩
     have h0:0≤ y:= by unfold y; linarith only [hu.exp.2]
     obtain ⟨ι,i,Q,hV,hF⟩:=Freight.offer h0 hJ H.contact ((h.represents N p _ hm).good) Z hY
     have hT:=hu.copper; have hb: 0 ≤ (r m)*siteFactor (P1|>.B)*d :=by have :=hu.hats.1; unfold siteFactor; positivity
     let Y:= (r m)*siteFactor (P1|>.B)*d+4*d
     have hl : 4*d≤Y:= le_add_of_nonneg_left hb
     have hq:= H.reserves Q hJ hO (hV.fatten (show 4*d+Real.exp (4*d)*(4*d) ≤ t from (add_le_add hl (mul_le_mul (Real.exp_monotone hl) hl (by have :=hu.hats.1; positivity) (Real.exp_pos _).le)).trans hT));rw [hF]; refine Rough.Canopy.freight (S:=Z) hq (h.represents N p m hm.le).good.labels hJ ?_
     have he:=hu.stakes.2
     let x:ℝ:= u+(r m)*siteFactor (P0|>.B)*d
     change Real.exp x - 1 ≤ 1 at he; have hx:= Real.add_one_le_exp x
     have hh : 0 ≤ (r m)*siteFactor (P0|>.B)*d :=by have :=hu.hats.1; unfold siteFactor; positivity
     change u+_+1 ≤ _ at hx; linarith only [he,hx,hh]
end
end YM.RGGapR2.Rough