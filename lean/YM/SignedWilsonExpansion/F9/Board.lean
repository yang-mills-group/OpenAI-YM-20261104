import YM.SignedWilsonExpansion.F9.Beam
import YM.WilsonCoeffUV.Product.I.Decay
/-!
# Locally recover the charged point projection

Probe once in each available rank. Although positive clock copies occur here,
their amplitude and also the receiver's power crop are still in the path of
`verseI` not at a lower cutoff. This estimate is coefficientwise and uniform
in the active top; scale changes are NOT implemented by truncating first.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m N u e i j l r q:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {a x b c B M X:ℝ}{U:Type*}{E W:Credit}{R:Realm G (q+1) E}

-- basic size arithmetic
lemma row_plus (F:Frame G h)(u:ℕ){Y Z:ChamberTen G ℝ r}(v:Fruit 0 1 u Y a)(w:Fruit 0 1 u Z b)(g:h*h≤u)(j:TagIx F r): row F (Y+Z) j=row F Y j+row F Z j:=by have hh:=row_sub F (Y+Z) Z (v.plus w zero_le_one) w g j; rw [add_sub_cancel_right] at hh; exact eq_add_of_sub_eq hh.symm
lemma row_scaled_sum (S:Finset U)(F:Frame G h)(X:U→ Ten ℝ (YForest G) r)(j:TagIx F r)(f:U→ℝ)(v:∀ i∈S,∃ a,Fruit 0 1 u (X i) a)(e:h*h≤u):
    row F (∑ i∈ S,f i • X i) j= ∑ i∈S,f i* row F (X i) j:=by
    induction S using Finset.induction_on with
    | empty=> simp [row_nil]
    | @insert i S h ih=>
        have p:= fun i (hi:i∈S)=>v i (Finset.mem_insert_of_mem hi); choose c hC using p
        -- choose a total function
        let P i:= if h:i∈S then c i h else 0
        obtain ⟨A,hA⟩:= v i (Finset.mem_insert_self ..); have hh: Fruit 0 1 u (∑ i∈S,f i • X i) (∑ i∈S,|f i| * P i):= Fruit.sum (fun j hj=>by rw [show P j=c j hj from dif_pos hj]; exact (hC j hj).μ _) zero_le_one
        rw [Finset.sum_insert h,Finset.sum_insert h,row_plus F u (hA.μ _) hh e,row_μ,ih (fun i hi=>⟨_,hC i hi⟩)]; rfl

lemma axPlus {x₁ x₂:Era G ℝ}(hx:Auth k x₁)(z: Auth k x₂) (i:TagIx F r): row F ((x₁+x₂).2 e r) i=row F (x₁.2 e r) i+row F (x₂.2 e r) i:=by obtain ⟨c,C⟩:= attends hx e r (h*h); obtain ⟨d,D⟩:= attends z e r (h*h); exact row_plus F (h*h) C D le_rfl i
lemma axSub {x₁ x₂:Era G ℝ}(hx:Auth k x₁)(z: Auth k x₂) (i:TagIx F r): row F ((x₁-x₂).2 e r) i=row F (x₁.2 e r) i-row F (x₂.2 e r) i:=by obtain ⟨c,C⟩:= attends hx e r (h*h); obtain ⟨d,D⟩:= attends z e r (h*h); exact row_sub F (x₁.2 _ _) (x₂.2 _ _) C D le_rfl i
lemma row_summed (S:Finset U)(X:U→Era G ℝ)(hX:∀ i∈S,Auth k (X i))(i:TagIx F r)(f:U→ℝ):
    row F ((∑ i∈S,f i • X i).2 e r) i=∑ j∈S,f j * row F ((X j).2 e r) i:= by simp only [Prod.snd_sum,Prod.smul_snd,Finset.sum_apply, Pi.smul_apply]; exact row_scaled_sum _ F _ _ f (fun i hi=> attends (hX i hi) e r (h*h)) le_rfl

/-- Probe at corresponding slot index on F's own section, NO engineering yet. -/
abbrev markP (T:SectionData F)(i:TagIx F r): Era G ℝ:= Probe T (h+1) (Nat.lt_succ_self _) i.val
lemma marks (T:SectionData F)(v:T.Sound H)(p:Bid.pop T)(i:TagIx F r): Auth r (markP T i):=by
   have hv:= probed H T (h+1) (Nat.lt_succ_self _) i v p; rw [i.property] at hv; exact hv
lemma fitsRank (T:Frame G h)(i:TagIx T r): r≤h:= by have hv:= value_le T i; rw [i.property] at hv; exact hv
-- The output-price of a single column even at the same order uses in-step inverse powers.
lemma funded (T:SectionData F)(v:T.Sound H)(p:Bid.pop T)(u r k q:ℕ)(Rk:h≤k)(E W:Credit) : ∃ B: Credit, ∀ R: Realm G (q+1) E,Dormitory R k u W→ ∀ (m N:ℕ), R.anchor ≤ m→ m<N→∀ i: TagIx F r,
    Fruit 0 1 u ((markP T i).2 0 r) (R.cash B m) ∧ Fruit 0 1 u ((ClockPage R m h k N (markP T i)).2 0 r) (R.cash B m):=by
    choose a ha using fun i:TagIx F r=>attends (marks T v p i) 0 r u; let A:=pur (∑ i,a i); have hv i:0≤ a i:= (ha i).C
    refine ⟨A.plus ((E.powC h).prodC A),fun R w m N hp q i=>?_⟩; let L:=R.mint m hp
    have hx:= R.depth m hp; have he: a i≤ R.cash A m:= (Finset.single_le_sum (fun i _=>hv i) (Finset.mem_univ i)).trans (pure_goal _ _)
    have hM:= marks T v p i; let V:= markP T i; let C:=ClockPage R m h k N V; let Qm:= (R.draws.S.block m).val; let D:= (Qm:ℝ)^h
    refine ⟨(ha i).more (he.trans (Credit.thickens _ hx)),?_⟩
    have hp':r≤ k:= (fitsRank F i).trans Rk; have hz:0≤thinLevel R.draws m 1:=by unfold thinLevel; positivity
    have hd:= (ha i).shave hz (div_le_self zero_le_one (by exact_mod_cast (R.draws.S.block m).pos))
    have hw (i j:ℕ)(v:lowerGrade i j 0 r): Fruit 0 (thinLevel R.draws m 1) u (V.2 i j) 0:=by rw [hM.coverN i j (by unfold lowerGrade at v; omega)]; exact Fruit.zero
    have ht:= amen R w hp q (Nat.zero_le _) (hp'.trans (Nat.le_add_right ..)) _ (hM.tall hp') zero_le_one le_rfl hd le_rfl hw
    rw [mul_zero,add_zero] at ht; apply (ht.μ D).more
    have hg:0≤D:=by unfold D Qm; positivity
    have ht : D≤ R.cash (E.powC h) m:= by unfold cash; rw [Credit.power]; exact pow_le_pow_left₀ (by positivity) (R.taxes m hp).height _
    have hz : lowRep R.draws.S m r≤ 1:=by unfold lowRep; split; exact le_rfl; exact rollFrac_le ..
    rw [abs_of_nonneg hg]; refine le_trans ((mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (hv i) hz).trans he) hg).trans (mul_le_mul_of_nonneg_right ht (cash_nn R A hp))) ?_; unfold cash; rw [←Credit.products]; exact Credit.thickened _ hx

abbrev wT (F:Frame G h)(i:TagIx F r):ℕ:= (F.grades i.val).1
/-- form T independently of all proof of inversibility -/
def stepT (T:SectionData F)(A:Levels G)(Ñ:ChartRatio G)(m k N r:ℕ): Matrix (TagIx F r) (TagIx F r) ℝ:= Matrix.of (fun i j=> row F ((pointStep A Ñ m N h k (markP T j)).2 0 r) i)
lemma step_top (T:SectionData F)(v:T.Sound H)(p:Bid.pop T)(L:Cloister G h){u:ℕ}(hu:Ample h u r)(hi:R.anchor≤m)(g:m<N)(t:relight R.draws R.paid m (R.mint m hi) L)(Q:h≤k)(i j:TagIx F r)(w:wT F i≤wT F j):
    stepT T R.draws R.paid m k N r i j= if i=j then ((R.draws.S.block m).val:ℝ)^(h-wT F i) else (0:ℝ):=by
    have hr:r≤k:= (fitsRank F i).trans Q; have hv:= marks T v p j
    have hx:=purchased_front hu H F hi g t (markP T j) (hv.tall hr) (fun i v=> hv.coverN 0 i v) hr (wT F j) (F.bound _) (fun x hx=> (direct H T _ (Nat.lt_succ_self _) v p j x).trans (if_neg (by intro e; rw [←e] at hx; exact lt_irrefl _ hx))) i w
    refine hx.trans ?_; rw [show row F ((markP T j).2 0 r) i= _ from direct H T _ _ v p j i]; by_cases e:i=j
    · subst j; rw [if_pos rfl,mul_one,if_pos rfl]
    rw [if_neg (Ne.symm e),if_neg e,mul_zero]
lemma needle_dark (Q:SectionData F)(v:Q.Sound H)(p:Bid.pop Q)(T:TagIx F r)(e:ℕ):
    ∀ i j, lowerGrade i j e r→(trim (PowerSeries.X^e) (markP Q T)).2 i j=0:=by intro i j u; rcases u with v'|⟨g,h⟩; rw [(thin e).zero v']; rfl; subst i; rw [(thin e).lance]; exact (marks Q v p T).coverN 0 j h

abbrev convoy (Q:SectionData F)(e:ℕ)(x:TagIx F r→ℝ): Era G ℝ:= ∑ i, x i • trim (PowerSeries.X^e) (markP Q i)
lemma convoy_pur (Q:SectionData F)(v:Q.Sound H)(p:Bid.pop Q)(e:ℕ)(x:TagIx F r→ℝ)(h:h≤k): Auth k (convoy Q e x):= Auth.sum (fun i _=>((trim_auth _ ((marks Q v p i).tall ((fitsRank F i).trans h))).μ (x i)))
lemma convoy_face (Q:SectionData F)(e:ℕ)(x:TagIx F r→ℝ): (convoy Q e x).2 e=∑ i, x i • (markP Q i).2 0:=by simp only [convoy,Prod.snd_sum, Prod.smul_snd, Finset.sum_apply,Pi.smul_apply]; exact Finset.sum_congr rfl (fun i _=> congr_arg _ ((thin e).lance _))
lemma send (g:G.Simple)(v:m<N)(p:LocalRatio Ñ)(Q:SectionData F)(w:Q.Sound H)(z:Bid.pop Q)(x:TagIx F r→ℝ)(hk:h≤k):
    (pointStep A Ñ m N h k (convoy Q e x)).2 e= (∑ i, x i • (pointStep A Ñ m N h k (markP Q i)).2 0):=by simp only [convoy]; rw [step_sum g v p _ _ (fun i _=> trim_auth _ ((marks Q w z i).tall ((fitsRank F i).trans hk)))]; simp only [Prod.snd_sum,Prod.smul_snd,Finset.sum_apply,Pi.smul_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [next_composed g v p _ _ ((marks Q w z i).tall ((fitsRank F i).trans hk)), ((thin e).spike g v p).lance _]
lemma convoy_read (Q:SectionData F)(v:Q.Sound H)(p:Bid.pop Q)(x:TagIx F r→ℝ)(i:TagIx F r): row F ((convoy Q e x).2 e r) i=x i:=by
    rw [row_summed _ _ (fun j _=>trim_auth _ (marks Q v p j))]; simp_rw [(thin e).lance]; unfold markP; simp_rw [direct H Q _ _ v p]; apply Eq.trans (Finset.sum_eq_single i _ (by simp)); swap; · intro j _ h; rw [if_neg h,mul_zero]
    rw [if_pos rfl,mul_one]
lemma convoy_after (g:G.Simple)(v:m<N)(p:LocalRatio Ñ)(Q:SectionData F)(w:Q.Sound H)(z:Bid.pop Q)(x:TagIx F r→ℝ)(hk:h≤k) (i:TagIx F r):
    row F ((pointStep A Ñ m N h k (convoy Q e x)).2 e r) i=(stepT Q A Ñ m k N r *ᵥ x) i:=by
    rw [send g v p Q w z x hk, Finset.sum_apply]; simp only [Pi.smul_apply]; let V i:=pointStep A Ñ m N h k (markP Q (i:TagIx F r)); rw [row_scaled_sum _ _ _ _ x (u:=h*h) (fun i _=> attends (Y:=V i) (nextStep g v p ((marks Q w z i).tall ((fitsRank F i).trans hk))) 0 r (h*h)) le_rfl]; exact Finset.sum_congr rfl (fun i _=> mul_comm ..)

private lemma baseline_bag (S:Finset U)(X:U→ℝ)(F:U→ChamberTen G ℝ r)(f:∀ i∈S,Fruit 0 1 u (F i) a)(p:0≤a)(x:∀ i:U,|X i|≤ c): Fruit 0 1 u (∑ i∈S,X i • F i) ((S.card:ℝ)*a*c):=by
    apply (Fruit.sum (S:=S) (fun i hi=> (f i hi).μ (X i)) zero_le_one).more
    rw [mul_assoc,← nsmul_eq_mul,← Finset.sum_const]; refine Finset.sum_le_sum fun i _=> (by rw [mul_comm _ c];exact mul_le_mul_of_nonneg_right (x i) p)
lemma poll (Q:SectionData F)(g:G.Simple)(v:m<N)(p:LocalRatio Ñ)(w:Q.Sound H)(z:Bid.pop Q){a0 a1:ℝ}(he:0≤a0)(hx:0≤a1)(f:∀i:TagIx F r,Fruit 0 1 u ((markP Q i).2 0 r) a0)
    (f':∀i:TagIx F r,Fruit 0 1 u ((pointStep A Ñ m N h k (markP Q i)).2 0 r) a1)(hk:h≤k)(e:ℕ) (x:TagIx F r→ℝ)(T:ℝ)(paid:∀ i,|x i|≤ T):
    Fruit 0 1 u ((convoy Q e x).2 e r) ((Fintype.card (TagIx F r):ℝ)*a0*T) ∧
    Fruit 0 1 u ((pointStep A Ñ m N h k (convoy Q e x)).2 e r) ((Fintype.card (TagIx F r):ℝ)*a1*T):=by
    rw [send g v p Q w z x hk,convoy_face,Finset.sum_apply,Finset.sum_apply]; simp only [Pi.smul_apply]; exact ⟨baseline_bag _ _ _ (fun i _=>f i) he paid,baseline_bag _ _ _ (fun i _=>f' i) hx paid⟩

/-- Point version of (31), two-sided charge on whole taps. At each height
 a owns all earlier rank/order and c owns row values (they can move
 without bounds on rank-r kernel; do not multiply the step contract by the
 latter!). This is only about *formal* vertical maps on this path. -/
structure Report (A:Levels G)(Ñ:ChartRatio G)(Q:SectionData F)(m N k e u r:ℕ)(b:ℝ): Prop where
   nn: 0≤b
   top : ∀ i j, wT F i ≤ wT F j → stepT Q A Ñ m k N r i j= if i=j then ((A.S.block m).val:ℝ)^(h-wT F i) else 0
   fare (i j:TagIx F r): ‖stepT Q A Ñ m k N r i j‖≤ b
   back (P: Era G ℝ)(a x:ℝ)(p:Auth k P)(hp:0≤a)(u':Earlier P e r u a)(hx:Fruit 0 1 u (P.2 e r) x):
       let t:=pointStep A Ñ m N h k P; let f:=row F (P.2 e r); let w:=stepT Q A Ñ m k N r
       (∀ i, ‖row F (t.2 e r) i-(w *ᵥ f) i‖ ≤ b*a) ∧
       ∀ c:ℝ,0≤c→(∀ i, ‖f i‖≤ c)→ Fruit 0 1 u (t.2 e r) (rollFrac A m*x+b*(a+c))
lemma Report.raise {b c:ℝ}{Q:SectionData F}(p:Report A Ñ Q m N k e u r b)(v:b≤c): Report A Ñ Q m N k e u r c:=by
    refine ⟨p.nn.trans v,p.top,fun i j=>(p.fare i j).trans v,?_⟩; intro P a x t hp u' hx r f w
    obtain ⟨p1,p2⟩:= p.back P a x t hp u' hx; refine ⟨fun i=> (p1 i).trans (mul_le_mul_of_nonneg_right v hp),fun c' h t=> (p2 c' h t).more (add_le_add_right (mul_le_mul_of_nonneg_right v (add_nonneg hp h)) _)⟩
lemma assembly (Q:SectionData F)(hq:Q.Sound H)(pw:Bid.pop Q)(S:Ample h u r)(Qp:h≤k)(e q:ℕ)(E W W':Credit)(ep:e≤q):
    ∃ D:Credit,∀ R:Realm G (q+1) E,Dormitory R k u W→ ∀ m N:ℕ,∀ L:Cloister G h,∀ v:R.anchor≤ m,∀ _ :m<N,relight R.draws R.paid m (R.mint m v) L → Bill H F S L k e (R.cash W' m) → Report R.draws R.paid Q m N k e u r (R.cash D m):=by
    obtain ⟨B,X⟩:= funded Q hq pw u r k q Qp E W; let C:=annuity G h k e r q u F E W'; let D:ℝ:=Fintype.card (TagIx F r); let A:= (C.plus ((pur (rowCost F u r)).prodC B)).plus ((pur (2*D)).prodC B)
    refine ⟨A,fun R w m N L v u' x T=>?_⟩; let V:=R.cash B m; let I:= R.cash A m; let Y:=R.cash C m; have hb:0≤V:=cash_nn R B v; have he:0≤I:=cash_nn R A v; have hp:= R.depth m v
    have hw:E.buy (R.y m) ≤ R.cash E m:=le_rfl
    have Ω: Y+(rowCost F u r)*V+2*D*V ≤ I:= by
       have hm (c:ℝ): c*V≤ R.cash ((pur c).prodC B) m:= by unfold cash; rw [Credit.products]; exact mul_le_mul_of_nonneg_right (pure_goal c _) hb
       exact (add_le_add ((add_le_add_right (hm _) _).trans (Credit.fuel _ _ hp)) (hm _)).trans (Credit.fuel _ _ hp)
    let f:=stepT Q R.draws R.paid m k N r; let t:= pointStep R.draws R.paid m N h k
    have hx:0≤rowCost F u r * V:=mul_nonneg (rowCost_nn F) hb; have hh:0≤Y:=cash_nn R C v; have hD:0≤D:=by unfold D; positivity
    have hv:=X R w m N v u'
    refine ⟨he, step_top Q hq pw L S v u' x Qp,fun i j=> le_trans (row_bound F _ (hv j).2 S.floor i) (( (le_add_of_nonneg_left hh).trans (le_add_of_nonneg_right ?_)).trans Ω),?_⟩
    · positivity
    intro P a z z' ha H' hB F' τ h; let c:= convoy Q e τ; have tc:Auth k c:= convoy_pur Q hq pw _ _ Qp; let Y':=P-c
    have ψ : Earlier Y' e r u a:= by
       intro i j e'; have he : c.2 i j=0:=by unfold c convoy; simp only [Prod.snd_sum, Finset.sum_apply,Prod.smul_snd,Pi.smul_apply,needle_dark Q hq pw _ e _ _ e',smul_zero,Finset.sum_const_zero]
       change Fruit 0 1 u (P.2 i j-c.2 i j) a; rw [he,sub_zero]; exact H' i j e'
    have z0(i:TagIx F r): row F (Y'.2 e r) i=0:=by rw [axSub (F:=F) z' tc]; unfold c; rw [convoy_read Q hq pw]; exact sub_self _
    have hy : t Y'=t P-t c:=step_sub R.hG u' R.green _ _ z' tc
    have hI : Y ≤ I:=le_trans (le_trans (le_add_of_nonneg_right hx) (le_add_of_nonneg_right (by positivity))) Ω
    have HRI:2*D*V ≤ I:= le_trans (le_add_of_nonneg_left (by positivity)) Ω
    constructor
    · intro i; obtain ⟨g,Z⟩:= attends (Auth.sub z' tc) e r u
      have he:= (funds_zero S H F v ep u' x T Y' (Auth.sub z' tc) a g ha ψ Z z0).2 i
      change ‖row F ((t Y').2 e r) i‖≤ Y*a at he; rw [hy,axSub (nextStep R.hG u' R.green z') (nextStep R.hG u' R.green tc)] at he; rw [show row F ((t c).2 e r) i=(h*ᵥ τ) i from convoy_after R.hG u' R.green Q hq pw τ Qp i] at he; exact he.trans (mul_le_mul_of_nonneg_right hI ha)
    intro g e' Z; let V':=D*V*g; have hg':0≤ V':= by unfold V'; positivity
    obtain ⟨h1,h2⟩:= poll Q R.hG u' R.green hq pw hb hb (fun i=>(hv i).1) (fun i=>(hv i).2) Qp e τ g Z
    have ht:=funds_zero S H F v ep u' x T Y' (Auth.sub z' tc) a (z+V') ha ψ (hB.diff h1 zero_le_one) z0; have hC:(t P).2 e r=(t Y').2 e r+(t c).2 e r:=by rw [hy]; exact (sub_add_cancel ..).symm
    change Fruit 0 1 u ((t P).2 e r) (rollFrac R.draws m*z+I*(a+g)); rw [hC]; apply (ht.1.plus h2 zero_le_one).more
    calc
       _ = rollFrac R.draws m*z+ (Y*a +( rollFrac R.draws m*V'+V')):= by change rollFrac _ _ * (z+V')+Y*a+V'=_; ring
       _ ≤ rollFrac R.draws m*z+(I*a+I*g):=add_le_add_right (add_le_add (mul_le_mul_of_nonneg_right hI ha) ((add_le_add_left (mul_le_of_le_one_left hg' (rollFrac_le ..)) V').trans (le_trans (le_of_eq (show V'+V'=2*D*V*g from by unfold V';ring)) (mul_le_mul_of_nonneg_right HRI e')))) _
       _ = _:=by ring
end YM.WilsonCoeffUV.Mer.Xa
