import YM.WilsonCoeffUV.Stable.Return
/-!
# Cheap audited nonstable steps (not iterated); differences along parameterized family OF operators. Telescopable as closed.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m u N M:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}
lemma foreQ (β:ℝ){P Q:Single G D}(y:β≥0) (F:Frame G h)(p:h*h≤u)(v:∀ i j,i≤e→j≤h→ YieldP 0 1 u A β (P i j) (Q i j))(i:Alma F)(hv:k≤e) : twain ((coinQ F p D)*A) β (glean F P k i) (glean F Q k i):=by
    unfold glean; dsimp only
    let S:= Finset.range (valence F i+1); let Z r:=(echo_credit F p r D).choose*A; have ht:0≤A:= (v 0 0 (Nat.zero_le _) (Nat.zero_le _)).nn; have hZ j:0≤Z j:= mul_nonneg (echo_credit F p j D).choose_spec.1 ht
    let f (P:Single G D)(r:ℕ):=if valence F i≤ k+r then echoS F (P (k+r-valence F i) r) i else 0
    have he r (hr:r∈ S): twain (Z r) β (f P r) (f Q r):= by
        unfold f; have hx:= Finset.mem_range.mp hr; split; · exact echoSupport F p (P _ _) (Q _ _) (v _ _ (by omega) ((Nat.le_of_lt_succ hx).trans (valence_cap ..))) i
        exact (twain.zero _).lift (hZ _) y
    have hh:= twain.sum S he; apply hh.lift _ y; unfold coinQ; rw [Finset.sum_mul]; exact Finset.sum_le_sum_of_subset_of_nonneg (show S⊆ Finset.range _ from Finset.range_mono (Nat.add_le_add_right (valence_cap ..) 1)) (fun i _ _=>hZ i)

lemma orchardRough (e k u r h D:ℕ)(G:Gauge): ∃ d:ℕ,∀ I: Gear G,∃ C:ℝ,0≤ C∧∀ (P: Rally (e+1) 0 I)(A:ℝ)(X Y: Single G D), 0≤A → (∀ i j,i≤e→YieldP 0 1 u A P.σ (X i j) (Y i j)) → ∀ i≤e,∀ j≤ r,YieldP 0 1 u (C*P.x^d*A) P.σ (Orchard I P.P h k X i j) (Orchard I P.Q h k Y i j):=by
    obtain ⟨d,H⟩:=uniform_air e 0 u r h k D G; obtain ⟨a,V⟩:= Air.paintH (e:=e) (G:=G) (r:=0) (D:=D) (u:=u) k
    refine ⟨d+a,fun I=>?_⟩; obtain ⟨A,hA,p⟩:= H I; obtain ⟨B,b,v⟩:=V I
    let L:ℝ:= I.patch.L.val; let G:= gradeH I.patch h k; have hg:0≤G:=grade_nn ..; let T:= G*(B+L^k); let C:=T+A; have hL:0≤L:=by unfold L; positivity
    have ht:0≤ T:=by unfold T; positivity
    have hc:0≤ C:=by unfold C; positivity
    refine ⟨C,hc,fun P M X Y hm f i hi j hj=>?_⟩
    let W: SumT I e 0 D u:=⟨P,X,Y,M,1,hm,zero_le_one,le_rfl,fun i j x=> (f i j (by unfold lowerGrade at x; omega)).shrink (by positivity) (by rw [one_div]; exact speck_le _)⟩
    have hy:P.x≥1:=P.rich
    by_cases z: lowerGrade i j e 0
    · exact (p W i j z hj).step (logStep (by omega) hA (le_add_of_nonneg_left ht) hy hm) P.θ
    unfold lowerGrade at z; have hk:i=e:=by omega
    have he:j=0:=by omega
    subst i j
    have hV:= v W
    have H:YieldP 0 1 u (L^k*M) P.σ (hall I.patch k P.P.Q (X e 0)) (hall I.patch k P.Q.Q (Y e 0)):=by
        have he:=f e 0 le_rfl; rw [show hall _ k P.P.Q (X e 0)= hall _ k P.Q.Q (X e 0) from congr_arg ((tiara I.patch k) • ·) (Finset.sum_congr rfl fun i _=> funext fun x=> by simp [pulseS,pump,spinJob])]
        let X':= X e 0; let Z:=Y e 0;
        have ht {A:ℝ}{Y':Single _ D}(q:Fruit 0 1 u (Y' e 0) A): Fruit 0 1 u (hall I.patch k P.Q.Q (Y' e 0)) (L^k*A):=by
            let Y:= Y' e 0; have hg w: Fruit 0 1 u (pulseS I.patch w P.Q.Q Y) A:=by
                rw [show pulseS _ w _ _= soprano _ w D ∘ Y from ?_]; exact (q.touch _ zero_le_one).more (mul_le_of_le_one_left q.C (budgetS ..))
                ext1 x; unfold pulseS pump; rw [tsum_fintype,Fintype.sum_unique]; simp only [spinJob,Finset.prod_empty,Finset.univ_eq_empty,one_smul, featherS]; rw [Function.comp_apply,revolve,Subsingleton.elim (α:=Fin 0→_) (jog _ ∘ _) x]; rfl
            unfold L; rw [← tier_cash]; exact (Fruit.sum (S:=Finset.univ) (fun w _=> hg w) zero_le_one).μ _
        refine ⟨ht he.wax,ht he.wane,?_⟩; rw [show hall _ k _ X'- hall _ k _ Z= hall I.patch k P.Q.Q ((X-Y) e 0) from ?_,mul_assoc]; exact ht (Y':=X-Y) he.toll
        unfold hall; rw [←smul_sub (tiara I.patch k) (_:ChamberTen _ (Vote D) 0),← Finset.sum_sub_distrib]; apply congr_arg _; refine Finset.sum_congr rfl fun w _=>funext fun x=>?_ ; unfold pulseS pump; simp only [Pi.sub_apply,tsum_fintype,Fintype.sum_unique,spinJob, Finset.univ_eq_empty, Finset.prod_empty,one_smul,featherS,revolve,map_sub,Function.comp_apply];
        rfl
    unfold Orchard; simp only [Pi.smul_apply, helmet_bows]; apply ((H.plus hV zero_le_one).μ G).step _ P.θ
    let Q:= P.x^a; have hQ:1≤ Q:= one_le_pow₀ hy
    rw [abs_of_nonneg hg]; change G*(L^k*M+B*Q*M) ≤ _
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity : 0≤L^k) hQ) hm) _) hg) ?_
    rw [show G*(L^k*Q*M+B*Q*M)=T*Q*M from by unfold T; ring]
    exact logStep (by omega) ht (le_add_of_nonneg_right hA) hy hm

lemma tenderOp (X Y:Island F D){V U:Verse F}(r:ℕ)(hp:∀ j k,k≤ e→ twain C δ (coeff k (V j)) (coeff k (U j)))(h:∀ i j,j≤ e→ YieldP 0 1 u A δ (X.2 i j r) (Y.2 i j r)): YieldP 0 1 u (∑ _ : Alma F, ∑ _ ∈ Finset.antidiagonal e,2*A*C) δ ((Shrine X V).2 e r) ((Shrine Y U).2 e r):=by
   unfold Shrine; simp_rw [Prod.snd_sum,Stem,vein, Finset.sum_apply, affix]; apply YieldP.sum _ zero_le_one; intro i _; simp_rw [Finset.sum_apply,Pi.smul_apply]; apply YieldP.sum _ zero_le_one; intro j hj; have hv:= Finset.mem_antidiagonal.mp hj; exact (h i j.2 (by omega)).mag (hp _ _ (by omega)) zero_le_one

lemma cheapPorts (F:Frame G h)(T:SectionData F)(p:h<D)(_h:h≤k)(hC:h*h≤u)(e r:ℕ): ∃ d:ℕ,∀ I:Gear G,∃ C:ℝ,0≤ C∧∀ (A:Levels G)(Ñ:ChartRatio G)(N M m:ℕ)(W:Rally (e+1) 0 I)(hv:m<N)(hu:m<M)(g:G.Simple)(q:LocalRatio Ñ)(V:Usage A Ñ m), ClaimP A N m hv g q V _ W.P → ClaimP A M m hu g q V _ W.Q → ∀ X:ℝ,0≤ X →∀ Y Z:TowerS G D,
    (∀ i j, i≤e → YieldP 0 1 u X W.σ (Y.2 i j) (Z.2 i j)) → (∀ i j, j ≤ e→ YieldP 0 1 u W.x W.σ ((Peaks A Ñ T p N m).2 i j r) ((Peaks A Ñ T p M m).2 i j r)) →
    let E:= C*W.x^d*X; YieldP 0 1 u E W.σ ((Sink A Ñ T p N m k Y).2 e r) ((Sink A Ñ T p M m k Z).2 e r) ∧ ∀ i:Alma F,∀ j≤ e,twain E W.σ (coeff j (Spray A Ñ T p N m k Y i)) (coeff j (Spray A Ñ T p M m k Z i)):=by
    obtain ⟨d,H⟩:=orchardRough e k u (max h r) h D G; refine ⟨d+1,fun I=>?_⟩; obtain ⟨A,hA,f⟩:= H I; let C:= coinQ F hC D * A; let V:= ∑ _:Alma F,∑ _ ∈ Finset.antidiagonal e, 2*C; have hU:= coinSoar F hC D; have hc:0≤ C:=by unfold C; positivity
    have hV:0≤V:= Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=>by positivity
    let E:= A+V+C; refine ⟨E,by unfold E; positivity,?_⟩; intro A' Ñ N M m W hp hu g q V' he e' X hX Y Z hY hy D'
    let R:= Spout A' Ñ N m h k Y; let L:= Spout A' Ñ M m h k Z
    let T':= Spray A' Ñ T p N m k Y; let Z':= Spray A' Ñ T p M m k Z
    let x:=W.x; have hx:1≤ x:=W.rich
    have hr i j (hi:i≤ e) (hj:j≤max h r) : YieldP 0 1 u (A*x^d*X) W.σ (R.2 i j) (L.2 i j):= by unfold R L; rw [spout_orch _ he,spout_orch _ e']; exact f W X _ _ hX hY _ hi _ hj
    have hk i j (p:j≤ e): twain (C*x^d*X) W.σ (coeff j (T' i)) (coeff j (Z' i)):= by
          change twain _ _ (coeff j (PowerSeries.mk fun w=> glean F R.2 w i)) (coeff j (PowerSeries.mk fun w=>glean F L.2 w i)); rw [coeff_mk,coeff_mk, show C*x^d*X=coinQ F hC D*(A*x^d*X) from by unfold C; ring]; exact foreQ _ W.θ F hC (fun l i hp h=> hr l i hp (h.trans (le_max_left ..))) i p
    let U:= Shrine (Peaks A' Ñ T p N m) T'; let K:= Shrine (Peaks A' Ñ T p M m) Z'
    refine ⟨?_,fun i j t=> (hk i j t).lift (logStep (by omega) hc (show C≤E from le_add_of_nonneg_left (by positivity)) hx hX) W.θ⟩
    have hT: YieldP 0 1 u (V*x^(d+1)*X) W.σ (U.2 e r) (K.2 e r) := by unfold V; simp_rw [Finset.sum_mul]; have ht:=(tenderOp _ _ r hk hy); apply ht.step _ W.θ; exact Finset.sum_le_sum fun i _=> Finset.sum_le_sum fun j _=> le_of_eq (by unfold x; ring)
    let G:= R.2 e r; let D:= L.2 e r; let P:=U.2 e r; let Q:= K.2 e r; change YieldP _ _ _ _ _ (G-P) (D-Q)
    have he':= hr e r le_rfl (le_max_right ..); have hs: YieldP 0 1 u _ W.σ (G-P) (D-Q):= (show YieldP _ _ _ (A*x^d*X+V*x^(d+1)*X) _ _ _ from ⟨he'.wax.diff hT.wax zero_le_one, he'.wane.diff hT.wane zero_le_one, by rw [sub_sub_sub_comm,add_mul]; exact he'.toll.diff hT.toll zero_le_one⟩); apply hs.step _ W.θ; apply (add_le_add_left (logStep (k:=d+1) (by omega) hA (le_refl A) hx hX) _).trans; rw [←add_mul,←add_mul]; exact logStep le_rfl (by positivity) (le_add_of_nonneg_right hc) hx hX
-- exact linearity also parent cast.
lemma Shrine_diff (X:Island F D)(U V:Verse F): Shrine X (U-V)=Shrine X U - Shrine X V:=by
    unfold Shrine; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; let E:= vein X i
    have hp {T:Type}[AddCommGroup T][Module ℝ T]{S:Type}(P:Pal T S): affix ((U-V) i) P= affix (U i) P-affix (V i) P:=by funext e; unfold affix; simp only [Pi.sub_apply,map_sub,sub_smul,Finset.sum_sub_distrib]
    exact Prod.ext (funext fun n=> hp (E.1 n)) (hp E.2)
lemma Sin_diff {T:SectionData F}{p:h<D}{A:Levels G}{Ñ:ChartRatio G}{Y Z: TowerS G D}(g:G.Simple)(q:LocalRatio Ñ)(hv:m<N)(y:On k Y)(z:On k Z): Sink A Ñ T p N m k (Y-Z)=Sink A Ñ T p N m k Y - Sink A Ñ T p N m k Z:=by
   unfold Sink Spray; rw [Shed_sub A Ñ hv g q y z,On.read_sub F (ShedG A Ñ hv g q y le_rfl) (ShedG A Ñ hv g q z le_rfl),Shrine_diff]; abel
end YM.WilsonCoeffUV.Shard
