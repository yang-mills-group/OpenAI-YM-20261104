import YM.WilsonCoeffUV.Stable.Reading
/-! # Cost emitted rows independent of rank continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {I J V U E:Type*}{r h D l j i e k a m u N:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}
def coinQ (F:Frame G h)(p:h*h≤u)(D:ℕ): ℝ:= ∑ i∈Finset.range (h+1),(echo_credit F p i D).choose
lemma coinSoar (F:Frame G h)(p:h*h≤u)(D):0≤coinQ F p D:= Finset.sum_nonneg fun i _=> (echo_credit F p i D).choose_spec.1
lemma uniform_coin (v:Alma F)(g:h*h≤u){Y:Single G D}(ha:0≤ A)(p:∀ l< i,∀ k< valence F v,Fruit 0 1 u (Y l k) A) : ‖ptax F Y i v‖≤ coinQ F g D*A:=by
    refine (pTax_fixed F Y g v p ha).trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (s:=Finset.range (valence F v)) (t:=Finset.range (h+1)) (Finset.range_mono ((valence_cap ..).trans h.le_succ)) (fun i _ _=> (echo_credit F g i D).choose_spec.1)) ha)
lemma p_val0 (p:h*h≤u){Y:ChamberTen G (Vote D) r}(q:Fruit 0 1 u Y A)(i:Alma F)(hk:r≤h): ‖echoS F Y i‖≤coinQ F p D*A:=by
    apply ((echo_credit F p r D).choose_spec.2 i Y A q).trans; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>(echo_credit F p i D).choose_spec.1) (Finset.mem_range.mpr (by omega))) q.C
structure Clean (u e r:ℕ)(F:Frame G h)(C:ℝ)(P: Single G D) : Prop where
   fare : 0≤ C
   row i j: i< e ∨ i=e∧r≤ valence F j → ‖glean F P i j‖≤ C
lemma orchardBoss (F:Frame G h)(H:Hol G)(p:h<D)(e k u r:ℕ)(hg:h+(h+1)≤u)(hp:(h+1)*r≤u)(hV:h*h≤u): ∃ d:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (P: SumT (inkPin I) e r D u)(_:Courant I P.P.P)(X:ℝ), P.η=1→ Stakes P.Y→ Standby (P.Y e r) → (∀ i< e,∀ j,Fruit 0 1 u (P.Y i j) P.fund) → (∀ i:Alma F,valence F i=r→ glean F P.Y e i=0) → Fruit 0 1 u (P.Y e r) X →
   let B:=I.lamp; let Z:=Orchard (inkPin I) P.P.P h k P.Y; let W:= C*P.x^d*P.fund
   Fruit 0 1 u (Z e r) ((permeability H F p u r B)/(inkPin I).patch.L.val * X + W) ∧ Clean u e r F W Z:=by
   obtain ⟨d,H'⟩:= orchardTop F H p e k u r hg hp hV; obtain ⟨n,T⟩:=uniform_air e r u h h k D G
   refine ⟨d+n,fun i=>?_⟩; obtain ⟨A,hA,hC⟩:= H' i; obtain ⟨B,hB,hG⟩:= T (inkPin i); let V:= coinQ F hV D; let K:= V*B; have hv:0≤ K:= mul_nonneg (coinSoar ..) hB; let S:= (K+K)+ A; have he:A≤S:=by unfold S; linarith
   refine ⟨S,hA.trans he,?_⟩; intro P T X hx hY hz hu hF Yp B' Z Q
   obtain ⟨x,y⟩:= hC P T X hx hY hz hu hF Yp
   let u':=P.x; have hy':1≤ u':=P.P.rich; have hf:0≤ P.fund:=P.large; have hs: A*P.x^d*P.fund≤ Q:=logStep (by omega) hA he hy' hf
   have hK:0≤ Q:=le_trans (mul_nonneg (mul_nonneg hA (pow_nonneg (zero_le_one.trans hy') d)) hf) hs
   refine ⟨x.more (add_le_add_right hs _), hK,fun j w p=>?_⟩
   rw [tail_glint]; let v:=valence F w; have ht:v≤h:= valence_cap ..; let W:=B*u'^n*P.fund; have hk: K+K≤S:= le_add_of_nonneg_right hA; have hh : K+A≤S:=by unfold S; linarith
   have hY' (i' v') (p:lowerGrade i' v' e r)(h:v'≤h): Fruit 0 1 u (Z i' v') W:=hx ▸ (hG P i' v' p h).wax
   have hg: ‖ptax F Z j w‖≤K*u'^n*P.fund:=by rw [show K*u'^n*P.fund=V*W from by unfold K W; ring]; exact uniform_coin w hV (by unfold W; positivity) (fun k' hk' u v=> hY' _ u (Or.inl (by omega)) (Nat.le_trans v.le ht))
   apply (norm_add_le ..).trans; by_cases hi : lowerGrade j v e r
   · apply (add_le_add hg ((p_val0 hV (hY' j v hi ht) w ht).trans_eq (show _= K*u'^n*P.fund from by unfold K V W; ring))).trans; rw [← add_mul,← add_mul]; exact logStep (by omega) (add_nonneg hv hv) hk hy' hf
   unfold v lowerGrade at hi; have h:j=e:=by omega
   have hh' : valence F w=r:=by omega
   subst j;
   exact (add_le_add hg ((show ‖echoS F (Z e (valence F w)) w‖≤_ from by rw [hh']; exact y w hh'))).trans ((le_of_eq (show _= K*u'^n*P.fund+A*u'^d*P.fund from rfl)).trans (by
       have hv1: K*u'^n*P.fund≤ K*u'^(d+n)*P.fund:=logStep (by omega) hv le_rfl hy' hf
       have hv2: A*u'^d*P.fund≤ A*u'^(d+n)*P.fund:=logStep (by omega) hA le_rfl hy' hf
       apply (add_le_add hv1 hv2).trans; rw [← add_mul,←add_mul]; exact logStep le_rfl (add_nonneg hv hA) hh hy' hf))

-- recycled Shrine negative operator. only rank earlier. material P.Ψ from production. impose etc.
lemma stern_s (X:Island F D)(p:Shimmer X)(_:h*h≤u)(P:TowerS G D)(W:Clean u e r F C P.2) (v:x≥0)(H:∀i j,j≤ e→ Fruit 0 1 u (X.2 i j r) x) : Fruit 0 1 u ((Shrine X (opal F P)).2 e r) (∑ _ : Alma F,∑ _∈ Finset.antidiagonal e,C*x) :=by
   have hx:=W.fare; unfold Shrine; simp_rw [Prod.snd_sum,Stem,vein, Finset.sum_apply, affix]; apply Fruit.sum _ zero_le_one; intro i _; rw [Finset.sum_apply]; apply Fruit.sum _ zero_le_one; intro b hb
   have he:=Finset.mem_antidiagonal.mp hb; by_cases hv:r≤valence F i+b.2; · rw [Pi.smul_apply]; refine (Fruit.μ (H i b.2 (by omega)) _).more ((mul_le_mul_of_nonneg_right ?_ v)); rw [opal,coeff_mk]; exact W.row _ _ (by omega)
   rw [Pi.smul_apply, show X.2 i b.2 r=0 from solo_shape (p.scan.solo i) b.2 r (lt_of_not_ge hv), smul_zero]; exact Fruit.zero.more (by positivity)

-- lift from Align to actual agenda. No circular dependencies late.
def ClaimP {Ñ:ChartRatio G}(A:Levels G)(N m:ℕ)(h:m<N)(p:G.Simple)(q:LocalRatio Ñ)(V:Usage A Ñ m)(I:Gear G)(M: Stand I):Prop:= I= V.gear ∧ HEq M (V.postStand h p q)
lemma spout_orch {A:Levels G}{Ñ:ChartRatio G}{hv:m<N}{t:G.Simple}{q:LocalRatio Ñ}{V:Usage A Ñ m}{I:Gear G}{M:Stand I}(X:TowerS G D) (g:ClaimP A N m hv t q V I M) (h k): (Spout A Ñ N m h k X).2=Orchard I M h k X.2:= by
    have h:=g.1; subst I
    rw [eq_of_heq g.2]; rfl
lemma sterileCost (F:Frame G h)(H:Hol G)(T:SectionData F)(p:h<D)(_:h≤k)(e u r:ℕ)(hg:h+(h+1)≤u)(hp:(h+1)*r≤u)(hV:h*h≤u): ∃ d:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(W:Rally (e+1) 0 (inkPin I))(hv:m<N)(g:G.Simple)(q:LocalRatio Ñ)(V:Usage A Ñ m), ClaimP A N m hv g q V _ W.P → ∀Y:TowerS G D, On k Y → opal F Y=0 → Shimmer (Peaks A Ñ T p N m)→ Courant I W.P →(∀ i j,j≤e → Fruit 0 1 u ((Peaks A Ñ T p N m).2 i j r) W.x) →∀ X B:ℝ, Fruit 0 1 u (Y.2 e r) X → 0≤ B→ (∀ i j,lowerGrade i j e r → Fruit 0 1 u (Y.2 i j) B) →
    Fruit 0 1 u ((Sink A Ñ T p N m k Y).2 e r) (permeability H F p u r I.lamp/(inkPin I).patch.L.val * X + C*W.x^d * B):=by
   obtain ⟨d,H'⟩:= orchardBoss F H p e k u r hg hp hV
   refine ⟨d+1,fun I=>?_⟩; obtain ⟨A,hA,f⟩:= H' I; let E:=A+ (∑ _ : Alma F, ∑ _∈ Finset.antidiagonal e,A)
   have hE:A≤E:=le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=>hA)
   refine ⟨E,hA.trans hE,?_⟩; intro A' Ñ n m W hp G' q V he Y w z hs q' rt X B hc hB v
   let U:= Peaks A' Ñ T p n m; let Z:= Spout A' Ñ n m h k Y; have hv: Z.2= _:=spout_orch Y he h k
   let P: SumT (inkPin I) e r D u:=⟨W,Y.2,Y.2,B,1,hB,zero_le_one,le_rfl,fun i j p=> YieldP.same ((v i j p).shave (by positivity) (by rw [one_div]; exact speck_le _)) W.θ⟩
   have hg (i:Alma F): glean F Y.2 e i=0:=by rw [show glean F Y.2 e i= coeff e (opal F Y i) from Eq.symm (show coeff e (opal F Y i)=_ by rw [opal,coeff_mk]),z]; simp
   obtain ⟨ht,hx⟩:=f P q' X rfl w.flanks (solo_stretch w e r) (fun i hi r=> v i r (Or.inl hi)) (fun i _=> hg i) hc
   have hr:0≤W.x:=zero_le_one.trans W.rich
   have hd := stern_s U hs hV Z (hv.symm ▸ hx) hr rt
   change Fruit 0 1 u (Z.2 e r- (Shrine U (opal F Z)).2 e r) _; apply ((hv.symm ▸ (show Fruit 0 1 u (Orchard (inkPin I) W.P h k Y.2 e r) _ from ht)).diff hd zero_le_one).more; rw [add_assoc]; apply add_le_add_right; change A*W.x^d*B+(∑ _ : Alma F,∑ _∈ Finset.antidiagonal e,A*W.x^d*B*W.x) ≤ _; unfold E; simp_rw [add_mul,Finset.sum_mul]; refine add_le_add (logStep (by omega) hA le_rfl W.rich hB) (Finset.sum_le_sum fun i _=> Finset.sum_le_sum fun _ _=>?_); exact le_of_eq (by ring)
end YM.WilsonCoeffUV.Shard
