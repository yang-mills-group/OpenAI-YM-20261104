import YM.WilsonCoeffUV.Stable.Coast
/-!
# Finish estimate of pre-length polynomial λ and smooth booth
-/
set_option autoImplicit false
set_option maxHeartbeats 580000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c L:Side}{U V:Type*}{r h D l j e k a m u:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X B C M δ:ℝ}
lemma pluck_sub [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{P Q:ChamberTen G V r}(p:Twig 0 s A P)(q:Twig 0 s A Q)(h:0<s){b: Fin r→ Leg G}(ht:∀ i,Wages (b i)): pluck (P-Q) b=pluck P b-pluck Q b:=by unfold pluck; rw [← (pluck_profit p h ht).of_norm.tsum_sub (pluck_profit q h ht).of_norm]; exact tsum_congr fun _=>smul_sub ..
lemma paperPay (F:Labels.Frame G h)(H:Hol G) (i: Fin r→Fin (h+2))(b: Embroider.Spiral h)(e:mMarked i+b.val.card≤h)(hp:h<u)(D:ℕ)(C:ℝ)(p:0<s):∃ T:ℝ,0≤ T∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(t A M:ℝ), 0<t→ Crank Q (h+1) s C→Smooth Y→ mural Y→ Twig 0 t A Y→ VectorWind 0 1 u M Y→ Hears F h M Y →
       ‖pluck Y (fun j=> splint P Q w (x j) (h+1) (i j)) (wallope b.val D)‖≤ T*M*Real.exp (-s*port_d 0 x):=by
    by_cases c:0≤C; swap; · exact ⟨0, le_rfl,fun _ _ _ _ _ _ _ _ _ H=> (c H.1).elim⟩
    let n j:= 1+(i j).val
    obtain ⟨T,hT,hp⟩:= gateway H F n b.val e le_rfl D hp
    choose E hE hu using fun j=> break_charge G (i j).val
    let B:= ∑ i,E i; have hB :0≤ B:= Finset.sum_nonneg (fun i _=>hE i)
    refine ⟨T*(B*C)^r,by positivity,fun P w Q x Y t A M ht g a v u l k=>?_⟩
    let f j:= breaks P Q w (x j) (i j).val
    have he (j:Fin r): (i j).val<h+1:=by
        have hx: n j≤ h:= (Finset.single_le_sum (s:=Finset.univ) (f:=n) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)).trans ((Nat.le_add_right _ _).trans e); unfold n at hx; omega
    have hx j: f j∈rangeLt _ (n j):=by unfold n; rw [add_comm]; exact breaks_in P Q w (x j) _
    simp_rw [splint,if_pos (he _)]; refine (hp t Y A M ht u v a k l f hx).trans ?_; have hh:= VectorWind.pos l
    have H : (∏ i, slideRank (n i) (f i))≤ (B*C)^r*Real.exp (-s*port_d 0 x):=by
       refine (Finset.prod_le_prod (s:= Finset.univ) (fun _ _=> slide_nn _ _) (fun j _=> (show slideRank (n j) (f j)≤ rentM P s (B*C) ((i j).val+1) (x j) from ?_))).trans ((term_money P s (B*C) p.le (by positivity) x i).trans ?_)
       · unfold n; rw [add_comm]; apply (hu j P (h+1) C s Q (he j).le g w _).trans; unfold rentM; have hg:E j ≤ B:= Finset.single_le_sum (fun i _=> hE i) (Finset.mem_univ j); have := speck_pos P; gcongr
       gcongr; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (speck_pos P).le (speck_le P))
    exact (mul_le_mul_of_nonneg_left H (by positivity)).trans_eq (by ring)
lemma rummage (F:Labels.Frame G h)(H:Hol G) (i: Fin r→Fin (h+2))(b: Chunk h)(e:h<D)(X:ℝ)(g:h+(h+1)≤u)(hp:(h+1)*r≤u)(hs:0<s):
    ∃ T:ℝ,0≤ T∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(t A M B:ℝ)(f:Scroll D), 0<t→ Crank Q (h+1) s X→ Smooth Y→ mural Y→ Twig 0 t B Y→ VectorWind 0 1 u M Y→ Hears F h M Y → Fruit 0 1 u Y A →
       ‖pluck (Coast P.L Y) (fun j=> splint P Q w (x j) (h+1) (i j)) (jotC P w f b)‖≤ (T*(A*speck P^(h+1)+M))*Real.exp (-s*port_d 0 x)*‖page D f‖:=by
   by_cases H0 : h+1≤mMarked i+rateC b
   · obtain ⟨L,hL,h⟩:= rug_snap G X hs r h D u hp i
     obtain ⟨c,hc,hf⟩:= chunk_prep b e
     refine ⟨L*c,by positivity,fun P w Q x Y t A M B f _ g a u _ v z Yp=>?_⟩
     have hp := h P Q w x Y A g Yp; let S:= speck P; have hS : 0<S:= speck_pos P; set K:= Real.exp (-s*port_d 0 x); have hk : 0≤ K:=by unfold K; positivity
     have ha:=Yp.C; have he:=z.fair; apply ((pluck (Coast P.L Y) _).le_opNorm (jotC P w f b)).trans; refine (mul_le_mul hp (hf P w f) (norm_nonneg _) (by positivity [speck_pos P])).trans ?_
     rw [show _*(c* (_ * ‖page D f‖))= L*c*(A*S^(mMarked i+rateC b))*K*‖page D f‖ from by unfold S; ring]; gcongr; exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hS.le (speck_le P) H0) ha).trans (le_add_of_nonneg_right he)
   cases b with
   | none => simp only [rateC] at H0; omega
   | some b=>
      have he:mMarked i+b.val.card≤h:=Nat.le_of_lt_succ (Nat.lt_of_not_ge H0)
      have hx:mMarked i≤h:=by omega
      obtain ⟨T,hT,hg⟩:= paperPay F H i b he (show h<u from by omega) D X hs
      obtain ⟨W,hW,hb⟩:= buds G X hs r h D u i hx (by omega)
      let V:=wallope b.val D; let U:= W*‖V‖; have hv:0≤ U:=mul_nonneg hW (norm_nonneg _); refine ⟨U+T,by positivity,fun P w Q x Y t A M B f ht g a y v m z p=>?_⟩
      let F j:= splint P Q w (x j) (h+1) (i j); let M':=pluck Y F; let Z:=pluck (Pasture P.L Y) F
      have hS:= speck_pos P; have hy : ‖halo P w b.val f‖ ≤ ‖page D f‖:= (halo_bound P w f b.val (le_trans b.property e.le)).trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hS.le (speck_le _)))
      have hw:= hS.le; have hM:= z.fair; have ha:=p.C; let K:= Real.exp (-s*port_d 0 x); have hk:0≤K:=by unfold K; positivity
      rw [jotC,map_smul,norm_smul,mul_comm, show Coast P.L Y=Y-Pasture P.L Y from eq_sub_of_add_eq (zoned P Y), pluck_sub v (pastureC P.L v) ht (fun j=> splints _ _ _ _ g hs _), _root_.sub_apply]
      refine mul_le_mul ((norm_sub_le (M' V) (Z V)).trans ?_) hy (norm_nonneg _) (by positivity)
      have hp:= (Z.le_opNorm V).trans (mul_le_mul_of_nonneg_right (hb P Q w x Y A g p) (norm_nonneg _)); apply (add_le_add (hg P w Q x Y t B M ht g a y v m z) hp).trans
      rw [show _ *A*‖V‖= U*(A*speck P^(h+1))*K from by unfold K U; ring]; rw [show T*M* _+_= (U*(A*speck P^(h+1))+T*M)*K from by unfold K; ring, mul_add (U+T)]; gcongr <;> linarith
lemma coastPrice (F:Labels.Frame G h)(H:Hol G) (r:ℕ)(e:h<D)(X:ℝ)(g:h+(h+1)≤u)(hp:(h+1)*r≤u)(hs:0<s):
    ∃ T:ℝ,0≤ T∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(Y:ChamberTen G (Vote D) r)(t A M B:ℝ), 0<t →Crank Q (h+1) s X→ Smooth Y→ mural Y→ Twig 0 t B Y→ VectorWind 0 1 u M Y→ Hears F h M Y → Fruit 0 1 u Y A →
       Twig 0 s (T*(A*speck P^(h+1)+M)) (pulseS P w Q (Coast P.L Y)):=by
    choose T hT h' using fun (i:Fin r→Fin (h+2))(b:Chunk h)=> rummage F H i b e X g hp hs
    let V:= ∑ i,∑ b,T i b; have hv:0≤V:= Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> hT _ _
    refine ⟨V,hv,fun P w Q Y t A M B ht g a o q v z Yp=>?_⟩; let S:= A*speck P^(h+1)+ M; have hh:= z.fair; have hS : 0≤ S:= by unfold S; have H:= Yp.C; positivity [speck_pos P]
    refine ⟨mul_nonneg hv hS,fun x=>?_⟩; set K := Real.exp (-s*port_d 0 x); have hk : 0≤ K:=by unfold K; positivity
    apply ContinuousLinearMap.opNorm_le_bound _ (show 0≤ V*S*K by positivity); intro c
    let Z:=Coast P.L Y; obtain ⟨f,rfl⟩:= submitted c; rw [pulse_dress P w Q g Z (coastC P.L q) ht hs]; let R i j:=splint P Q w (x i) (h+1) j
    rw [show (fun i=>sip P Q w (x i))=fun i=>∑ b,R i b from funext fun i=> sipping P Q w (x i) _, gathers Z R (fun i=>splints P Q w (x i) g hs) (coastC P.L q) ht]; change ‖(∑ i:Fin r→Fin (h+2), pluck Z (fun j=> R j (i j))) (foldWord P w D (page D f))‖≤ _
    rw [chunks P w f h,_root_.sum_apply]; simp_rw [map_sum]
    unfold V; simp_rw [Finset.sum_mul]; apply (norm_sum_le ..).trans; exact Finset.sum_le_sum fun i _=> (norm_sum_le ..).trans (Finset.sum_le_sum (fun b _=> h' i b P w Q x Y t A M B f ht g a o q v z Yp))

-- numerical constants not dependent on P, L, Aperture inherited by Y!
def throughP (s:ℝ)(G:Gauge)(u r:ℕ):= ceilPoly u (s/2) * tiePay (Hooks G) r (s/2)
lemma twig_lp [NormedAddCommGroup V]{Y:ChamberTen G V r}(p:Twig 0 s A Y)(hp:0<s)(u:ℕ): Fruit 0 1 u Y (A*throughP s G u r):=by
   have h:=shrub _ _ p hp u; simp only [sub_zero,zero_mul,Real.exp_zero, mul_one] at h; unfold Fruit Award hedge autumn throughP; rw [←mul_assoc]; simp_rw [one_mul]; exact h

lemma mantleR (P:Patch)(Q:Drip P G)(s B:ℝ)(hs:0<s)(p:dragCup Bank.terrain s B Q) (u:ℕ)(Y:ChamberTen G (Vote D) r)(η:ℝ)(he:0≤η)(hu:η≤1)(g: Fruit 0 (η/P.L.val) u Y A)(h:ℕ): Fruit 0 η u (hall P h Q Y) ((P.L.val:ℝ)^h*((B*tender (Hooks G) s u)^r*(9^u*A))):=by
    have hv (w:Site P.L): Fruit (P.L.val • (0:Cover)+lift w) (η/P.L.val) u (featherS P w Y) A:=by rw [smul_zero,zero_add]; exact (((show Fruit (lift w) _ _ _ _ by simpa only [add_zero] using g.turn (lift w)).touch (soprano P w D) (by positivity)).more (mul_le_of_le_one_left g.C (budgetS ..)))
    have hh (w:Site P.L) : Fruit 0 η u (pulseS P w Q Y) ((B*tender (Hooks G) s u)^r*(9^u*A)):=by
       have hk:= roses _ hs _ (fun _=>p) (hv w) he hu; rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hk; exact hk
    rw [←tier_cash]; exact (Fruit.sum (S:=Finset.univ) (fun w _=> hh w) he).μ _

theorem repeatCap (F:Labels.Frame G h)(H:Hol G) (r:ℕ)(e:h<D)(X:ℝ)(g:h+(h+1)≤u)(hp:(h+1)*r≤u)(hs:0<s): ∃ C:ℝ,0≤ C∧∀ (P:Patch)(Q:Drip P G)(Y:ChamberTen G (Vote D) r)(t A M B:ℝ),0<t →Crank Q (h+1) s X→ Smooth Y→ mural Y→ Twig 0 t B Y→ VectorWind 0 1 u M Y→ Hears F h M Y → Fruit 0 1 u Y A →
    Fruit 0 1 u (hall P h Q Y) ((C/(P.L.val:ℝ))*A+C*(P.L.val:ℝ)^h*M):=by
    by_cases hv:0≤X; swap; · exact ⟨0,le_rfl,fun _ _ _ _ _ _ _ _ H=>(hv H.1).elim⟩
    obtain ⟨T,hT,p⟩:= coastPrice F H r e X g hp hs; let S:= throughP s G u r; let V:= (X*tender (Hooks G) s u)^r*9^u*2^u; let C:= V+T*S
    have hV:0≤V:=by unfold V; have h:= tender_nn hs (Hooks G) u; positivity
    have hS:0≤S:= mul_nonneg (ceilPoly_pos ..).le (tie_nn (by positivity) _); have hc: T*S≤ C:=le_add_of_nonneg_left hV
    refine ⟨C,(mul_nonneg hT hS).trans hc,fun P Q Y t A M B ht g' a v q m z Yp=>?_⟩; set L:ℝ:=(P.L.val:ℝ); set Z:=Pasture P.L Y
    have hL:0<L:=by unfold L; positivity
    have hx: Fruit 0 1 u (hall P h Q (Coast P.L Y)) (L^h*(T*(A*speck P^(h+1)+M))*S):=by
       refine twig_lp (s:=s) (V:=Vote D) ?_ hs u; unfold L; rw [←tier_cash]; exact Cork.μ (Cork.sum (s:=Finset.univ) (fun w _=> p P w Q Y t A M B ht g' a v q m z Yp)) _
    have hB: dragCup Bank.terrain s X Q:= g'.polish.le (div_le_self hv (by exact_mod_cast P.L.property)); have hy:= mantleR P Q s X hs hB u Z 1 zero_le_one le_rfl (cloudPay P Yp (k:=h+1) (by omega)) h
    let c:=min t s; have hc':0<c:=lt_min ht hs; have hk:c/L≤ t:= le_trans (div_le_self hc'.le (by unfold L; exact_mod_cast P.L.property)) (min_le_left ..)
    have he: hall P h Q (Coast P.L Y)+hall P h Q Z=hall P h Q Y:=by
        rw [show Coast P.L Y= Y-Z from eq_sub_of_add_eq (zoned P Y),hall_diff P Q (hB.mono (min_le_right ..)) Y Z q (pastureC P.L q) hc' hk h, sub_add_cancel]
    rw [←he]; apply (hx.plus hy zero_le_one).more; have hh:L^h*speck P^(h+1)=1/L:=by unfold speck; rw [inv_pow,pow_succ]; unfold L; field_simp
    change L^h*_ *S+L^h*_ ≤ _
    calc
       _ = C*(L^h*speck P^(h+1))*A+(T*S)*L^h*M := by unfold C V; ring
       _ ≤ _ := by rw [hh,show C*(1/L)=C/L from by ring]; gcongr; exact z.fair
end YM.WilsonCoeffUV.Shard
