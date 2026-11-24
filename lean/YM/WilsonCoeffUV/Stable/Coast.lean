import YM.WilsonCoeffUV.Stable.Reproduction
/-!
# Reselect root by accurate Taylor. Two complementary estimates, same input and output moment. No cost link to aperture on Y numerically; exponential only used for certifying the transmission (e.g. algebraic equalities).
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c L:Side}{U V:Type*}{r h D l j e k a m u:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X B C M:ℝ}

-- arm Coast/far. structure with arbitrary Twig irrespective of width
section
variable [NormedAddCommGroup V]
def Coast (L:Side)(Y:ChamberTen G V r): ChamberTen G V r:= fun x=> if port_d 0 x≤ L.val then Y x else 0
def Pasture (L:Side)(Y:ChamberTen G V r): ChamberTen G V r:= fun x=> if L.val<port_d 0 x then Y x else 0
lemma zoned (P:Patch)(Y:ChamberTen G V r): Coast P.L Y +Pasture P.L Y=Y:=by
    funext x; unfold Coast Pasture; rw [Pi.add_apply]; split
    next h=> rw [if_neg (by omega), add_zero]
    next h=> rw [if_pos (by omega),zero_add]
lemma coastC (L:Side){Y:ChamberTen G V r}(p:Twig 0 s A Y): Twig 0 s A (Coast L Y):= ⟨p.1,fun x=>by
    unfold Coast; split; · exact p.2 _
    rw [norm_zero]; exact mul_nonneg p.1 (by positivity)⟩
lemma pastureC (L:Side){Y:ChamberTen G V r}(p:Twig 0 s A Y): Twig 0 s A (Pasture L Y):= ⟨p.1,fun x=>by
       unfold Pasture; split; · exact p.2 _
       rw [norm_zero]; exact mul_nonneg p.1 (by positivity)⟩
lemma jobC (L:Side){o:Cover}{Y:ChamberTen G V r}(p:Fruit o t u Y A)(h:0≤t): Fruit o t u (Coast L Y) A:=by
    refine budget_minor p (fun _=>mul_nonneg (zero_le_one.trans (autumn_pos h ..)) (norm_nonneg _)) (fun x=>?_); unfold Coast; split; exact le_rfl
    rw [norm_zero,mul_zero]; exact p.1 _
lemma cloudShrink (P:Patch){Y:ChamberTen G V r}(p:Fruit 0 1 u Y A)(hp:k+m≤u): Fruit 0 1 k (Pasture P.L Y) (speck P^m*A):=by
   have he := p.C; have ht:= speck_pos P
   refine budget_minor (cap_scale p (show 0≤speck P^m by positivity)) (fun _=>mul_nonneg (hedge_nn zero_le_one _) (norm_nonneg _)) ?_; intro x; unfold Pasture; split
   next h =>
      rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); change autumn 1 k (port_d 0 x) ≤ speck P^m * autumn 1 u (port_d 0 x); let D:ℝ:= 1+ port_d 0 x; unfold autumn; simp only [one_mul]; have hD:1≤ D:=by unfold D; linarith only [show 0≤ (port_d 0 x:ℝ) by positivity]
      have hL : (P.L.val:ℝ)≤ (port_d 0 x:ℝ):= Nat.cast_le.mpr h.le
      unfold speck; rw [inv_pow, ← div_eq_inv_mul]; apply (le_div_iff₀ (by positivity)).mpr
      change D^k* _ ≤ _; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show (P.L.val:ℝ)≤ D from hL.trans (le_add_of_nonneg_left zero_le_one)) m) (pow_nonneg (zero_le_one.trans hD) k)); rw [← pow_add]; exact pow_le_pow_right₀ hD hp
   rw [norm_zero,mul_zero]; exact mul_nonneg (by positivity) (p.1 _)
lemma cloudPay (P:Patch){Y:ChamberTen G V r}(p:Fruit 0 1 u Y A)(h:k≤u): Fruit 0 (1/P.L.val) u (Pasture P.L Y) (2^u*speck P^k*A):=by
   set S:=speck P; have ht:0<S:= speck_pos P
   have hA:= p.C
   refine budget_minor (cap_scale p (show 0≤2^u*S^k by positivity)) (fun _=>mul_nonneg (hedge_nn (show 0≤(1:ℝ)/P.L.val by positivity) _) (norm_nonneg _)) ?_; intro x; unfold Pasture; split
   next g=>
      let L:ℝ:=↑P.L.val; have hL:0<L:=by unfold L; positivity
      rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); let M:= port_d 0 x; change autumn _ u M ≤ _*autumn _ u M; unfold autumn; simp only [one_mul]; have hp:S≤1:=speck_le P
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hp h) (show 0≤(2:ℝ)^u by positivity)) (show 0≤(1+M:ℝ)^u by positivity)); rw [←mul_pow,←mul_pow]; apply pow_le_pow_left₀ (by positivity); change (1:ℝ)+1/L*M≤ _; rw [show S=L⁻¹ from rfl, div_mul_eq_mul_div,one_mul]; field_simp; linarith [show L≤M from Nat.cast_le.mpr g.le]
   rw [norm_zero,mul_zero]; exact mul_nonneg (by positivity) (p.1 _)
end

-- near high/deep (input in L units)
lemma rug_snap (G:Gauge)(X:ℝ)(hs:0<s)(r h D u:ℕ)(hp:(h+1)*r≤u)(i:Fin r→Fin (h+2)): ∃ T:ℝ,0≤ T∧∀ (P:Patch)(Q:Drip P G)(w:Site P.L)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(A:ℝ), Crank Q (h+1) s X→Fruit 0 1 u Y A →
   ‖pluck (Coast P.L Y) (fun j=>splint P Q w (x j) (h+1) (i j))‖ ≤ T*speck P^(mMarked i)*Real.exp (-s*port_d 0 x)*A:=by
   obtain ⟨B,hb,H⟩:= break_money G (h+1) s hs
   by_cases he:0≤ X; swap; · exact ⟨0,le_rfl,fun P Q w x Y A h=> (he h.1).elim⟩
   let V:= (B*X)^r*(Real.exp s)^r; have hv:0≤ V:=by unfold V; positivity
   refine ⟨V,hv,fun P Q w x Y A g a=>?_⟩; have hsp:= speck_pos P
   set T:=V*speck P^(mMarked i)*Real.exp (-s*port_d 0 x); let F j:=splint P Q w (x j) (h+1) (i j); have hT:0≤T:=by unfold T; positivity [speck_pos P]
   have hP (y:Fin r→YForest G)(p: port_d 0 y ≤ P.L.val): ‖∏ j,F j (y j)‖≤ T*hedge 0 1 u y:=by
       set K:= hedge 0 1 (h+1) y * Real.exp s
       have ht j : ‖F j (y j)‖≤ rentM P s (B*X) ((i j).val+1) (x j)*K:=by
          have hx : (size (y j).1:ℝ)≤ P.L.val:=Nat.cast_le.mpr ((port_size ..).trans p); refine (H P Q X g w (x j) (i j) (y j)).trans ?_; unfold K hedge autumn rentM; rw [one_mul]; gcongr
          · exact port_size ..
          rw [div_mul_eq_mul_div]; apply (div_le_iff₀ (by positivity)).mpr; exact mul_le_mul_of_nonneg_left hx hs.le
       rw [norm_prod]; refine (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>ht j)).trans ?_; have hK :0≤ K:=by unfold K; exact mul_nonneg (hedge_nn zero_le_one _) (by positivity)
       rw [Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ,Fintype.card_fin]; apply (mul_le_mul_of_nonneg_right (term_money P s (B*X) hs.le (by positivity) x i) (pow_nonneg hK r)).trans
       unfold K; rw [mul_pow (hedge _ _ _ _) _]; have hh: hedge 0 1 (h+1) y ^r≤ hedge 0 1 u y:= by unfold hedge autumn; rw [←pow_mul]; exact pow_le_pow_right₀ (by simp) hp
       apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (show 0≤(Real.exp s)^r by positivity)) (by positivity)).trans; exact le_of_eq (by unfold T V; ring)
   have hv' (x:Fin r→ YForest G):‖pressOn (Coast P.L Y) F x‖ ≤ T*(hedge 0 1 u x* ‖Coast P.L Y x‖):=by
      unfold pressOn; by_cases h: port_d 0 x≤ P.L.val
      · rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hP x h) (norm_nonneg _)).trans_eq (mul_assoc ..)
      unfold Coast; rw [if_neg h,smul_zero,norm_zero,mul_zero,mul_zero]
   have hk:= budget_minor (cap_scale (jobC P.L a zero_le_one) hT) (fun i=> norm_nonneg _) hv'
   exact (norm_tsum_le_tsum_norm hk.2.1).trans hk.2.2

-- low even tail in OUTPUT exponential! Bernstein multi; unit polynomial from Newton.
lemma plain_charge (H:ℕ) (P:Patch)(Q:Drip P G)(w:Site P.L)(g:Crank Q H s X)(x y:YForest G){b: Fin (H+1)} (h:b.val<H): ‖splint P Q w x H b y‖ ≤ (((4*((b.val:ℝ)+1))^b.val)*X)*speck P^(b.val+1)*Real.exp (-s*size x.1)*((1+size y.1:ℝ)^b.val):=by
   rw [splint,if_pos h,stain]; let f (z:Cover):= sip P Q w x (z,y.2); have hx:=g.1
   have ht:=speck_pos P; let K:=X*speck P^(b.val+1)*Real.exp (-s*size x.1); have hK:0≤ K:=by unfold K; positivity
   exact (Newt.component _ f hK (fun l h'=> (price_o g _ (show l.length≤ H from by omega) y.2 x).trans_eq (by rw [h'])) y.1).trans_eq (by unfold K; ring)
-- far low pluck inherits speckA only from mass reserve even (no smooth need)
lemma buds (G:Gauge)(X:ℝ)(hs:0<s)(r h D u:ℕ)(i:Fin r→Fin (h+2))(hi:mMarked i≤h)(p:mMarked i+(h+1)≤ u):∃ T:ℝ, 0≤ T∧∀ (P:Patch)(Q:Drip P G)(w:Site P.L)(x:Fin r→YForest G)(Y:ChamberTen G (Vote D) r)(A:ℝ), Crank Q (h+1) s X→Fruit 0 1 u Y A →
    ‖pluck (Pasture P.L Y) (fun j=>splint P Q w (x j) (h+1) (i j))‖ ≤ T*Real.exp (-s*port_d 0 x)*speck P^(h+1)*A:=by
    by_cases he:0≤ X; swap; · exact ⟨0,le_rfl,fun P Q w x Y A h=> (he h.1).elim⟩
    let C j:= (((4*(((i j).val:ℝ)+1))^(i j).val)*X)
    let B:=∑ j,C j; have hh (j):0≤C j:=by unfold C; positivity;
    have hb :0≤B:= Finset.sum_nonneg fun j _=> hh j; let T:= B^r; have hT:0≤ T:=by unfold T; positivity
    refine ⟨T,hT,fun P Q w x Y A g a=>?_⟩; have hp:= speck_pos P
    let S:= Pasture P.L Y; let F j:= splint P Q w (x j) (h+1) (i j)
    let V:= T*Real.exp (-s*port_d 0 x); have hv :0≤V:=by unfold V; positivity
    have hp y: ‖pressOn S F y‖ ≤ V*(hedge 0 1 (mMarked i) y*‖S y‖):=by
       unfold pressOn; rw [norm_smul,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
       have hF j : ‖F j (y j)‖≤ rentM P s B ((i j).val+1) (x j)*hedge 0 1 (1+(i j).val) y:=by
          have hx : (i j).val<h+1:=by
               have H:= (Finset.single_le_sum (f:=fun j=>1+(i j).val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)).trans hi; omega
          apply (plain_charge _ P Q w g (x j) (y j) hx).trans; unfold rentM hedge autumn; rw [one_mul]; have he:C j≤ B:= Finset.single_le_sum (fun i _=> hh i) (Finset.mem_univ j); unfold C at he; gcongr
          refine le_trans ?_ (pow_le_pow_right₀ (show (1:ℝ) ≤ 1+(tread Bank.terrain 0 y:ℝ) by simp) (show (i j).val≤1+(i j).val by omega)); gcongr; exact port_size ..
       rw [norm_prod]; refine (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=>hF j)).trans ?_; rw [Finset.prod_mul_distrib]; have hr: (∏ j,hedge 0 1 (1+(i j).val) y)= hedge 0 1 (mMarked i) y := Finset.prod_pow_eq_pow_sum ..
       rw [hr]; apply mul_le_mul_of_nonneg_right _ (hedge_nn zero_le_one _); apply (term_money P s B hs.le hb x i).trans; unfold V T; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (speck_pos P).le (speck_le _))) (by positivity)
    have hx:= budget_minor (cap_scale (cloudShrink P a p) hv) (fun _=>norm_nonneg _) hp
    exact (norm_tsum_le_tsum_norm hx.2.1).trans (hx.2.2.trans_eq (by unfold V; ring))
end YM.WilsonCoeffUV.Shard
