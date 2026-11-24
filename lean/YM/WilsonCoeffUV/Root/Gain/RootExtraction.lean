import YM.WilsonCoeffUV.Root.Step.MeanWind
/-!
# Read the stamp coordinates by through-slot tests and conversely.
Symmetry is required. Uses same normalization as ABC ontology.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A:ℝ}
private def pebble (x:YForest G)(h:ℕ): Lawn (Cart G h)→L[ℝ]ℝ:= (fderiv ℝ (flex x) 0).comp (casing G h).symm.toContinuousLinearMap
private lemma pebble_at (x:YForest G)(u:Snap G h): pebble x h (casing G h u)=grain u x:=by rw [pebble,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]; exact grace u x
private lemma pebble_fee (x:YForest G) (p:Fin r→YForest G)(i:Fin r)(hf:x=p i): ‖pebble x h‖≤ (Fountain.tune G h 1 1).choose*(1+(port_d 0 p):ℝ)^h:=by
    let C:= (Fountain.tune G h 1 1).choose; have hx:0≤C:=(Fountain.tune ..).choose_spec.1
    let b (_:Fin 1):= x
    have hp: port_d 0 b ≤ port_d 0 p:=by
       let P : Fin 2→ Cover:= Fin.cons 0 (Prod.fst ∘ b); let K: Fin (r+1)→Cover:= Fin.cons 0 (Prod.fst ∘ p)
       have he (u:Fin 2): ∃ j,P u=K j:=by refine Fin.cases ⟨0,rfl⟩ (fun j=>⟨i.succ,?_⟩) u; simp only [P,K,Fin.cons_succ,Function.comp_apply,b,hf]
       apply league_le Bank.terrain P; intro j k; obtain ⟨u,hu⟩:= he j; obtain ⟨v,hv⟩:= he k; rw [hu,hv]; exact leg_le Bank.terrain K _ _
    apply ContinuousLinearMap.opNorm_le_bound (pebble x h) (by positivity); intro X; obtain ⟨f,rfl⟩:=(casing G h).surjective X
    rw [pebble_at, show grain f x= Tensor.diagonal (skyline h b 1) (casing G h f) by simp [on_k,b]]
    apply ((skyline h b 1).le_opNorm (fun _=> casing G h f)).trans; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply ((Fountain.tune G h 1 1).choose_spec.2 b).trans
    change C*(1+(port_d 0 b):ℝ)^(h*1) ≤ C*(1+(port_d 0 p):ℝ)^h; rw [mul_one]; gcongr
private def gem (y:Fin r→YForest G)(h:ℕ): Glas G h r:= (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap (fun i=>pebble (y i) h)
lemma emerald (y:Fin r→YForest G)(u:Fin r→Snap G h): gem y h (fun i=>casing G h (u i))= ∏ i,grain (u i) (y i):=by
   unfold gem; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp_rw [pebble_at]; rfl
private lemma gems {P:ChamberTen G (Vote D) r} (q:Twig 0 s A P)(h0:0<s)(c:Volume D) (h:ℕ): Summable fun y=> ‖(P y c) • gem y h‖ := by
   let C:= (Fountain.tune G h 1 1).choose; let g:=ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ; let W:=‖c‖*‖g‖*C^r
   have hp:0≤ C := (Fountain.tune ..).choose_spec.1; have ht : 0≤W:=by unfold W; positivity
   have he:=shrub _ P q h0 (h*r); simp only [zero_mul,Real.exp_zero,mul_one] at he
   refine (budget_minor (cap_scale he ht) (fun _=>norm_nonneg _) (fun y=>?_)).2.1
   have hv:‖gem y h‖≤‖g‖*(C*(1+(port_d 0 y):ℝ)^h)^r:=by
      apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le g _); apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>pebble_fee (h:=h) (y i) y i rfl)).trans_eq (by change (∏ _ : Fin r,C*(1+(port_d 0 y):ℝ)^h)=_; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin])
   rw [norm_smul]; apply (mul_le_mul ((P y).le_opNorm _) hv (norm_nonneg _) (by positivity)).trans_eq _; rw [mul_pow, pow_mul]; unfold W; ring
lemma gemsRead {P:ChamberTen G (Vote D) r} (q: Twig 0 s A P)(hc:0<s)(e:Smooth P)(c:Volume D)(X:Fin r→Snap G h): latent (arret c P h r) X=∑' y,(P y c)*(∏ i,grain (X i) (y i)):=by
    let v (i):= P i c; let b (x:Fin r→Lawn (Cart G h))(y):=v y*gem y h x; let T:=∑' y,v y • gem y h
    have ht x:T x=∑' y,b x y:=(ContinuousMultilinearMap.apply ℝ (fun _:Fin r=>Lawn (Cart G h)) ℝ x).map_tsum ((gems q hc c h).of_norm)
    have hg : Tensor.Sym T:=by
       intro x σ; rw [ht,ht]; let u i:= (casing G h).symm (x i)
       let S:= (σ.symm).arrowCongr (Equiv.refl (YForest G))
       rw [← S.tsum_eq]; refine tsum_congr fun y=>?_; unfold b; have he: x=fun i=>casing G h (u i):= funext fun i=> ((casing G h).apply_symm_apply _).symm
       have hS : S y=y ∘ σ:=rfl
       rw [hS,show v (y∘σ)=v y from congr_arg (fun z:Vote D=>z c) (e σ y)]; apply congr_arg ((v y)*·)
       rw [show x ∘ σ = fun i=> casing G h (u (σ i)) from funext fun i=> congr_fun he _,emerald,he,emerald]; exact Equiv.prod_comp σ (fun i=>grain (u i) (y i))
    have he: arret c P h r=T:=by
       apply Tensor.ext_diag _ _ (arret_seal c P _ _ q hc) hg; funext x; obtain ⟨Y,rfl⟩:=(casing G h).surjective x
       unfold Tensor.diagonal; rw [arret_pays _ _ _ _ q hc,ht]; refine tsum_congr fun v=>?_
       unfold b; apply congr_arg ((P v c)*·); rw [emerald _ (fun _=> Y)]; exact on_k v Y
    change arret c P h r _=_; rw [he,ht]; exact tsum_congr fun y=> congr_arg ((P y c)*·) (emerald y X)

-- exact tile using taps. Finite-dimensional cost below.
variable (F)
private def casting (G:Gauge)(h r k:ℕ): Submodule ℝ (Glas G h r) where
    carrier:= {M|Tensor.Sym M ∧seedTile M k∈ localFields G h}
    zero_mem':= by
       refine ⟨fun _ _=>rfl,?_⟩; rw [seeding_empty]; exact Submodule.zero_mem _
    add_mem':=fun {a b} ⟨x,y⟩ ⟨u,v⟩=> ⟨fun i w=>congr_arg₂ (·+·) (x i w) (u i w),by rw [seeding_sum]; exact Submodule.add_mem _ y v⟩
    smul_mem':=fun c x ⟨u,v⟩=> ⟨fun i w=>congr_arg (c • ·) (u i w),by rw [seeding_scale]; exact Submodule.smul_mem _ _ v⟩

abbrev Wait (h r k:ℕ):= {u:Fin r→Fin (h-1)// Parts.rate u=k}
private def yarn (b: Fin (h-1)) : Lawn (Cart G h) →L[ℝ] Snap G h :=
    (ContinuousLinearMap.single ℝ (fun j:Fin (h-1)=>Taylor G j.val) b).comp ((ContinuousLinearMap.proj b).comp (casing G h).symm.toContinuousLinearMap)
def pearls (b: Wait h r k)(j:Fin r→Cart G h): Fin r→Snap G h:= fun i=> yarn (b.val i) (Pi.single (j i) 1)
lemma pearls_tapped (b:Wait h r k)(j:Fin r→Cart G h)(i): throughSlot (pearls b j i : Snap G h) ((b.val i).val+2):=by
    intro m e; change (Pi.single (b.val i) (_:Taylor G (b.val i).val):Snap G h) m=_; rw [Pi.single_eq_of_ne (show m ≠ b.val i from fun u=>by rw [u] at e; omega)]
def bagg (G:Gauge)(h r k:ℕ): Glas G h r→ₗ[ℝ] (Wait h r k×(Fin r→ Cart G h)→ℝ) where
    toFun M i:= latent M (pearls i.1 i.2)
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
private lemma bags_fill (T: Glas G h r)(p:bagg G h r k T=0)(b:Fin r→Fin (h-1)) (e:Parts.rate b=k)(A:Fin r→ Lawn (Cart G h)): latent T (fun i=>yarn (b i) (A i))=0:=by
    let y i:= yarn (G:=G) (b i); let c (i:Cart G h):Lawn (Cart G h):= Pi.single i 1
    have he i: y i (A i)= ∑ j:Cart G h, A i j • y i (c j):=by

       conv_lhs => rw [show A i = ∑ j:Cart G h, A i j • c j from funext fun k=> by simp [c,Pi.single_apply]]
       rw [map_sum]; exact Finset.sum_congr rfl fun j _=>map_smul (y i) ..
    change latent T (fun i=> y i (A i))=0; simp_rw [he]; rw [(latent T).map_sum (fun i j=> A i j • y i (c j))]; apply Finset.sum_eq_zero; intro f _; rw [(latent T).map_smul_univ,show latent T (fun i=>y i (c (f i)))=0 from congr_fun p ((⟨b,e⟩: Wait h r k),f),smul_zero]
private lemma bag_empty {T:Glas G h r} (p:bagg G h r k T=0): seedTile T k=0:=by
   refine eval_ext _ _ fun J=>?_; rw [reads_seedTile,map_zero]; apply Complex.ofReal_eq_zero.mpr
   let M:= latent T; let Y:= trunk h J; let W (b:Fin r→ Fin (h-1)):= M (fun i=> Pi.single (b i) (Y (b i)))
   have hx (t:ℝ):vein T J t=∑ b:Fin r→Fin (h-1), t^(Parts.rate b) • W b:=by
       change M (fun _=> engineered t Y)= _; simp_rw [Parts.spread_scale]; rw [M.map_sum (fun _ j=> t^(j.val+2) • (Pi.single j (Y j):Snap G h))]; apply Finset.sum_congr rfl; intro b _; rw [M.map_smul_univ, Finset.prod_pow_eq_pow_sum]; rfl
   rw [funext hx,lead_sum _ _ (fun _ _=> (monoSmooth ..).contDiffAt)]; simp_rw [lead_monomial]; apply Finset.sum_eq_zero; intro b _; split; rename_i ht
   · unfold W M; have hv:= bags_fill _ p b ht.symm (fun _=> casing G h Y); convert hv; unfold yarn; simp
   rfl
lemma bell_floor (T:Glas G h r)(s: Tensor.Sym T)(p:seedTile T k∈ localFields G h): Bell F k r T=0 ↔ bagg G h r k T=0:=by
   rw [detecting _ _ _ p]; constructor
   · intro H; have ht:= F.coords.injective (H.trans (map_zero F.coords).symm)
     funext ⟨v,j⟩; unfold seedTile at p
     let b:= v.val; let A (i):=(casing G h).symm (Pi.single (j i) 1)
     apply Complex.ofReal_inj.mp
     have he: Tensor.Sym (castP T):=fun i y=> congr_arg (Complex.ofReal) (s (casing G h ∘ i) y)
     exact Parts.tile_detects _ he b (by rw [show Parts.rate b=k from v.property]; exact congr_arg Subtype.val ht) (fun i=> A i (b i))
   intro z; rw [show (⟨_,p⟩:Label G h)=0 from Subtype.ext (bag_empty z),map_zero]

-- finite coefficient prices. Useful even for Lens with no slots.
lemma charged {E U W:Type*}[AddCommGroup E][Module ℝ E][NormedAddCommGroup U][NormedSpace ℝ U][FiniteDimensional ℝ U][NormedAddCommGroup W][NormedSpace ℝ W] (f:E→ₗ[ℝ]U)(g:E→ₗ[ℝ]W)(p:∀ e:E,f e=0 → g e=0): ∃ C:ℝ,0≤C∧∀e, ‖g e‖ ≤ C*‖f e‖:= by
   let D:=LinearMap.range f
   choose u hu using LinearMap.surjective_rangeRestrict f
   have hr a b (e:f.rangeRestrict a=f.rangeRestrict b): g a=g b:=by
       apply sub_eq_zero.mp; rw [←map_sub]; apply p; rw [map_sub,sub_eq_zero]; exact congr_arg Subtype.val e
   let L: D→ₗ[ℝ] W:={
       toFun:= fun x=>g (u x)
       map_add':=fun x y=> (hr _ _ (by rw [map_add,hu,hu,hu])).trans (map_add g (u x) (u y))
       map_smul':=fun c x=> (hr _ _ (by rw [map_smul,hu,hu])).trans (map_smul g c (u x))}
   let H:=L.toContinuousLinearMap; exact ⟨‖H‖,norm_nonneg H,fun i=> by rw [hr i (u _) (Eq.symm (hu (f.rangeRestrict i)))]; exact H.le_opNorm _⟩
lemma market (k r:ℕ): ∃ C A:ℝ,0≤C∧0≤A∧∀ T:Glas G h r,Tensor.Sym T → seedTile T k∈localFields G h →
       ‖bagg G h r k T‖≤C*‖Bell F k r T‖ ∧ ‖Bell F k r T‖ ≤ A*‖bagg G h r k T‖:=by
   let P:= casting G h r k; let L:= (Bell F k r).toLinearMap.comp P.subtype; let M:= (bagg G h r k).comp P.subtype
   obtain ⟨C,hc,hp⟩:= charged L M (fun x=> (bell_floor F x.val x.property.1 x.property.2).mp)
   obtain ⟨A,ht,hf⟩:= charged M L (fun x=> (bell_floor F x.val x.property.1 x.property.2).mpr)
   exact ⟨C,A,hc,ht,fun T e p=> ⟨hp ⟨T,e,p⟩,hf ⟨T,e,p⟩⟩⟩
-- Cost on any tapped vector w.
lemma shines (b: Fin r→Fin (h-1))(A:Fin r→Snap G h): ∃ C:ℝ,0≤C∧ ∀ T:Glas G h r,Tensor.Sym T→seedTile T (Parts.rate b)∈ localFields G h →
       ‖latent T (fun i=>Pi.single (b i) (A i (b i)))‖ ≤ C*‖Bell F (Parts.rate b) r T‖:=by
   let k:= Parts.rate b; let X : Fin r→Snap G h:= fun i=> Pi.single (b i) (A i (b i)); let P:= casting G h r k; let f:= (Bell F k r).toLinearMap.comp P.subtype; let g:= (ContinuousMultilinearMap.apply ℝ (fun _:Fin r=>Lawn (Cart G h)) ℝ (casing G h ∘ X)).toLinearMap.comp P.subtype
   obtain ⟨C,hc,hf⟩:= charged f g fun x hx=>by
       have he:= bags_fill _ ((bell_floor F x.val x.property.1 x.property.2).mp hx) b rfl (fun i=> casing G h (A i))
       simp_rw [yarn,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at he; exact he
   exact ⟨C,hc, fun T e p=> hf ⟨T,e,p⟩⟩
-- one-sided price doesn't require seedTile accessible. Null tile does imply accessibility by zero. Even when pricing before mural proof.
lemma quarantine (k r:ℕ): ∃ A:ℝ,0≤ A∧∀ T:Glas G h r, ‖Bell F k r T‖ ≤ A * ‖bagg G h r k T‖:= by
    apply charged (bagg G h r k) (Bell F k r).toLinearMap; intro x hx; have he: seedTile x k=0:= bag_empty hx
    change Bell F k r x= _; have hv: seedTile x k∈localFields G h:= he.symm ▸ Submodule.zero_mem _; rw [detecting F x _ hv,show (⟨_,hv⟩:Label G h) = 0 from Subtype.ext he,map_zero]
end YM.WilsonCoeffUV.Cosmos
