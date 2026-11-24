import YM.RegulatorIR.Binding.Blending

/-! Syntax of marginal Fubini. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {I J E L:Type}[Fintype E][Fintype I][Fintype J][Fintype L]
variable {F A:Hook G E I}{Z: Hook G L J}{P:Viewport G I}{Q:Viewport G J}{V:Transfer I L G}
variable (H:Stead P F)(N:Move P Q V Z)(B:Tune A)

lemma bean_split (E L:Type)[Fintype E][Fintype L](G:Gauge): MeasurePreserving (beanK E L G) (physical G _) ((physical G E).prod (physical G L)):=measurePreserving_sumPiEquivProdPi (_m:=fun _: E⊕L=>G.elMeasurableSpace) (fun _=>G.probHaar)
lemma spun_dart (E L:Type)[Fintype E][Fintype L](G:Gauge): MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _:E⊕L=>G.Color)) (tangent G _) ((tangent G E).prod (tangent G L)):= measurePreserving_sumPiEquivProdPi (fun _:E⊕L=>volume (α:=G.Color))
lemma order_sums (G:Gauge)(E L:Type)[Fintype E][Fintype L]: Laplace.dim G (E⊕L)= Laplace.dim G E+Laplace.dim G L:=by rw [Laplace.dim,(dart E L G).finrank_eq,Module.finrank_prod]; rfl

include H N B
lemma puzzling (t:ℝ)(u:RoomK G J): scan (fuse V F Z) (blade J V A) t u=
  ∫ z,scan F A t (V.inlet z) * tilt Z 1 t u z ∂(physical G L):=by
 let G' := fuse V F Z; let A':= blade J V A
 let P:= beanK E L G
 have he:= bean_split E L G
 have h: Integrable (fun x=>tilt G' A' t u (P.symm x)) ((physical G E).prod (physical G L)):= (he.symm.integrable_comp_emb P.symm.measurableEmbedding).mpr (((H.integrates N).allows (blade_c _ B)).reading t u)
 change (∫ z, tilt G' A' t u z ∂physical G (E⊕L))=_
 rw [← he.symm.integral_comp' (tilt G' A' t u), show _= ∫ z, (∫ y,tilt G' A' t u (P.symm (y,z)) ∂physical G E) ∂physical G L from integral_prod_symm _ h]
 apply integral_congr_ae; filter_upwards with z; rw [scan, ← integral_mul_const]; refine integral_congr_ae (Eventually.of_forall (fun y=>?_))
 unfold tilt G' A' fuse blade; dsimp only; rw [show trestle (P.symm (y,z))=(y,z) from P.apply_symm_apply _]; rw [Pi.one_apply,Pi.one_apply,Pi.one_apply,one_mul,neg_add,add_div, Real.exp_add]; ring

-- Exact coefficient rule. Test parameter not integrated. Prove equality by point Taylor uniqueness before Gaussian integration. No convexity bound on Z used after dividing by its quadratic (Z may entirely vanish at terminal).
omit H N B in
lemma aspFixed {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X] {F A : X→ℝ}(F':Stationary F)(a:ContDiffAt ℝ ∞ A 0)(x:X) : Aspiration (fun t:ℝ=>projection A F t x) (fun i=>normTerm A F i x):= by
 let v := Radial.zone (E:=X); let w:= v.w x
 have hw:0 < w:=lt_of_lt_of_le zero_lt_one (v.high _)
 intro i
 obtain ⟨d,c,p,hd,hc,h⟩:= ((integrand a F' (show (0:ℝ)<1 from zero_lt_one)).fits i).cost
 let C:= c*w^p*Series.Radial.shade 1 x
 have hC: 0 ≤ C:= by dsimp only [C,Series.Radial.shade]; positivity
 refine ⟨C*kernel F x, mul_nonneg hC kernel_pos.le,?_⟩; filter_upwards [Tested.eventually_small (div_pos hd hw)] with t ht
 have hm:t*w ≤ d:= ((lt_div_iff₀ hw).mp ht.2).le; have hx:=h x t ht.1 hm
 rw [Pi.sub_apply];change ‖projection _ _ _ _-_‖≤_
 rw [show peval (fun j=>normTerm A F j x) i t=Zone.eval (integrandSeries F A) i t x * kernel F x from ?_,projection,← sub_mul,norm_mul,Real.norm_of_nonneg kernel_pos.le]
 exact le_trans (mul_le_mul_of_nonneg_right hx kernel_pos.le) (le_of_eq (mul_right_comm ..))
 unfold peval Zone.eval;rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _=>by rw [smul_mul_assoc]; rfl
private lemma Hp (x:Meadow G L × ℝ × Meadow G J)(u:Meadow G E) :
 (fun k=>normTerm (aura (blade J V A)) (priceMap (fuse V F Z)) k ((dart E L G).symm (u,x.1),x.2))=conv (fun j=>normTerm (aura A) (priceMap F) j (u,x.2.1,V.curve x.1)) (fun i=>normTerm (aura (1:Hook G L J)) (priceMap Z) i x):=by
 let w:= ((dart E L G).symm (u,x.1),x.2); let g:=fuse V F Z;let z:= (aura (blade J V A)); let V':= (u,x.2.1,V.curve x.1); let K:=aura (1:Hook G L J)
 have hj:ContDiffAt ℝ ∞ K 0:=by
    apply ContDiffAt.mul (contDiffAt_const (c:=(1:ℝ))); exact (Chart.Ratio.jacobian_smooth (Orb.traySpec G)).of_le le_top|>.comp (f:=Prod.fst) (0:Angle L J G) contDiffAt_fst
 have he:= ((H.integrates N).allows (blade_c (V:=V) J B)).entry
 have hb:= aspFixed he.station he.fine w; have hv:= (aspFixed H.localK (H.allows B).entry.fine V').prod (aspFixed (F:=priceMap Z) N.localK hj x)
 apply hb.unique; convert hv using 1 <;> try rfl
 ext1 t
 rw [Pi.mul_apply]; simp_rw [projection_eq]
 have hf(p : Angle (E⊕L) J G) : priceMap g p= priceMap F (drawUp V p)+priceMap Z (front J L E G p) := congr_arg (· +priceMap Z (front J L E G p)) (blade_map (V:=V) (F:=F) p)
 have hh : drawUp V w= V':= by apply Prod.ext; change ((dart E L G) w.1).1=u; exact congr_arg Prod.fst ((dart E L G).apply_symm_apply (u,x.1)); change (x.2.1,V.curve ((dart E L G) w.1).2) = V'.2; exact Prod.ext rfl (congr_arg V.curve (congr_arg Prod.snd ((dart E L G).apply_symm_apply (u,x.1))))
 have ht:front J L E G w=x:= by apply Prod.ext;change ((dart E L G) w.1).2=x.1; exact congr_arg Prod.snd ((dart E L G).apply_symm_apply (u,x.1)); rfl
 have hq:z (t • w) = aura A (t • V') * K (t • x):=by
    unfold z aura; rw [blade_map,map_smul,hh]; unfold K aura
    have hK: Chart.jacobian (Orb.tray G) (t • w.1) = Chart.jacobian (Orb.tray G) (t • V'.1)*Chart.jacobian (Orb.tray G) (t • x.1):=by
       unfold Chart.jacobian; rw [Fintype.prod_sum_type]; rfl
    change _*Chart.jacobian (Orb.tray G) (t • w.1)=_*(1*Chart.jacobian (Orb.tray G) (t • x.1)); rw [hK,one_mul,mul_assoc];rfl
 change z _ * Real.exp (-priceMap g _/_)= _; rw [hf (t • w),map_smul,map_smul,hh,ht,hq];rw [neg_add,add_div, Real.exp_add];unfold K; ring

lemma heard (y: Meadow G J) (e:ℕ): tomorrow (fuse V F Z) (blade J V A) y e =
 ∫ x:Meadow G L, conv (tomorrow F A (V.curve x)) (fun i=>normTerm (aura (1:Hook G L J)) (priceMap Z) i (x,1,y)) e ∂tangent G L:=by
 let B':=aura (blade J V A);let K:= priceMap (fuse V F Z);let U (z:Meadow G (E⊕L)):= normTerm B' K e (z,1,y)
 let f:=dart E L G;let P:=MeasurableEquiv.sumPiEquivProdPi (fun _:E⊕L=>G.Color)
 have he := spun_dart E L G
 have hh: Integrable U (tangent G (E⊕L)):= ((H.integrates N).allows (blade_c (V:=V) J B)).entry.protects _ e (1,y)
 have ht: Integrable (fun x=>U (f.symm x)) ((tangent G E).prod (tangent G L)):= (he.symm.integrable_comp_emb P.symm.measurableEmbedding).mpr hh
 change (∫ z,U z ∂tangent G (E⊕L))=_
 rw [← he.symm.integral_comp' U]; change (∫ x,U (f.symm x) ∂ ((tangent G E).prod (tangent G L)))=_; rw [integral_prod_symm _ ht]
 apply integral_congr_ae;filter_upwards with x
 let X(i z):= normTerm (aura A) (priceMap F) i (z,1,V.curve x); let Y i:=normTerm (aura (1:Hook G L J)) (priceMap Z) i (x,1,y)
 have hX i: Integrable (X i) (tangent G E):= (H.allows B).entry.protects _ _ (1,V.curve x)
 have hz(z:Meadow G E) : U (f.symm (z,x))=conv (fun i=>X i z) Y e:=congr_fun (Hp H N B (x,1,y) z) e
 change (∫ z,U (f.symm (z,x)) ∂tangent G E) = _
 simp_rw [hz,conv,Tested.term, PowerSeries.coeff_mul,PowerSeries.coeff_mk]
 rw [integral_finsetSum _ (fun i _=>(hX i.1).mul_const (Y i.2))]; apply Finset.sum_congr rfl; intro i _;rw [integral_mul_const];rfl
end YM.RegulatorIR.Binding
