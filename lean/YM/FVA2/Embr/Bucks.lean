import YM.FVA2.Embr.Poll
/-!
# Exponent branch calculation on the Fk epoch (preparation)
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth RGComparison.Core16
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {c f n:Side} {L:Fabric G n}

-- actual joint cost reading, full chosen-vector across levels.
def taxes {n:Side}(L:Fabric G n)(w:L.Cost→ℝ)(x:L.LinksOn)(t:Clan L):ℝ:= match L with
 | .endcap _ _=> 0
 | .layer S H b hf L=> w none * penalty S (show S.Choices×Clan L from t).1 ((layer S H b hf L).principal x) (L.principal (future S H b hf L x)) + taxes L (w∘some) (future S H b hf L x) (show S.Choices×Clan L from t).2
variable (L)
def spends (w:L.Accounts→ℝ)(x:L.LinksOn)(t:Clan L):= w none * wilson (L.principal x) + taxes L (w∘some) x t
lemma same_tax {n:Side}(L:Fabric G n): ∀ᶠ x in 𝓝 (1:L.LinksOn),∀ w t,taxes L w x t=L.installment w x:= by
 cases L with
 | endcap=> exact Filter.Eventually.of_forall fun x w t=> (zero_tax ..).symm
 | layer S H b hf L=>
   let T:=layer S H b hf L; filter_upwards [(T.principal_cont.tendsto 1).eventually (same_choice S H b),((future_cont S H b hf L).tendsto 1).eventually (same_tax L)] with x h he w t
   change S.Choices×Clan L at t; rw [tax_split,taxes, he]; unfold penalty; rw [show atStep S t.1 (T.principal x)=atStep S b (T.principal x) from funext fun i=> congr_fun (h _) i.val]
termination_by structural L
lemma impression : ∀ᶠ x in 𝓝 (1:L.LinksOn),∀ w t,spends L w x t=L.spend w x:= (same_tax L).mono (fun x h w t=> by unfold spends; rw [budget_sum, h])
lemma strength {n:Side} (L:Fabric G n)(g:Vertex n→G.El)(w:L.Cost→ℝ)(x:L.LinksOn)(t:Clan L): taxes L w (L.loom.spin g x) t=taxes L w x t:= by
 cases L with
 | endcap=> rfl
 | layer S H b hf L =>
   change S.Choices×Clan L at t; unfold taxes; rw [spin_main,spin_future, strength L, spin_main, show (g∘placement S.ratio) ∘track= (g∘ track) ∘ S.ratio.embed from funext (fun i=> congr_arg g (place_track ..)) ]; exact congr_arg₂ (· + ·) (congr_arg (w none * ·) (BlockGauge.motion S H t.1 _ _ _ (track_even g))) rfl
termination_by structural L
lemma moves (g:Vertex n→G.El)(w:L.Accounts→ℝ)(x:L.LinksOn)(t:Clan L) : spends L w (L.loom.spin g x) t=spends L w x t:= by unfold spends; rw [L.main_gauge,strength]
lemma counted {n:Side}(L:Fabric G n)(t:Clan L)(w:L.Cost→ℝ): Measurable (fun x=>taxes L w x t):= by
 cases L with
 | endcap=>exact measurable_const
 | layer S H b hf L=>
   let T:=layer S H b hf L; let p:S.Choices × Clan L:=t
   let V (x:T.LinksOn):= (T.principal x,L.principal (future S H b hf L x)); have hv : Measurable V:= T.principal_cont.measurable.prodMk (L.principal_cont.comp (future_cont S H b hf L)).measurable
   change Measurable (fun x:T.LinksOn=> w none * ((fun a=> penalty S p.1 a.1 a.2) ∘ V) x + taxes L (w∘some) (future S H b hf L x) p.2)
   exact (((measurable_penalty S H p.1).comp hv).const_mul (w none)).add ((counted L _ _).comp ((future_cont S H b hf L).measurable))
termination_by structural L
lemma spends_meas (w:L.Accounts→ℝ)(t:Clan L): Measurable (fun x=>spends L w x t):= ((L.price_clean none).const_mul (w none)).add (counted L _ _)

-- exact thermo bill with FULL weighted tagged mixture
lemma mixture_toll {n:Side}(L: Fabric G n)(w:L.Cost→ℝ)(x:L.LinksOn): ∑ t,poll L x t * Real.exp (-taxes L w x t)= L.thermostat w * Hearth.worlds L w x:= by
 cases L with
 | endcap=> change (∑ _:Unit,(1:ℝ)*_) = 1* (Hearth.worlds ..); erw [Fintype.sum_unique]; simp [taxes,Hearth.worlds]
 | layer S H t hf L=>
    change Option _→ℝ at w
    let A:= layer S H t hf L; let W:= A.principal x; let U:= future S H t hf L x; let f:S.Choices→ℝ:=fun s=>S.likelihood (Orb.liftLinks W) s; let Y:= L.principal U; let z:=zone (w none) _ _ G S
    let W₀:=w none; let v:L.Cost→ℝ:=fun i=>w (some i); let B(s:S.Choices):= f s* Real.exp (- W₀ * penalty S s W Y); let R(k:Clan L):= poll L U k*Real.exp (-taxes L v U k)
    change (∑ i:Clan A, poll A x i* Real.exp (-taxes A w x i))= _
    have hh(i:Clan A): poll A x i* Real.exp (-taxes A w x i)= B (show S.Choices×Clan L from i).1 * R (show S.Choices×Clan L from i).2:= by
      let k:S.Choices× Clan L:=i
      change f k.1*poll L U k.2 * Real.exp (-(W₀*penalty S k.1 W Y+ taxes L v U k.2))= B k.1* R k.2
      unfold B R; rw [neg_add,Real.exp_add,neg_mul]; ring
    have hp: ∑ i,B i=z * mixture S W Y W₀:= by
      unfold B f mixture noise; rw [mul_sum]; apply sum_congr rfl; intro i _; have he:0<z:= zone_pos S W₀; -- use ring equivalence
      change _= z*(_*(z⁻¹*_)); field_simp
    calc
     _ = (∑ i:S.Choices× Clan L, B i.1 * R i.2) := Finset.sum_congr rfl (fun i _=>hh i)
     _ = (z * mixture S W Y W₀) * (L.thermostat v * worlds L v U):= by rw [Fintype.sum_prod_type,← hp,← Embr.mixture_toll]; simp_rw [←mul_sum, ←sum_mul]; rfl
     _ = _ := by change _ = z* L.thermostat v*(mixture S W Y W₀ * worlds L v U); ring
termination_by structural L

lemma tribute (w:L.Accounts→ℝ)(x:L.LinksOn) :
    ∑ t,poll L x t* Real.exp (-spends L w x t)= Real.exp (- (w none * wilson (L.principal x))) * (L.thermostat (w∘some)* Hearth.worlds L (w∘some) x):= by rw [←mixture_toll]; unfold spends; rw [mul_sum]; exact sum_congr rfl fun i _=>by rw [neg_add,Real.exp_add]; ring
lemma squares (w:L.Accounts→ℝ)(x:L.LinksOn)(t:Clan L)(r:ℝ): spends L w x t / r=spends L (fun i=> w i/r) x t:= by
 unfold spends; rw [add_div, others L]; congr 1; all_goals first | rfl | ring_nf
where
 others {n:Side} (L:Fabric G n)(w:L.Cost→ℝ)(x:L.LinksOn)(t:Clan L): taxes L w x t / r=taxes L (fun i=> w i/r) x t:= by
    cases L with
    | endcap=> unfold taxes; simp
    | layer S H b hf L=> unfold taxes; rw [add_div,others]; apply congr_arg₂; ring_nf; rfl
 termination_by structural L
end YM.FVA2.Embr
