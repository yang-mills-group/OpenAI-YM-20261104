import YM.FormalOPE.RG10.BlockGauge.Cascade
/-!
 # canonical kernel cost in independent variables (true nonpolynomial at this stage)

 top truss can evaluate this way. More general trusses using inheritance; still need Hessian proofs.
 All couplings positive when using stationary point; study exponents for real g; pass to re-expression
 at fixed order. Same tags when using scheme likelihood. No actual period identification.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
namespace Fabric
variable (L : Fabric G n)(u:LinkFrame G n)
 def now (G:Gauge)(n:Side):= Chart.physical G (OEdge n)
abbrev always := Chart.physical G L.Path
abbrev later := Chart.physical G L.More
instance : IsProbabilityMeasure (now G n):= by unfold now; infer_instance
 def spread : L.LinksOn ≃ᵐ (LinkFrame G n×L.Clouds) := MeasurableEquiv.sumPiEquivProdPi _
lemma spread_packs : MeasurePreserving L.spread.symm ((now G n).prod L.later) L.always := measurePreserving_sumPiEquivProdPi_symm (fun _=> G.probHaar)
lemma spread_pres : MeasurePreserving L.spread L.always ((now G n).prod L.later):= by convert L.spread_packs.symm; rfl
lemma spread_eq (u:L.LinksOn) : L.spread u=(L.principal u,L.runoff u):=rfl
lemma symm_eq (u : LinkFrame G n)(e:L.Clouds) : L.spread.symm (u,e)=L.combine u e:= rfl
lemma mist {n:Side}(L:Fabric G n)(u:LinkFrame G n) : MeasurePreserving (L.drizzle u) L.later L.later:= by
 cases L with
 | endcap => exact MeasurePreserving.id _
 | @layer c _ S H t hf L =>
   let k:= (atStep S t u)⁻¹
   let f : LinkFrame G c→ _ := (· * k)
   let Q:= L.spread.symm ∘ (fun x=> (f x.1,L.dry x.1 x.2)) ∘ ⇑L.spread
   have hu : MeasurePreserving f (now G c) (now G c):= measurePreserving_pi _ _ (fun i=> measurePreserving_mul_right _ (k i))
   have hp : MeasurePreserving Q L.always L.always:= L.spread_packs.comp ((hu.skew_product L.leftMeas (Filter.Eventually.of_forall fun i=> (mist L i).map_eq)).comp L.spread_pres)
   let D:=layer S H t hf L
   -- More iMore is computed via recursion.W.Helpers Need type cast harmony.
   change MeasurePreserving (D.dry u) D.later D.later
   exact hp
termination_by structural L
lemma mist_rain : MeasurePreserving ((L.drizzle u).symm) L.later L.later:= (L.mist u).symm

 def air {n}(L:Fabric G n)(e:L.Clouds) : L.Cost→ℝ:= match L with
 | .endcap _ _=> Empty.elim
 | .layer S _ _ _ L=> fun (i:Option L.Cost)=> i.elim (distance S (L.principal e)) (air L (L.runoff e))
lemma costs {n}(L:Fabric G n)(i:L.Cost)(u:LinkFrame G n) (e:L.Clouds): L.regional (L.combine u e) i=L.air (L.dry u e) i:= by
 cases L with
 | endcap => exact Empty.elim i
 | layer S B t hf L=>
   let y:= L.principal e
   let w:= L.runoff e
   change Option _ at i
   cases i with
   | none =>
     rw [dry_eq]
     rfl
   | some i =>
     rw [dry_eq]; -- combine definal reduces enough.
     change L.regional e i=L.air (L.dry (L.principal e) (L.runoff e)) i
     conv_lhs => rw [← L.comb_principal e]
     exact costs L i _ _
termination_by structural L
lemma areal {n}(L: Fabric G n) (i:L.Cost): Continuous (fun u=> L.air u i):= by
 cases L with
 | endcap=> exact Empty.elim i
 | layer S B t hf L =>
   change Option _ at i; cases i with
   | some i=> exact (areal L i).comp (L.runoff_cont)
   | none => change Continuous ((distance S) ∘ L.principal); apply Continuous.comp _ (L.principal_cont); unfold distance; fun_prop
termination_by structural L
end Fabric
end YM.FormalOPE.RG10.BlockGauge
