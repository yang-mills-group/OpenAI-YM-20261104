import YM.FVAAlt2.Boot.Start
/-! # Packet stencil products from actual section. includes empty region, raw strut stencils & k-degrees (multi power). -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Boot
open Function Finset Filter Set MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Spatial Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Source Labels Halo
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries PhysicalNext.Repeat.Legato Run
open Kick Rocket YM.FVAAlt2 Orb.SlotEvaluation Lodge
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {I X:Type} [LinearOrder I] (R:Run G) (s:Finset I) (k:I→ℕ)(v:(i:I)→ (R.family.labels.level (k i)).Index) (z:I→ Cover) {f:Side}
local notation "B"=> Lodge.basisR R
local notation "V!"=> topPortrait B s k v z
local notation "M"=> depthF s k v
local notation:max "O_" j:max=> (R.family.localSection (k j))
lemma covers (p:Side)(U:Config G p)(t:ℝ): topMark B s k v p z U=(topPortrait (B) s k v z t (U ∘ Geometry.around p)):= by
    have h(x:Cover): Lattice.translate x (U ∘ Geometry.around p) = Lattice.expandAt (wrap p x) U:= by ext1 i; change U (wrap p (i.1+x),i.2)= U (_,i.2); rw [map_add]
    unfold topMark topPortrait; simp_rw [Finset.prod_apply]; refine prod_congr rfl (fun i hi=>?_); unfold Halo.convey; rw [h]; rfl
lemma setup (j:I): let g:= wrap f (z j); (Complex.ofReal ∘ fieldAt (O_ j) (v j) g)=(O_ j).places (Pi.single (v j) 1) g :=by intro g; exact funext fun U=> scalar_real (R.makes.sections _)
lemma combined (f:Side): (Complex.ofReal ∘ ( topMark B s k v f z ))=∏ i∈s,(O_ i).places (Pi.single (v i) 1) (wrap f (z i)):=by ext1 U; unfold topMark; simp_rw [Finset.prod_apply,← setup R k v z]; simp [Function.comp_apply]; rfl
section
lemma packaged {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{u:I→X→ℂ}{m:I→ℕ} (h:∀i,Assembly.GradeAt (m i) (u i)) : Assembly.GradeAt (∑ i∈s,m i) (∏ i∈s, u i):=by
    induction s using Finset.induction_on with
    | empty=> rw [Finset.prod_empty,Finset.sum_empty]; exact Assembly.GradeAt.unchecked contDiffAt_const
    | insert i s h' ih=> rw [Finset.prod_insert h',Finset.sum_insert h']; exact (h i).mul ih
end
lemma primed (f:Side) : Assembly.GradeAt M (Bulk.projected fun _ U=> (↑( topMark (B) s k v f z U ):ℂ)):=by
   let W i:= (O_ i).places (Pi.single (v i) 1) (wrap f (z i))
   have he : Bulk.projected (fun _ U=> (↑(topMark B s k v f z U):ℂ))= ∏ i∈s, Bulk.projected fun (_:ℝ)=> W i:= by ext1 x; rw [Finset.prod_apply]; change (Complex.ofReal ∘ ( topMark B s k v f z )) _=_; rw [combined,Finset.prod_apply];rfl
   rw [he]; exact packaged s fun i=> Assembly.GradeAt.coarse (g:=(Prod.snd:ℝ×fieldDir G f 1→_)) (Bare.Signals.primary (C:=R.family) (v i) ( YM.FVAAlt2.Block.clothes R _ ) (wrap f (z i))) contDiffAt_snd rfl
lemma respects (f:Side): GaugeInvariant (topMark B s k v f z):=by
    intro t U; apply Complex.ofReal_injective; have h:= combined R s k v z f; rw [ show ( Complex.ofReal (topMark B s k v f z ( Lattice.gauge t U)))=_ from congr_fun h _, show ( Complex.ofReal (topMark B s k v f z U))=_ from congr_fun h _,Finset.prod_apply, Finset.prod_apply]; exact prod_congr rfl (fun i _=> (O_ i).placed_invariant (R.makes.sections _) _ _ t U)
lemma opened (f:Side): Continuous (topMark B s k v f z):= by
    have h: Continuous ( Complex.ofReal ∘ ( topMark B s k v f z ) ):= by rw [combined,_root_.funext (fun x=>Finset.prod_apply x s (fun i=> (O_ i).places (Pi.single (v i) 1) (wrap f (z i))))]; exact continuous_finsetProd _ fun i _=> (O_ i).continuous_places _ _ -- syntax
    exact Complex.continuous_re.comp h

def scout : Boot.Scout (G:=G) M:={
    body:= topPortrait B s k v z
    Vt:=fun f=> topMark B s k v f z
    gear:= kickStart B s k v z
    sight:= (kickLaw B s k v z).1
    ranks:= (kickLaw B s k v z).2
    expose:= covers R s k v z
    prepared:= primed R s k v z
    rooted:= respects R s k v z
    payment:= opened R s k v z }
-- straightforward formulas model.Kraft.R.Stock.P.External normalization.Y.Scalar.H

end YM.RegulatorIR.FVAAlt2.Boot
