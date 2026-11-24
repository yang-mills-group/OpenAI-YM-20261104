import YM.OPE.Compatible.Glim.Heth
/-! # divergence identity -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (L:Law E)
lemma Prow (p:ScriptJ E)(u:I→E)(Y:I→ScriptJ E)(H:Finset I)(hp:p.B):
     Flux u Y H (wheel p)= -(wheel p)*(Flux u Y H p-∑ i∈H,Y i *spur (Pry (u i) p)):=by unfold Flux; simp_rw [PryWheel _ _ hp]; rw [← sum_sub_distrib, Finset.mul_sum]; apply sum_congr rfl;intro i _;ring
lemma portX (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(p:E→ℝ)(hp:ContDiffAt ℝ ω p 0):
     let W:=Real.exp ∘ fun x=>-p x
     Flux u Y H (Pawn.mold W 0)= -Pawn.mold W 0 * Flux u Y H (Pawn.mold p 0):=by intro W; unfold Flux W; simp_rw [pokeExp _ p hp]; rw [mul_sum]; apply sum_congr rfl; intro i _;ring
omit [FiniteDimensional ℝ E] in lemma pureFlux (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(v:Token): Flux u Y H (fun _=>v)=0:=by unfold Flux; simp_rw [pryC,mul_zero];simp
-- fee.Ha stability
noncomputable abbrev Wax (w F J:E→ℝ):= Pawn.mold J 0* Pawn.mold (Real.exp ∘ fun x=>-F x) 0 * wheel (Pawn.mold w 2)
lemma stampB(w f j:E→ℝ):ScriptJ.B (Wax w f j):= height (height (tallJ _ _) (tallJ _ _)) (heightens _ (tallJ _ _))
lemma boltP (f:E→ℝ)(z:E)(h:∀ x,jet f 2 x=L.P x x/2): spur (Pry z (Pawn.mold f 2))= link L z:=by
     funext x; apply eta; · change fderiv ℝ (jet f 2) x z=L.P z x; rw [funext h]; exact billing L x z
     · rfl
     rfl
noncomputable abbrev BookW (p:E→ℝ)(f:E→ℝ): ScriptJ E:= Pawn.mold p 2+Pawn.mold f 0
lemma bud (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(p F J:E→ℝ)(c:Token)(hf:ContDiffAt ℝ ω F 0)(h:∀ x,jet p 2 x=L.P x x/2)(hp':divergence u Y H * Pawn.mold J 0+ Flux u Y H (Pawn.mold J 0)=0):
    let W:=(fun _:E=>c)*Wax p F J
    let R:= BookW p F
    Flux u Y H W+ W*Flux u Y H R = W*((∑ i∈H, Y i*link L (u i))-divergence u Y H):=by -- symbolic
         intro W R; let g:= Pawn.mold J 0; let f:=Pawn.mold (Real.exp ∘ fun x=>-F x) 0; let C:E→Token:=fun _=>c; let q:=Wax p F J; let w:=wheel (Pawn.mold p 2); have hw:ScriptJ.B w:=heightens _ (tallJ _ _); have ht:g*f*w=q:=rfl
         have hz := plyFlux u Y H (g*f) w (height (tallJ _ _) (tallJ _ _)) hw; rw [ht, plyFlux u Y H g f (tallJ _ _) (tallJ _ _)] at hz; rw [show Flux u Y H w= _ from Prow _ u Y H (tallJ _ _), show Flux u Y H f= _ from portX _ _ _ _ hf] at hz; simp_rw [boltP L p _ h] at hz; unfold W; rw [plyFlux u Y H (p:=fun (_:E)=>c) _ (Bfray _) (stampB p F J), pureFlux, zero_mul, add_zero, show Flux u Y H _=_ from hz]; erw [plyAdd u Y H (Pawn.mold p 2) (Pawn.mold F 0) (tallJ _ _) (tallJ _ _)]
         rw [show Flux u Y H g= -(divergence u Y H*g) from eq_neg_of_add_eq_zero_right hp']; unfold Wax f w g; ring -- ring interop
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
lemma sumPry (H:Finset I)(x:I→ScriptJ E)(h:∀ i∈H,(x i).B): draw (∑ i∈H,x i) L μ=∑ i∈H,draw (x i) L μ:=by induction H using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; exact eta _ _ (by exact Flock.singleConst ..) (by exact Flock.singleConst ..) (by exact Flock.singleConst ..)
    | insert i H hi ih=>rw [sum_insert hi,sum_insert hi,duoS _ _ _ _ (h i (mem_insert_self ..)) (sumBat _ _ (fun i hi=> h _ (mem_insert_of_mem hi))), ih (fun i hi=>h _ (mem_insert_of_mem hi))]
noncomputable abbrev indexQ (u:I→E)(Y:I→ScriptJ E)(H:Finset I):= ∑ i∈H,Y i*link L (u i)
lemma Ein (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(h:∀ i∈H,(Y i).B)(p:ScriptJ E)(hp:p.B): draw (Flux u Y H p+divergence u Y H*p) L μ= draw (p * indexQ L u Y H) L μ:=by
    let qJ:=∑ i∈H,Pry (u i) (p*Y i); have he:Flux u Y H p+divergence u Y H*p=qJ:=by
         unfold Flux divergence qJ; rw [sum_mul,← sum_add_distrib]; apply sum_congr rfl;intro i hi; rw[pryMul _ _ _ hp (h _ hi)]; ring
    rw [he]; unfold qJ indexQ; erw [mul_sum,sumPry _ _ _ _ (fun i hi=>pryB _ _ (height hp (h _ hi))),sumPry _ _ _ _ (fun i hi=>height hp (height (h i hi) (lower (Bond.glyph (L.P (u i))))))]; apply sum_congr rfl; intro i hi; rw [purge _ _ _ _ (height hp (h _ hi))]; rw [show link L (u i)*(p*Y i)=p*(Y i*link L (u i)) by ring];rfl
end YM.OPE.Variance
