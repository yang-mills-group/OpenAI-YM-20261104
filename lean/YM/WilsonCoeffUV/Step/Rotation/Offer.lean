import YM.WilsonCoeffUV.Step.Rotation.Turn
import YM.WilsonCoeffUV.VacuumLaw
import YM.WilsonCoeffUV.Product.I.Evaluated
/-!
# Port supplement: interchange of the auxiliary forest on torus W samplers.
For invariant stencil calls only. No change assertions on individual free
response kernels, or estimates with different protections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Fk
open Matrix Function Lattice FreeResolvent Metric RG Wilson Tree Precision Gauge
open Mer Bank Bank.Bloom Blue Power PowerSeries
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{A:Levels G}{m N:ℕ}{Ñ:ChartRatio G}
section dual
variable {c f:Side} {S:StepData c f}{F T:Forest S.ratio} {K:FaceRow} {Q:Matrix (Exterior.Body 1 f) (Exterior.Body 1 c) ℝ}{k:ℕ}{P:PChart G f}
-- any dual already works in applications; transport does not choose positivity quotient basis.
lemma carry_joint {V:Type*} [NormedAddCommGroup V][NormedSpace ℝ V] (R:Parcelized V G f)(ha:shellK k R)(hx:∀ i,Pure (R i)) (w:Cert R)
    (e:∀ A:PChart G f,shellK k A→(∀ i,Pure (A i)) → rollTest (flash A) (flash A) 1 0→ reed S F K Q Ñ P k A=reed S T K Q Ñ P k A):
    reed S F K Q Ñ P k R=reed S T K Q Ñ P k R := by
  ext i j u; apply (SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)).mpr; intro L
  have he (F:Forest S.ratio): reed S F K Q Ñ P k (ply L.toLinearMap R)=ply L.toLinearMap (reed S F K Q Ñ P k R):= (reed_maps S F K Q k L.toLinearMap).symm
  have ht:=e (ply L.toLinearMap R) (ply_shell _ ha) (fun i=> ply_pure _ (hx i)) (w L.toLinearMap)
  rw [he F,he T] at ht; exact congr_arg (fun x:PChart G c=> x i j u) ht
end dual

theorem allForests {V: Type*}[NormedAddCommGroup V][NormedSpace ℝ V](p:G.Simple)(h:LocalRatio Ñ)(v:m<N)(n : Side) (T: Forest (mStep A n m).ratio) :
    let S:=mStep A n m
    let Q:=roam A N m n
    let H:=freeForms A N (m+1)
    let Y:=freeForms A N m
    let P:= (story A Ñ N (m+1)).1 (n*(loose A m).L)
    let D:= unripe A Ñ N m (story A Ñ N (m+1)).1 n
    Fintype.card (repeatF S).Free=Fintype.card T.Free ∧
    (treeMatrix G S (repeatF S) H).det=(treeMatrix G S T H).det ∧
    (treeMatrix G S T H).PosDef ∧ D=winter S T H Y Q Ñ P ∧
    (shot S T Q Ñ P=loom (camSlice G S T (extractV G S T Q)) (jet (unhaar Ñ))-unscaled S T Q P+(holdUp (Active G T) (orbC (precisionC G n Y))+bodyQ (Woods G n) (treeMatrix G S T H))) ∧
    residualUnmarked Y D * (soil (ζ Ñ S.kernel.penalty))^(Fintype.card (Edge (Site n)))=inside S T H Q Ñ P ∧
    ∀ (k:ℕ)(A:Parcelized V G (n*(loose A m).L)),shellK k A→ (∀ i,Pure (A i)) → Cert A →
       reed S (repeatF S) H Q Ñ P k A=reed S T H Q Ñ P k A:=by
  intro S Q H Y P D
  have he:= (finite_sampler (A:=A) p h v n).prescription
  dsimp only at he
  let L:= (loose A m).L
  let F:=repeatF S
  obtain ⟨hs,hx,_,hy,_⟩:=he
  have hu:S.patch.Branches S.kernel G:= (A.blocks m 0).branches
  have hw:= horizon_step A m N v n (n*L) rfl
  have hb:= age_sym A N (m+1) (n*L)
  obtain ⟨ha,hv,ht⟩:= Power.Freedom.allegiance S F T H Y Q (P:=P) hu hw hb h hs hy
  have hn := (Matrix.isUnit_iff_isUnit_det _).mp hy.isUnit
  have hL:D=winter S T H Y Q Ñ P:= hx.trans (Power.Freedom.winter_neutral S F T H Y Q hu hw hb h hs hn (age_sym A N m n))
  refine ⟨ha,hv,ht,hL,shot_bill S T _ _ _ hs.lamp hs.stem hu hw hb, ?_,?_⟩
  · rw [hL]; apply log_output S _ _ _ _ _ h hs hu hb
  intro k B p' u w; exact carry_joint B p' u w (fun A=> Power.Freedom.reed_neutral S F T _ _ _ hu hw hb h hs hn A k)
end YM.WilsonCoeffUV.Fk
