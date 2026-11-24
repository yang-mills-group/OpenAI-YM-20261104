import YM.Contacts.Lintel.Rafter
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
variable {V X Y E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
   [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {t:E} {a b:E→ ℝ}
namespace Crag
open Wire
section beam
variable {k:Lattice.Ratio c f}{F:Forest k}
open Next.SectorChange Gaussian
local notation "κ" => AxisChart G F
variable (V:Matrix (Key F G) (Key F G) ℝ)
-- bridge Counting with Thermal.Form.Bench
lemma count_axis (F:Forest k)(G: Gauge)(x: (AxisChart G F))(i:Key F G) : (countingBasis F G).equivFun x i=tape.symm x i:= by simp only [Module.Basis.equivFun_apply]; rcases i with ⟨x,i⟩; simp [countingBasis]; rfl
lemma count_form {P:(AxisChart G F)→ℝ}{x:(AxisChart G F)} (U:(AxisChart G F)): iteratedFDeriv ℝ 2 P x (fun _=>U)= tape.symm U ⬝ᵥ ((LinearMap.toMatrix₂ (countingBasis F G) (countingBasis F G) (bend P x))*ᵥ tape.symm U):= by
   rw [show tape.symm U=(countingBasis F G).equivFun U from funext fun i=> (count_axis F G ..).symm]; let b:=countingBasis F G; have hh := apply_eq_dotProduct_toMatrix₂_mulVec b b (bend P x) U U; exact (show _=bend P x U U from (by rw [Work.F05.bend_apply, show ![U,U]=(fun _:Fin 2=>U) from funext (fun i=>by fin_cases i<;>rfl)])).trans hh
lemma stamp_count (h:V.PosDef){M:(AxisChart G F)→ℝ} (hM:∀ x,M x= Real.exp (- (tape.symm x ⬝ᵥ (V*ᵥ tape.symm x))/2)) : Integrable M (tangent G (F).Free) ∧ (∫ x,M x ∂tangent G F.Free)= dome (Key F G) * Real.exp (-Real.log V.det/2):= by
   obtain ⟨hf,hp⟩:= under_cloud h.inv (M ∘ tape); let M' : Prices G F.Free →ℝ := M ∘ tape; set C:= coat V⁻¹; have he : (fun x=> Real.exp (force V⁻¹ x/2) • M' x)=(fun _=>1):=by
       funext x; unfold M'; simp only [Function.comp_apply,hM,MeasurableEquiv.symm_apply_apply,Gaussian.force, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _|>.1 h.isUnit),smul_eq_mul, ← Real.exp_add]; rw [neg_div, add_neg_cancel,Real.exp_zero]
   have ht:= tape_volume (ι:=F.Free) (G:=G); refine ⟨(ht.integrable_comp_emb tape.measurableEmbedding).1 ?_,?_⟩
   · apply hf.mpr; change Integrable _ _; rw [he]; exact integrable_const _
   rw [show tangent G F.Free=MeasureTheory.volume from rfl, ← ht.integral_comp' M]; change (∫ x,M' x)= _; erw [hp,he]; simp only [integral_const, probReal_univ,smul_eq_mul,mul_one]; unfold C coat; congr 1; rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv, Real.sqrt_inv,neg_div,show Real.log V.det/2=Real.log (Real.sqrt V.det) from (Real.log_sqrt h.det_pos.le).symm,Real.exp_neg,Real.exp_log (Real.sqrt_pos.mpr h.det_pos)] -- rewrite neg_div

variable [MeasurableSpace E][BorelSpace E]
variable {S:E×AxisChart G F→ℝ}{t:E}{d:ℝ}
def bunch (F:Forest k)(G:Gauge)(S:E×AxisChart G F→ℝ) (x:E) := LinearMap.toMatrix₂ (countingBasis F G) (countingBasis F G) (bend (fun y=> S (x,y)) 0)
lemma radial_yes (S:E×AxisChart G F→ ℝ)(x:E)(v:AxisChart G F): radial S (x,v)= (tape.symm v ⬝ᵥ (bunch F G S x*ᵥ tape.symm v))/2 := by unfold radial jet; rw [count_form (F:=F)]; unfold bunch; norm_num; ring
lemma ok_mx (he:∀ v : AxisChart G F,d*‖v‖^2 ≤ radial S (t,v)) (hp:0<d)(h:AnalyticAt ℝ S (t,0)): (bunch F G S t).PosDef:= by
   have ht : AnalyticAt ℝ (fun y => S (t,y)) (0:AxisChart G F) := ContDiffAt.analyticAt (ContDiffAt.comp _ h.contDiffAt (contDiffAt_const.prodMk contDiffAt_id)); apply Matrix.PosDef.of_dotProduct_mulVec_pos; · ext i j; change star ((bunch F G S t) j i)=_; simp only [star_trivial,bunch,LinearMap.toMatrix₂_apply]; exact ht.contDiffAt.isSymmSndFDerivAt_of_omega .. -- implicit
   intro u hu; rw [star_trivial]; let v:= (tape (G:=G) (ι:=F.Free)) u; have hv: tape.symm v=u:= MeasurableEquiv.symm_apply_apply ..; have hi :0 < ‖v‖ := by
      apply norm_pos_iff.mpr; change colors u ≠0; exact (colors (G:=G) (ι:=F.Free)).map_ne_zero_iff.mpr hu
   have hx := he v; rw [radial_yes _ t v,hv] at hx; linarith only [hx,mul_pos hp (pow_pos hi 2)]
instance : (tangent G F.Free).IsNegInvariant := ⟨(measurePreserving_pi _ _ (fun _ : F.Free=> Measure.measurePreserving_neg (MeasureTheory.volume:Measure G.Color))).map_eq⟩
lemma breath_pay {c':ℝ} (hc:0<c')(hi :∀ v: AxisChart G F,c'*‖v‖^2 ≤ radial S ((0:E),v))(h:AnalyticAt ℝ S 0): ∀ᶠ x:E in 𝓝 0,(bunch F G S x).PosDef ∧ ∫ y, Real.exp (-radial S (x,y)) ∂tangent G F.Free=dome (Key F G)*Real.exp (-Real.log (bunch F G S x).det/2):= by
    obtain ⟨d,hd,H⟩:= based_bent hc h hi; filter_upwards [H,(show Tendsto (fun x:E=>(x,(0:AxisChart G F))) (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually h.eventually_analyticAt] with x hx he; let Q:= bunch F G S x; have hQ:Q.PosDef:=ok_mx hx hd he; exact ⟨hQ,(stamp_count Q hQ (M:=fun y=> Real.exp (-radial S (x,y))) (fun y=>by rw [radial_yes,← neg_div])).2⟩ -- parenth
end beam
end Crag
end
end YM.Contacts.Lintel
