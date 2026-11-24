import YM.MSbar.Pole.Feynman.PlaneFlow

/-! # Four-dimensional plane value after subtraction, includes momentum projection

This DOES NOT discard evanescent operators prior to taking poles.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin Piece Sew Thread Symbol PoleVal
open scoped Topology ContDiff BigOperators Classical Interval Real
variable {I : Type} [Fintype I]
namespace PoleVal
lemma sumValues {F G:ℂ→Cloud I} (h:Vortex 0 F)(p:Vortex 0 G): pay (F+G)=pay F+pay G:= paid fun n x=> (ends h n x).add (ends p n x)
lemma product {F G:ℂ→Cloud I} (h:Vortex 0 F)(p:Vortex 0 G): pay (F*G)=pay F*pay G:= paid fun n x=> (ends h n x).mul (ends p n x)
lemma eq {F G:ℂ→Cloud I} (h:Vortex 0 F) (hg : F =ᶠ[approaching] G): pay G=pay F:= paid fun n x=> (ends h n x).congr' (hg.mono fun i hi=> congr_fun (congr_fun hi _) _)
end PoleVal
namespace Sew.Thread
variable {T: Thread I}
-- no cutoff this 'value' across ζ
private lemma zeroAngles {F:ℂ→Cloud I} (h:Vortex 0 F)(n)(x:External I n) : Tendsto (fun z:ℂ=>Chain.term T.left (dimension z) (F z) T.chain n x) approaching (nhds (Chain.term T.left (dimension 0) (PoleVal.pay F) T.chain n x)) := by
  rcases hg : T.chain with _|i|⟨a,b⟩
  · exact ends h n x
  · exact ends h n (update x i (x T.left))
  let g(z:ℂ):=dimension z-2*n; have hg' : Continuous g:=by unfold g dimension; fun_prop
  exact (tendsto_finsetSum _ fun i _=> ends h _ (Symbol.joint a b x (ortho n i) (ortho n i))).add (Tendsto.mul (hg'.continuousAt.continuousWithinAt) (ends h _ _))
lemma walking {F : ℂ→Cloud I} (h: Vortex 0 F) (r:ℝ)(L:Finset I) : PoleVal.pay (T.twig L r F) = T.twig L r (fun _=>PoleVal.pay F) 0:= by refine PoleVal.paid fun n x=>?_ ; exact (zeroAngles (T:=T) h n _).const_mul _

lemma epoch {K : ℂ → Screened I} (k:Skin 0 K) {μ:ℝ} (hμ:0<μ) {F:Screened I} (hh : ∀ n x,Tendsto (fun z=> K z n x) approaching (nhds (F n x))) (x:External I 2) :
    PoleVal.pay (Integrates μ K) 2 x= ((π:ℂ)^2)⁻¹ * (∫ t:place 2,F 2 (t,x))*factor μ 0 :=by
  obtain ⟨R,G,hr,H,h⟩:=k
  have he:G 0=F:=by
    funext n x; refine tendsto_nhds_unique_of_eventuallyEq (((H.budget _).region 0 (zone_zero hr) _).continuousAt.continuousWithinAt) (hh n x) ?_
    filter_upwards [neighborhood hr] with z hz; rw [← h z hz]; simp
  have hP : Integrates μ K=ᶠ[approaching] Integrates μ G:=by
    filter_upwards [neighborhood hr] with z hz; funext n x; unfold Integrates; rw [show K z=G z by funext n x; simpa using h z hz n x]
  rw [harvest hr (integrates R (fun z hz=> ((zone_mem ..).mp hz).le) Metric.isOpen_ball H μ hμ) hP]
  unfold Integrates; rw [show dimension 0=(2:ℂ)*(↑(2:ℕ):ℂ) by unfold dimension; norm_num,
      Ambient.projection (H.breeze (zone_zero hr)) (H.texture 0 (zone_zero hr)),he]
lemma exhale {K : ℂ→Cloud I} {Y:Finset I} (h : T.Fits Y) {r:ℝ} (hr:0<r) (hp : Vortex 0 K) (hh: Acts (T.inputs∪(T.chain.reads∪Y)) (T.chain.reads∪Y) K) (x:External I 2) {μ:ℝ} (hμ : 0<μ) :
    PoleVal.pay (Integrates μ (T.spun r K)) 2 x=((π:ℂ)^2)⁻¹ * (∫ t:place 2,T.spun r (fun _=> PoleVal.pay K) 0 2 (t,x))*factor μ 0 :=
    epoch (joined h _ hr hp hh) hμ (fun n y => (zeroAngles (T:=T) hp n (T.warp n y)).const_mul _) x
end Sew.Thread
end YM.MSbar.Pole
