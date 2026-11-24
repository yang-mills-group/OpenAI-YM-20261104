import YM.MSbar.Rolling.Natural
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set Next.SectorChange Further.GaussianScalar
open Push Push.Uniform RG Wilson Gauge Lattice Tree Precision Metric Exterior Price
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{c:Side}
open Cacao Bakery Portal MvPolynomial
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "µ"=> PowerSeries.coeff
local notation "X"=> Positions (Primary c G)
local notation "V"=> Config G c
set_option quotPrecheck false
noncomputable def widthV (G:Gauge) (c: Side)(x:Positions (Primary c G)) := Wilson.energy (represent (tint G _ x))
def breed (G: Gauge) (c:Side)(s:ℝ): Config G c→ℝ:= bare (s⁻¹^2)
noncomputable def opening (G:Gauge) (c:Side) : Nesting G c := -(splitV (singularity (widthV G c) 2))
variable (R:PathData G)(p:Clip)(h:∀ j,j≤2 → SameJet j (fun x => Wilson.energy (represent x: Config G c)) (main c p R))
lemma pinPose (G:Gauge)(c:Side): Wilson.energy (1:Config G c)=0:=by
    unfold Wilson.energy; refine Finset.sum_eq_zero fun i _=>?_; rw [Progress.DirectedRecipe.face1]; -- name price_one
    linarith only [G.chord_one, G.chord_price 1, congr_arg (fun v:ℝ=>v^2) G.chord_one]
include h
set_option maxHeartbeats 500000 in
lemma sprout (u:ℕ): Trend (breed G c) (opening G c) R p u:=by
    let g (x:fieldDir G c 1):= Wilson.energy (represent x); have hp:ContDiffAt ℝ ω g 0:=(h 0 (by omega)).1; have hz: g 0=0:=by unfold g; rw [link_one]; exact pinPose ..
    have ht: ∀ x: V,0 ≤ Wilson.energy x:= fun x=> Finset.sum_nonneg fun i _=> (coast G (faceValue x i))
    have hg:Premier g:= ⟨hp,hz, (show IsLocalMin g 0 from Eventually.of_forall (fun i=> (show g 0 ≤ g i from hz.symm ▸ ht (represent i)))).fderiv_eq_zero⟩
    let F:= widthV G c; let K:=singularity F 2; let k:= (tint G (Body 1 c)).toContinuousLinearMap
    have hf:Premier F:= hg.line k; have hh:= hg.stitch (g':=main c p R) (fun i hi=> h i (by omega))
    refine ⟨?_,?_,?_,?_,hh,fun n=>?_⟩
    · rw [Kind,opening,_root_.map_neg,splitK,neg_zero]
    · refine ⟨fun i _=>?_⟩; unfold opening; let Q:=µ 0 K; rw [_root_.map_neg,totalDegree_neg]; by_cases hv:i=0
      · rw [hv, splitK]; simp
      rw [splitV, _root_.map_sub,PowerSeries.coeff_C_of_ne_zero hv,sub_zero,singularity, PowerSeries.coeff_mk,one_mul]; exact potsD ..
    · refine Eventually.of_forall fun x=>?_ ; have he : Envelope (breed G c x):=by
          obtain ⟨C,hC⟩:= isCompact_univ.bddAbove_image ((show Continuous (breed G c x) from bare_cont _).norm.continuousOn) -- edit signature
          refine ⟨(show Continuous (breed G c x) from bare_cont (x⁻¹^2)).measurable,C,fun i=>hC ⟨i,mem_univ _,rfl⟩⟩
      exact ⟨⟨fun t U=>bare_gauge (x⁻¹^2) U t,fun U s t=> bare_pull (x⁻¹^2) U s t,he,bare_pos (x⁻¹^2)⟩, by rw [breed,bare,pinPose G c,mul_zero,Real.exp_zero]⟩
    · refine ⟨0,1,zero_lt_one,Eventually.of_forall fun x U=>?_⟩; unfold breed bare; apply le_of_eq; rw [pow_zero,div_one]; ring_nf
    have hL:= earn 2 u F hf.1 (fun i hi x=>hf.zeroP i x hi) _ (payY X n); refine hL.neg.egress (Eventually.of_forall fun t y _=>?_)
    have he:(µ 0 (singularity (widthV G c) 2):Pot (Primary c G))=potter F 2:=by unfold singularity; rw [PowerSeries.coeff_mk]
    have hZ: MvPolynomial.eval y (µ 0 K)= height c p R y:=by
       have hb:rim F y y=rim g (k y) (k y):= hg.carriage k y y; rw [show µ 0 K=potter F 2 from he,pots,hf.second,hb,height,hh.second]; apply congr_arg
       have hp:= congr_arg (fun i:Tensor.T (fieldDir G c 1) ℝ 2=> i ![k y,k y]) (h 2 le_rfl).2.2; change iteratedFDeriv ℝ _ _ _ _= iteratedFDeriv ℝ _ _ _ _ at hp; rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply] at hp; exact hp
    change -(F _/ _-taste _ (picture y K) _) = _
    rw [SplitT K y,hZ,show taste u (picture y (opening G c)) t= -taste u (picture y (splitV K)) t from ?_]; swap; · unfold taste opening; unfold picture;simp only [map_neg,mul_neg]; rw [Finset.sum_neg_distrib]
    unfold breed bare; rw [Real.log_exp]; unfold F postcard widthV; ring -- `K` reduc
end YM.MSbar.Rolling
