import YM.MSbar.Ballet.Palette
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

open Midpoint Aqua
variable (W:Rep G c)(t:ℝ)(u:ℕ)(x:Positions (Primary c G))
local notation "p"=> W.clip
local notation "R"=> W.path
variable (h:∀ j,j≤2 → SameJet j (fun x => Wilson.energy (represent x: Config G c)) (main c W.clip W.path))
include h
set_option maxHeartbeats 600000 in
lemma pruner (hcl:0<t)(hβ:t⁻¹^2=W.beta)(hx:W.eval=bare W.beta) : (film W (opening G c) t u) x = -(t⁻¹^2)*((widthV G c) (t • x)-Work.G05.blockTaylor (2+u) (widthV G c) (t • x)):=by
    let g (x:fieldDir G c 1):= Wilson.energy (represent x); have hp:ContDiffAt ℝ ω g 0:=(h 0 (by omega)).1; have hz: g 0=0:=by unfold g; rw [link_one]; exact pinPose ..
    have ht: ∀ x: V,0 ≤ Wilson.energy x:= fun x=> Finset.sum_nonneg fun i _=> (coast G (faceValue x i))
    have hg:Premier g:= ⟨hp,hz, (show IsLocalMin g 0 from Eventually.of_forall (fun i=> (show g 0 ≤ g i from hz.symm ▸ ht (represent i)))).fderiv_eq_zero⟩
    let F:= widthV G c; let K:=singularity F 2; let k:= (tint G (Body 1 c)).toContinuousLinearMap
    have hf:Premier F:= hg.line k; have hh:= hg.stitch (g':=main c p R) (fun i hi=> h i (by omega))
    let y:=x; have hE:= drives F (2+u) t y; rw [Rolling.lens 2 u F (fun i hi x=> hf.zeroP i x hi) t y] at hE
    have he:(µ 0 (singularity (widthV G c) 2):Pot (Primary c G))=potter F 2:=by unfold singularity; rw [PowerSeries.coeff_mk]
    have hZ: MvPolynomial.eval y (µ 0 K)= height c p R y:=by
       have hb:rim F y y=rim g (k y) (k y):= hg.carriage k y y; rw [show µ 0 K=potter F 2 from he,pots,hf.second,hb,height,hh.second]; apply congr_arg
       have hp:= congr_arg (fun i:Tensor.T (fieldDir G c 1) ℝ 2=> i ![k y,k y]) (h 2 le_rfl).2.2; change iteratedFDeriv ℝ _ _ _ _= iteratedFDeriv ℝ _ _ _ _ at hp; rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply] at hp; exact hp
    have hv: taste u (picture y (opening G c)) t= - taste u (picture y (splitV K)) t:=by unfold taste opening; unfold picture; simp only [map_neg,mul_neg]; rw [Finset.sum_neg_distrib]
    have he0: ore W (opening G c) t u y= taste u (picture y (Wave.tariff c u p R (opening G c))) t:=by unfold ore taste; simp_rw [picture,PowerSeries.coeff_map]; rfl
    change Aqua.vine W t y-ore W _ t u y= -(t⁻¹^2)*(F (t • y)-Work.G05.blockTaylor (2+u) F (t • y)); rw [he0, Wave.tariff_data (c:=c) _ _ _ _ (sprout R W.clip h u),hv,←hE,show singularity F 2=K from rfl, SplitT K y,hZ]; unfold vine walnut; rw [hx]; change Real.log (Real.exp (- W.beta* F (t • y)))- _= _; rw [← hβ,Real.log_exp]; field_simp; ring -- β mul sign. 
end YM.MSbar.Rolling
