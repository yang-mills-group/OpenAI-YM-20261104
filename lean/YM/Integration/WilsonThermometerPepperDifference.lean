import YM.Integration.WilsonThermometerUnitFilingRaw

/- Extract the actual lower raw integral from two values paid on the same
   older Wilson transfer. The common vacuum normalization stays inside both. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPepperDifference
open Function MeasureTheory RG Wilson Lattice Marker Source Push
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingCoarse
open scoped BigOperators Topology Classical
variable {G:Gauge}(R:Run G){N p b:ℕ}
local notation "H" => R.family.path

theorem scaled (c:ℂ)(f:Config G (R.family.side b p)→ℂ)
    (hf:Integrable f (prior G _)){j:ℕ}(jb:j≤b):
    reading R (N:=N) (c • f) j jb=c*reading R (N:=N) f j jb:=by
  have eq:gust (H) N p b (c • f) j jb=c • gust (H) N p b f j jb:=by
    induction jb using Nat.decreasingInduction with
    | self=>rw [gust_base,gust_base]
    | of_succ i ix ih=>
      rw [gust_step (H) N p b _ ix,ih,StepData.push_smul _ _ _ _ (gust_live (H) N p b f hf ix),
        ←gust_step (H) N p b f ix]
  unfold reading
  rw [eq,Pi.smul_apply,smul_eq_mul]
  ring

theorem pair {j u:ℕ}(uj:u≤j)(w B:ℝ)(width:0<w)
    (f h:Config G (R.family.side (j+1) p)→ℂ)
    (hf:Integrable f (prior G _))(hh:Integrable h (prior G _)):
    let step:=(H).levels.clock.op j p
    let beta:=((H).rep N p (j+1)).beta
    let pay:=fun x:Config G (R.family.side (j+1) p)→ℂ=>reading R (N:=N) (p:=p) (step.push beta x) u uj
    ‖pay f‖≤B →
    ‖pay (fun U=>f U+(((2*w)⁻¹:ℝ):ℂ)*h U)‖≤B →
      ‖pay h‖≤4*w*B:=by
  intro step beta pay left right
  let c:ℂ:=((2*w)⁻¹:ℝ)
  have kernel:=(H).levels.transition_mass j p beta
  have first:=StepData.push_integrable kernel f hf
  have second:=StepData.push_integrable kernel h hh
  have eq:step.push beta (fun U=>f U+(((2*w)⁻¹:ℝ):ℂ)*h U)=step.push beta f+c • step.push beta h:=by
    change step.push beta (f+c • h)=_
    rw [step.push_add kernel _ _ hf (hh.smul c),step.push_smul _ beta _ hh]
  change ‖reading R (N:=N) (p:=p) (step.push beta _) u uj‖≤B at right
  rw [eq,WilsonThermometerUnitFilingRaw.add R _ _ first (second.smul c) uj,scaled R c _ second uj] at right
  change ‖pay f+c*pay h‖≤B at right
  have tariff:‖c*pay h‖≤2*B:=calc
    _=‖(pay f+c*pay h)-pay f‖:=by congr 1;ring
    _≤‖pay f+c*pay h‖+‖pay f‖:=norm_sub_le .. 
    _≤B+B:=add_le_add right left
    _=2*B:=by ring
  have positive:0<2*w:=mul_pos (by norm_num) width
  rw [norm_mul] at tariff
  have restore:‖c‖=(2*w)⁻¹:=by
    change ‖(((2*w)⁻¹:ℝ):ℂ)‖=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive)]
  rw [restore] at tariff
  calc
    ‖pay h‖=(2*w)*((2*w)⁻¹*‖pay h‖):=by rw [←mul_assoc,mul_inv_cancel₀ positive.ne',one_mul]
    _≤(2*w)*(2*B):=mul_le_mul_of_nonneg_left tariff positive.le
    _=4*w*B:=by ring

end YM.Integration.WilsonThermometerPepperDifference
end
