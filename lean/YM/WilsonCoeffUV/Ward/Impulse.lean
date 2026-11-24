import YM.WilsonCoeffUV.Ward.AxisColor
/-!
# Infinitesimal Ward at given orders

Leave directions at arbitrary sites free, no condition of low frequency or
restriction to affine fields. Define chords through independent rank tensors
on ONE link plus gauge impulse, this matters on crossing distances. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter Metric
open Blue FreeResolvent Tree Matrix PowerSeries Next.Free Gauge
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c: Side}{G:Gauge}

section one
-- universal leg infinitesimal
variable (a b:G.Color)
def swerveG (v:Lawn (Option G.ColorIndex)) : G.El := G.lieExp (v none • a)*G.lieExp (coatC G (fun i=>v (some i)))*(G.lieExp (v none • b))⁻¹
def jerk (v:Lawn (Option G.ColorIndex)):= (coatC G).symm (LocalH.snap G (swerveG a b v))
lemma jerk_green : Green (jerk a b) := by
  have h (a : G.Color): Green fun v:Lawn (Option G.ColorIndex)=>G.mat (G.lieExp (v none • a)) := G.exp_jet.contDiffAt.comp _ ((contDiffAt_apply ℝ ℝ none _).smul contDiffAt_const)
  have hz : Green fun v:Lawn (Option G.ColorIndex)=>G.mat (G.lieExp (coatC G (fun i=>v (some i)))) := (G.exp_jet.comp (coatC G).contDiff).contDiffAt.comp _ (contDiffAt_pi.mpr fun i=> contDiffAt_apply ℝ ℝ _ _)
  have H : Green fun v=> G.mat (swerveG a b v) := ((h a).mul hz).mul (Push.Loops.mat_inv_diff (h b))
  have hm : G.mat (swerveG a b 0)=1:= by unfold swerveG; rw [show (fun i : G.ColorIndex => (0:Lawn (Option G.ColorIndex)) (some i))=0 from rfl]; simp
  apply (coatC G).symm.contDiff.contDiffAt.comp (f:=fun v=>LocalH.snap G (swerveG a b v)) 0
  exact (show ContDiffAt ℝ ω G.plog (G.mat (swerveG a b 0)) from hm.symm ▸ G.plog_diff).comp 0 H
lemma jerk_zero : jerk a b 0=0 := by
  unfold jerk swerveG; rw [show (fun i : G.ColorIndex=> (0:Lawn (Option G.ColorIndex)) (some i))=0 from rfl]; simp [LocalH.snap]
lemma jerk_exp : ∀ᶠ v:Lawn (Option G.ColorIndex) in 𝓝 0,G.lieExp (coatC G (jerk a b v))=swerveG a b v := by
  have hc : Continuous (swerveG a b) := by unfold swerveG; fun_prop
  have hZ : swerveG a b 0=1 := by unfold swerveG; rw [show (fun i:G.ColorIndex=> (0:Lawn (Option G.ColorIndex)) (some i))=0 from rfl]; simp
  simp_rw [jerk,ContinuousLinearEquiv.apply_symm_apply];
  exact (hZ ▸ hc.tendsto 0).eventually G.plog_right

/-- At t=0 time slot, return discrete vector field. -/
def electric (i:G.ColorIndex) (v:Lawn G.ColorIndex) := rub (fun w=>jerk a b w i) none (fun x=> x.elim 0 v)
-- restriction matrix
variable {U:Type}[Fintype U]
def nilM (U:Type)[DecidableEq U] : Matrix (Option U) U ℝ := of fun i j=> if i=some j then 1 else 0
lemma nilM_act [DecidableEq U] (u:Lawn U) : nilM U *ᵥ u= fun x=> x.elim 0 u:= by ext j; cases j with
                                                                         | none=> simp [nilM,mulVec,dotProduct]
                                                                         | some j=> unfold mulVec dotProduct; rw [Finset.sum_eq_single j] <;> simp +contextual [nilM, eq_comm]
lemma liveCurrent (i:G.ColorIndex): Green (electric a b i) := by
  let P:=rub (fun w=>jerk a b w i) none
  have he : Green P:=rubbed ((contDiffAt_apply ℝ ℝ i _).comp 0 (jerk_green a b)) _
  have hv := board (nilM G.ColorIndex)
  apply ContDiffAt.congr_of_eventuallyEq (f:=fun u=> P (nilM G.ColorIndex *ᵥ u)) (ContDiffAt.comp (f:=fun u=>nilM G.ColorIndex *ᵥ u) 0 (show ContDiffAt ℝ ω P (nilM G.ColorIndex *ᵥ0) from by rw [Matrix.mulVec_zero]; exact he) hv)
  exact Eventually.of_forall fun _=> congr_arg P (nilM_act _).symm

lemma electric_point (i:G.ColorIndex): electric a b i 0=(a-b) i:=by
  let K:=Option G.ColorIndex
  let f (t:ℝ):= t • pebble (none: K)
  let Y t:=swerveG a b (f t)
  have hv t : Y t=G.lieExp (t • a)*(G.lieExp (t • b))⁻¹ := by
    have he : f t none=t := by simp [f,pebble]
    unfold Y swerveG
    rw [he,show (fun i:G.ColorIndex=> f t (some i))=0 from funext fun i=> by simp [f,pebble],map_zero,G.mat_lieExp_zero,mul_one]
  have hz:Y 0=1:= by rw [hv]; simp
  have hs (c : G.Color) : HasDerivAt (fun t:ℝ=> G.mat (G.lieExp (t • c))) (G.colorMat c) 0 := Push.side _ G.expDiff_zero.differentiableAt c |>.congr_deriv (DFunLike.congr_fun G.expDiff_zero.fderiv c)
  have he : HasDerivAt (fun t:ℝ=>G.mat (Y t)) (G.colorMat (a-b)*G.mat (Y 0)) 0:=by
    rw [hz]; simp_rw [hv,G.mat_mul,G.mat_inv]
    convert! (hs a).mul (hs b).star using 1; simp [G.colorMat_skew,sub_eq_add_neg]
  have ht:=Push.Loops.delta_rate he; rw [hz] at ht
  have hV : HasDerivAt (fun t=>LocalH.snap G (Y t)) (a-b) 0 := by simpa [LocalH.snap,Push.Loops.delta] using ht
  have hp : HasDerivAt (fun t=>jerk a b (f t) i) ((a-b) i) 0 := by
    let Q:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : G.ColorIndex=>ℝ) i) ∘L (coatC G).symm.toContinuousLinearMap
    exact Q.hasFDerivAt.comp_hasDerivAt 0 hV
  have hh : Green fun w=>jerk a b w i:= (contDiffAt_apply ℝ ℝ i _).comp _ (jerk_green a b)
  have hy := Push.side _ (hh.differentiableAt (by simp)) (pebble (none:K))
  rw [electric,rub,show (fun x:K=> x.elim 0 (0:Lawn G.ColorIndex))=0 from funext fun i=> by cases i <;> rfl]; exact hy.unique hp
lemma jerk_stat : ∀ᶠ x:Lawn G.ColorIndex in 𝓝 0, jerk a b (nilM _ *ᵥ x)=x := by
  filter_upwards [((coatC G).continuous.tendsto (0:Lawn G.ColorIndex)).eventually (by rw [map_zero]; exact G.plog_left)] with x hx
  rw [jerk, swerveG,nilM_act]; simp only [Option.elim_none, zero_smul,G.mat_lieExp_zero, Option.elim_some,one_mul,inv_one,mul_one];
  exact ((congrArg (coatC G).symm hx).trans ((coatC G).symm_apply_apply _))
lemma stop_zero_car [DecidableEq U]: stopF (U:=U) 0=loom (nilM U) := by
  apply serial_ext (by simp [stopF]) _ (by simp [stopF,loom]); intro p
  induction p using MvPolynomial.induction_on with
  | C a=> rw [show C _=realS a from rfl,loom_real]; simp [stopF,realS,stopT,MvPolynomial.algebraMap_eq]
  | add p q a b=> simp only [map_add,a,b]
  | mul_X p j h=> simp only [map_mul,h]; cases j with
                  | none=> rw [show C _=path (none:Option U) from rfl,loom_pin]; simp [stopF,path,stopT_X,nilM]
                  | some i=>
                    congr 1
                    rw [show C _=path (some i) from rfl,loom_pin,Finset.sum_eq_single i] <;> simp +contextual [stopF,path,stopT_X,nilM,eq_comm]
lemma liveStop (i:G.ColorIndex): stopF 0 (spool (jerk a b) i)=path i := by
  rw [stop_zero_car]
  have h := spool_chain (fun u=> nilM _*ᵥ u) (jerk a b) (by simp) (jerk_zero _ _) (board _) (jerk_green _ _)
  have hv:=congr_arg (fun f: Ink _ →+* Ink _=> f (path i)) h
  rw [RingHom.comp_apply,train_path,spool_loom,train_path] at hv
  rw [hv];
  apply mul_left_cancel₀ (a:=PowerSeries.X) X_ne_zero; rw [spool_raised _ (by simp [Function.comp_apply,jerk_zero]),← jet_arg i]
  exact jet_congr ((jerk_stat a b).mono fun x hx=> congr_fun hx i)
lemma fluxStop (i:G.ColorIndex): stopF 0 (brush none (spool (jerk a b) i))=jet (electric a b i):=by
  let Q : Lawn (Option G.ColorIndex) → ℝ := fun w=> jerk a b w i
  rw [spool_ext _ _ (jerk_green a b) (jerk_zero a b) _,stop_zero_car]
  change loom _ (jet (rub Q none))= _; rw [loom_jet _ _ (rubbed (show Green Q from (contDiffAt_apply ℝ ℝ i _).comp _ (jerk_green a b)) _)]
  congr 1; funext i; simp_rw [nilM_act]; rfl

-- zero on unperturbed legs exactly.
lemma emptyStop (i:G.ColorIndex): jet (electric (0:G.Color) 0 i)=0:= by
  let T : Option G.ColorIndex:=none
  let A (w:Lawn (Option G.ColorIndex)):= (fun i:G.ColorIndex=> w (some i))
  have ha : ∀ᶠ w: Lawn (Option G.ColorIndex) in 𝓝 0, jerk (0:G.Color) 0 w=A w:=by
    let N:=(0:Lawn (Option G.ColorIndex)); have he : Continuous A:= by unfold A; fun_prop
    have h := (coatC G).continuous.comp he |>.tendsto N
    filter_upwards [h.eventually (by rw [Function.comp_apply,show A N=0 from rfl,map_zero]; exact G.plog_left)] with w hw
    unfold jerk swerveG; simp only [smul_zero,G.mat_lieExp_zero,mul_one,one_mul, inv_one]; exact (congrArg _ hw).trans ((coatC G).symm_apply_apply _)
  rw [←fluxStop]
  have he: spool (jerk (0:G.Color) 0) i=path (some i) := by
    apply mul_left_cancel₀ (a:=PowerSeries.X) X_ne_zero; rw [spool_raised _ (jerk_zero _ _), ←jet_arg];
    exact jet_congr (ha.mono fun v hv=> congr_fun hv _)
  rw [he, brush_path,if_neg (by simp),map_zero]
end one
end YM.WilsonCoeffUV.Power
