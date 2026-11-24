import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Voltage
/-! # Poincaré calculus with an invertible-leading solution. Keep series determined
 independent of this order crop. Not needing any poly-T scale geometry here. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Read Comparing Pose Original Matrix Quotes
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I A B : Type*}{L:Filter I}[Fintype A][DecidableEq A][Fintype B] {t g:I→ℝ} {w:ℕ}
    (ht : t=O[L] g) (hg:Tendsto g L (𝓝 0))
-- station on all-order prices: THIS step no growing geometry
local notation "V" => (PowerSeries ℂ)
local notation "C'" => Coin L Pose.home t g
abbrev Worth (L:Filter I) (t g:I→ℝ) (f:I→ℂ) (X:PowerSeries ℂ) := ∀ p:ℕ, Coin L Pose.home t g p Pose.home f (fun _=>X)
variable {X:I→ Matrix A A ℂ}{Y:Matrix A A V} {P:I→ A→ℂ} {Q:A→V}
    (y:(Y.map (constantCoeff (R:=ℂ)))=1) (hX:∀ i j, Worth L t g (fun k=>X k i j) (Y i j))
    (p : I→A→ℂ)(hq:∀ a, Worth L t g (fun i=>p i a) (Q a))
include y in
lemma credible : IsUnit Y.det := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr; rw [ RingHom.map_det,RingHom.mapMatrix_apply, y, Matrix.det_one ]; exact isUnit_one

include ht hg
lemma cover {b f:I→ℂ}{x: V} (p:ℕ) (h:C' p home f (fun _=>x)) (e:(fun i=> b i-f i)=O[L] (fun i=>g i^(p+1))) : C' p home b (fun _=>x) := Coin.covered (one_paid _) h (Fare.bare (e.congr_right fun _=>(mul_one _).symm))
lemma worth_mul {X Y:PowerSeries ℂ}{f v:I→ℂ}{p:ℕ} (h:C' p Pose.home f (fun _=>X))(hx:C' p Pose.home v (fun _=>Y)) : C' p Pose.home (fun i=> f i*v i) (fun _=>X*Y) := by
  apply (Coin.mul ht ((ht.trans_tendsto hg).abs.eventually (ge_mem_nhds (by simp))) ( hg.abs.eventually (ge_mem_nhds (by simp)) ) (one_paid _) h hx).congr (EventuallyEq.refl ..) (EventuallyEq.refl ..); exact Eventually.of_forall fun _=> one_mul (Pose.home _)
lemma cost {f:I→ℂ}{X:PowerSeries ℂ} (h:C' 0 Pose.home f (fun _=>X)) : Tendsto f L (𝓝 (constantCoeff X)) := by
  obtain hf:= homebound h.expense; simp_rw [crop_apply,Finset.sum_range_succ, Finset.sum_range_zero,zero_add,pow_zero,one_mul,coeff_zero_eq_constantCoeff_apply] at hf
  exact tendsto_sub_nhds_zero_iff.mp ((hf.congr_right (fun i=> show _=g i from by simp [Pose.home])).trans_tendsto hg)
include hX hq y

-- quantity P obtained by applying actual matrix inverse on true kernel. Use coordinatewise
-- recursion via comparing and then paying matrix inverse boundedly.
lemma solution (he:∀ᶠ i in L, X i *ᵥ P i=p i) (a:A): Worth L t g (fun i=>P i a) ((Y⁻¹ *ᵥ Q) a) := by
  let y':= Y⁻¹ *ᵥ Q; have eq : Y*ᵥ y'=Q:= by unfold y'; rw [ Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (credible y), Matrix.one_mulVec ]
  intro q
  let F i (a:A):= crop q (t i) (y' a); let f i:=g i^(q+1)
  have h (a) : C' q Pose.home (fun i=> F i a) (fun _=> y' a) := Coin.already fun _=> Fare.constant _
  have hh : Tendsto X L (𝓝 1) := by
    rw [←y]; exact tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=> cost ht hg (hX i j 0)
  have V' : ∀ᶠ i in L, IsUnit (X i).det := ((continuous_id.matrix_det.tendsto _ |>.comp hh).eventually
    (eventually_ne_nhds (by simp : (1:Matrix A A ℂ).det≠0))).mono fun i hi=> isUnit_iff_ne_zero.mpr hi
  have K (a:A) := Coin.sum (one_paid L) (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset A))=> worth_mul ht hg (hX a i q) (h i))
  let R i:=P i-F i
  have X0 (a) : (fun i=> (X i *ᵥ R i) a)=O[L] f := by
    apply (((homebound (hq a q).expense).sub (homebound (K a).expense)).congr' ?_ (Eventually.of_forall fun _=>mul_one _)); filter_upwards [he] with i hi
    change p i a - _ - ((X i *ᵥ F i) a - crop q (t i) ((Y *ᵥ y') a)) = _; unfold R; rw [Matrix.mulVec_sub,Pi.sub_apply,hi, eq]; abel
  have hp: Tendsto (fun i=>(X i)⁻¹) L (𝓝 1) := by
    have e : ContinuousAt Ring.inverse (1:Matrix A A ℂ).det := by rw [Ring.inverse_eq_inv',det_one]; exact continuousAt_inv₀ one_ne_zero
    simpa [Function.comp_def] using! (continuousAt_matrix_inv (1:Matrix A A ℂ) e).tendsto.comp hh
  apply cover ht hg q (h a) ; apply (IsBigO.sum (s:=Finset.univ) (fun j (_:j∈(Finset.univ:Finset A))=> (((isBigO_const_of_tendsto (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hp a) j) (show (1:ℝ)≠0 from one_ne_zero)).mul (X0 j)).congr_right (fun i=>one_mul _)))).congr' ?_ (EventuallyEq.refl ..)
  filter_upwards [V'] with i hi; exact congr_fun (show (X i)⁻¹ *ᵥ (X i *ᵥ R i) = R i from by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hi, Matrix.one_mulVec ]) a
end YM.FVA2.GradedFar259.Sparks
