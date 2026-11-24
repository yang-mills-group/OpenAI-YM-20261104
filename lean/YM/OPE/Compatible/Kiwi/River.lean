import YM.OPE.Compatible.Kiwi.Star
/-!
# Towers at finite radius. variation parameter for SPD only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I:Type}{ℓ:Filter I}
local notation "AX"=> Axis
def LakeT (ℓ: Filter I):Filter (I×ℕ):= Filter.bind ℓ fun i=> atTop.map fun k:ℕ=> (i,k)
local notation "Q"=> LakeT ℓ
lemma sails {f:I×ℕ→Prop}: (∀ᶠ i in Q, f i)↔ ∀ᶠ i in ℓ,∀ᶠ j:ℕ in atTop,f (i,j):=by simp [LakeT]
lemma coast₁:Tendsto Prod.fst Q ℓ:=by
    rw [tendsto_def]; intro s hs; rw [← eventually_mem_set,sails]; exact (show ∀ᶠ i in ℓ,i∈s from hs).mono (fun i hi=> Eventually.of_forall fun _=>hi)
lemma coast₂:Tendsto Prod.snd Q atTop:=by refine tendsto_def.mpr fun s h=>?_ ; change (∀ᶠ i in Q,i.2∈s); exact sails.mpr (Eventually.of_forall fun _=> h)
lemma WScale (q:Nestle.Pose)(p:Nestle.Pose)(B:List Axis→ Cover→ℝ)(t:ℝ): t*Wind p q B=Wind p q (fun i a=> t*B i a):=by unfold Wind mission Pose.Lck; split_ifs<;>ring
lemma WTends (p q:Nestle.Pose)(B:I→List Axis→Cover→ℝ)(g:List Axis→Cover→ℝ)(h:∀ D a,p.heat+q.heat=D.length+2→ Tendsto (fun j=>B j D a) ℓ (𝓝 (g D a))): Tendsto (fun i=> Wind p q (B i)) ℓ (𝓝 (Wind p q g)):=by
    have he (j):j=p.heat→True:=fun _=> trivial; unfold Wind mission Pose.Lck; refine Tendsto.sub (tendsto_const_nhds.mul (Tendsto.sub ?_ ?_)) (tendsto_const_nhds.mul (Tendsto.sub ?_ ?_)); all_goals split_ifs <;> first | exact tendsto_const_nhds | apply h; simp [Pose.heat];omega
lemma WZero (q p:Nestle.Pose):Wind p q (fun _ _=>0)=0:=by unfold Wind mission Pose.Lck; split_ifs<;>ring
lemma WSum (p q:Nestle.Pose)(f g:List Axis→Cover→ℝ):Wind p q f+Wind p q g =Wind p q (fun i a=> f i a+g i a):=by unfold Wind mission Pose.Lck; split_ifs<;>ring
lemma WMinus (p q:Nestle.Pose)(f g:List Axis→ Cover→ℝ): Wind p q f-Wind p q g=Wind p q (fun i a=> f i a-g i a):=by unfold Wind mission Pose.Lck; split_ifs<;>ring
variable (u:I→Side)(q:Side)(h:q.val>1) (x y a:Cover) (D:List Axis)
abbrev polls (i:I×ℕ):Side:=stageN q (u i.1) i.2
local notation "Y¤"=> polls u q
lemma Q_chart (hp:Ncap u ℓ): Ncap Y¤ Q:=by
    refine tendsto_atTop_mono (fun p=>(show (u p.1).val≤ _ from Nat.le_mul_of_pos_right _ (q^p.2).pos)) (hp.comp coast₁) -- defeq
lemma up_chart (hp:Ncap u ℓ): Tendsto (fun i: I × ℕ=> Balsam.dew (u i.1)) Q (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (hp.comp coast₁))
lemma ζ_norm (q:Side)(i:ℕ): 0≤baseR q i:= (show 0<baseR q i from val_pos _).le
lemma outer_zone (hp:Ncap u ℓ) (x:Cover)(hN:ℕ):∀ᶠ i in Q, hN ≤ ((Y¤) i).val∧2*size (rangeS q i.2 x+a)≤ ((Y¤) i).val:= by apply Eventually.and ((Q_chart u q hp).eventually_ge_atTop _); rw [sails]; exact (hp.eventually_ge_atTop _).mono (fun i hi=> Eventually.of_forall fun j=>beamMass q (u i) a x j hi)
lemma star_cost (hp:Ncap u ℓ):Tendsto (fun i:I×ℕ=>baseR q i.2 ^ (D.length+2) * seam D ((Y¤) i) (rangeS q i.2 x+a)) Q (𝓝 0):=by
    obtain ⟨C',hC,M,hM⟩:= image_pebbles D; let e:=D.length+2; let g(i:I×ℕ):= C'*Balsam.dew (u i.1)^e
    have hx:= ((up_chart u hp).pow e).const_mul C' -- q omitted?
    refine squeeze_zero_norm' (a:=g) ?_ ?_
    · filter_upwards [outer_zone u q a hp x M] with i ⟨hi,hh⟩; rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (ζ_norm _ _) _)]; apply (mul_le_mul_of_nonneg_left (hM (Y¤ i) hi _ hh) (pow_nonneg (ζ_norm _ _) _)).trans_eq; change baseR q i.2^e*(C'*Balsam.dew (Y¤ i)^e)= C'*Balsam.dew _ ^ e; rw [mul_left_comm,← mul_pow,show baseR q i.2 * Balsam.dew (Y¤ i)= _ from ?_]; have hf:= val_pos (ζ q i.2); change (ζ q i.2).val * ((sizeR ((u i.1)*ζ q i.2))⁻¹:ℝ)= Balsam.dew (u i.1); rw [show sizeR _= sizeR (u i.1)*sizeR (ζ q i.2) from by unfold sizeR;rw [PNat.mul_coe,Nat.cast_mul],mul_inv,mul_left_comm]; erw [mul_inv_cancel₀ hf.ne',mul_one];rfl
    convert! hx using 1; simp [e]
open Maxwell Pert.Band Next.Rank.Radian
lemma beam_dew (p:Nestle.Pose)(Y:Nestle.Pose)(X:Cover)(h:q.val>1)(hp:Ncap u ℓ)(hx:X≠0):
    Tendsto (fun i:I×ℕ=> baseR q i.2^(p.heat+Y.heat)* Wind p Y (fun D a=> mildX D (Lattice.wrap ((Y¤) i) (rangeS q i.2 X+a)))) Q (𝓝 (Wind p Y (fun D _=>dV D Maxwell.Green (incVec 1 X)))):=by
    let T(i:I×ℕ)(D:List Axis)(a:Cover):=baseR q i.2^(p.heat+Y.heat)*mildX D (Lattice.wrap (Y¤ i) (rangeS q i.2 X+a)); simp_rw [WScale]; apply WTends
    intro D a hy; rw [hy]; let R(i:I×ℕ):= rangeS q i.2 X+a
    have hv:Tendsto (fun i:I×ℕ=>baseR q i.2^(D.length+2) * hull D (R i)) Q (𝓝 ((casual D (incVec 1 X)).re)):=by
        have he:incVec 1 X≠0:=by intro hh; apply hx; funext i; have hg:= congr_arg (fun (x:E4)=>x i) hh; norm_cast at hg; simpa using hg
        have hg:= softening he D (ζ q) (smoothDoc q h) (fun i=>rangeS q i X+a) (beamOffset q h X a); apply (hg.comp coast₂).congr'; filter_upwards with i; change (Balsam.dew _ ^ _)⁻¹*_= _; unfold Balsam.dew; rw [inv_pow,inv_inv] -- maybe pow wrong
    have he(i:I×ℕ):mildX D (Lattice.wrap (Y¤ i) (R i))=hull D (R i)+seam D (Y¤ i) (R i):=by unfold seam; ring
    convert! Tendsto.add hv (star_cost (ℓ:=ℓ) u q X a D hp) using 2 with i
    · rw [he i,mul_add]
    · rw [add_zero];rfl
end YM.OPE.Prairies
