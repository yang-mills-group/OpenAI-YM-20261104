import YM.OPE.Compatible.Kiwi.March
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
local notation "Q"=> LakeT ℓ
variable (u:I→Side)(q:Side)(h:q.val>1) (x y a:Cover)
local notation "Y¤"=> polls u q
open Maxwell -- circular
lemma inc_sub (p q:Cover): incVec 1 (p-q)=incVec 1 p-incVec 1 q:=by ext1 k;simp [incVec] -- remove
lemma scope_inj : Injective (incVec 1):=by
     intro x y h; ext1 i; have hp:=congr_arg (fun x:E4=>x i) h; simp at hp; exact hp
abbrev Bsky (p:Reed G)(x:Cover)(φ:Reed G)(y:Cover):ℝ := if x=y then 0 else Maxwell.Free.K (rayLeg p) (rayLeg φ) (incVec 1 x) (incVec 1 y)
abbrev wedgeL (p:Reed G)(u:I→Side)(q:Side)(h:q.val>1)(x:Cover)(i:I):= Match.mk p.1 (gammaT (u i) q h x) p.2
lemma Nsp (he:∀ i,Even (u i).val)(i:I×ℕ) : Even ((Y¤) i).val := (he i.1).mul_right _
include h
lemma stressY (p P:Reed G)(hp:Ncap u ℓ) (he:∀ i, Even (u i).val)(H:4≤r)(L:KernelChoices):
    let X:= wedgeL p u q h x
    let Y:= wedgeL P u q h y
    Tendsto (fun i:I×ℕ=>baseR q i.2^(p.1.heat+P.1.heat)*(launchW (X i.1) (Y i.1) H L i.2 (Nsp u q he i) -(if x=y then firm p P else 0))) Q (𝓝 (Bsky p x P y)):=by
       intro X Y; simp_rw [launch_parts]; let A:= stow u q x; let B:= stow u q y
       change Tendsto (fun i:I×ℕ=>baseR q i.2 ^ _ * ((if p.2=P.2 then ∑ k:Kv, torque p.1 k*tip P.1 (fun a=>paper (StageLight.reed p.1 k) a (decks k (A i))) (B i) else 0)-(if x=y then firm p P else 0))) _ _
       by_cases ht:p.2=P.2; swap
       · unfold firm Bsky; simp_rw [if_neg ht]; split_ifs with hh; · simpa only [sub_self,mul_zero] using! tendsto_const_nhds (x:=(0:ℝ)) (f:=Q)
         simp_rw [Kw_leg _ _ p P (scope_inj.ne hh),if_neg ht,sub_self,mul_zero]; exact tendsto_const_nhds
       simp_rw [if_pos ht]; let R(i:I×ℕ):=baseR q i.2^(p.1.heat+P.1.heat); let C'(j:Kv)(i:I×ℕ):= torque p.1 j*tip P.1 (fun a=>paper (StageLight.reed p.1 j) a (decks j (A i))) (B i); let s:= Finset.univ.erase (0: Kv); let f(i:I×ℕ):= if x=y then firm p P else 0
       have hx:Tendsto (fun i=> ∑ j∈s,R i*C' j i) Q (𝓝 0):=by
          rw [show (0:ℝ)= ∑ _∈s,0 from Finset.sum_const_zero.symm]; refine tendsto_finsetSum s (fun i hi=>?_); let L:= R; have hv:= deckZero u q h x y p.1 P.1 i (Finset.mem_erase.mp hi).1 hp he
          have ht:=(hv.const_mul (torque p.1 i)); rw [mul_zero] at ht; refine Tendsto.congr' ?_ ht; filter_upwards with j; exact mul_left_comm ..
       change Tendsto (fun i=>R i*((∑ j,C' j i)-f i)) _ _ ; simp_rw [← Finset.sum_erase_add _ (C' · _) (show (0:Kv)∈Finset.univ from by simp), add_sub_assoc,mul_add]; -- R not matched
       suffices ht: Tendsto (fun i=>R i*(C' 0 i-f i)) Q (𝓝 (Bsky p x P y)) by simpa only [zero_add,← Finset.mul_sum] using! hx.add ht
       unfold C'; rw [roll_zero p.1 |>.1,roll_zero p.1|>.2]; simp_rw [Weir.flats,one_mul]; unfold f Bsky; split_ifs with hh
       · subst y; exact stem_zero u q x p P hp ht L
       rw [Kw_leg _ _ p P (scope_inj.ne hh), if_pos ht]; simp_rw [sub_zero, forecast]; rw [←inc_sub]; have hv(i:I×ℕ): A i-B i = wrap _ (rangeS q i.2 (x-y)):=by unfold A B stow rangeS; rw [smul_sub,map_sub]
       simp_rw [hv,←map_add]; exact beam_dew u q p.1 P.1 (x-y) h hp (sub_ne_zero.mpr hh)
end YM.OPE.Prairies
