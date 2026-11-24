import YM.WilsonCoeffUV.Root.Step.ConditionalReed
import YM.WilsonCoeffUV.Ward.AxisColor
import YM.WilsonCoeffUV.Ward.LocalChord
/-!
# Recentered roll; arbitrary forest change already in Reed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision
open scoped Topology BigOperators ContDiff
variable {n c:Side}{U α β V ι E : Type*}{k r l j i D:ℕ} {G:Gauge}

-- pointwise test.
def jot (b:Volume D): Pal (Vote D) U →ₗ[ℝ] Pal ℝ U := LinearMap.pi fun j=> LinearMap.comp (cloaks ((ContinuousLinearMap.apply ℝ ℝ b).toLinearMap)) (LinearMap.proj j)
@[simp] lemma jot_here (b:Volume D)(W:Pal (Vote D) U)(e i x): jot b W e i x=W e i x b:=rfl
lemma jot_length {W:Pal (Vote D) U}(b:Volume D)(p:shellK l W):shellK l (jot b W):=fun i j h=>funext fun y=> by rw [jot_here,p _ _ h]; rfl
lemma jot_code {W:Pal (Vote D) U} (b:Volume D)(p:Pure (W i)): Pure (jot b W i):=fun r u x=>by rw [jot_here,p r u x]; rfl

lemma retail₁ (P:Pal ℝ (Woods G n))(b:Site n)(r i:ℕ): revolve b (P i r)= fade (spear (jog b : Woods G n≃ Woods G n)) (P i) r:= by
   let f:Woods G n≃ Woods G n:=jog b
   funext x; unfold fade
   rw [Finset.sum_eq_single (f.symm ∘ x)]
   · simp [spear,f]; rfl
   · intro y _ h; obtain ⟨i,hi⟩:=Function.ne_iff.mp h; rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_smul]; rw [spear, Matrix.of_apply,if_neg]; intro e; exact hi (f.injective (by rw [Function.comp_apply,Equiv.apply_symm_apply]; exact e.symm))
   simp
lemma translate_value (n:Side)(b:Site n)(P:Pal ℝ (Woods G n))(h:shellK k P): flash (fun j r=> revolve b (P j r))= loom (spear (jog b : Woods G n≃ Woods G n)) (flash P):=by simp_rw [retail₁,loom_fade _ _ (finite_shell h)]
lemma value_root (n:Side)(b:Site n)(P:Pal ℝ (Woods G n))(h:shellK k P){Z:Type}[Fintype Z](X:Lawn Z→ Lawn (Woods G n))(e:Green X)(t:X 0=0):
    train (spool X) (flash (fun j r=>revolve b (P j r)))=train (spool (fun i=> spear (jog b : Woods G n ≃ Woods G n)*ᵥ X i)) (flash P):=by
    classical
    rw [translate_value n b P h,← spool_loom]; exact DFunLike.congr_fun (spool_chain X (fun u=>spear (jog b : Woods G n≃ Woods G n)*ᵥ u) t (Matrix.mulVec_zero _) e (board _)) _
lemma mantle_reads (b:Site n)(x:Lawn (Woods G n)): mantle (spear (jog b : Woods G n≃ Woods G n)*ᵥ x)=pull 1 b (mantle x):=by
   rw [spear_act,pull_one]; funext i; obtain ⟨i,v⟩:= i; rw [bare_linkC]; unfold translate; rw [bare_linkC]; apply congr_arg G.lieExp; apply congr_arg (coatC G); funext j; unfold dyes'; dsimp only [Function.comp_apply]; congr 1; exact Prod.ext (add_comm ..) rfl
lemma rotation_needed (s:Signed)(Q T: PChart G n)(p:shellK l Q)(h:shellK k T)(x:rollTest (flash Q) (flash T) s 0)(w:Site n):
    rollTest (flash (fun i r=> revolve (s.act w) (Q i r))) (flash (fun i r=>revolve w (T i r))) s 0 := by
   intro Z I g X X' H; let M (b:Site n): Matrix (Woods G n) (Woods G n) ℝ:= spear (jog b : Woods G n≃ Woods G n)
   rw [value_root _ _ _ p X H.g₀ H.f₀,value_root _ _ _ h X' H.g₁ H.f₁]
   have he : TurnsG s 0 (fun t=>g t ∘ affine 1 w) (fun i=> M (s.act w)*ᵥ X i) (fun i=> M w *ᵥ X' i):=by
      refine ⟨?_,?_, by rw [H.f₀,mulVec_zero],by rw [H.f₁,mulVec_zero],fun i=> H.gauge _,?_⟩
      · exact (ContDiffAt.comp (g:=fun i=>M _ *ᵥ i) _ (by rw [H.f₀]; exact board _) H.g₀)
      · exact (ContDiffAt.comp (g:=fun i=>M _ *ᵥ i) _ (by rw [H.f₁]; exact board _) H.g₁)
      filter_upwards [H.shift] with i hi
      unfold M; rw [mantle_reads,mantle_reads, hi, gauge_roll,pull_pull,pull_pull]; simp [affine]
   exact x he

-- Single actually evaluated AND signed map clause separately.
def Wreathe (P Q: Pal (Vote D) (Woods G n))(s:Signed): Prop := ∀ c:Volume D, rollTest (flash (jot c Q)) (flash (jot (spinV s D c) P)) s 0
lemma anchor (x:Volume D): spinV 1 D x=x := by obtain ⟨x,rfl⟩:=submitted x; rw [chronic]; apply congr_arg (page D); exact Subtype.ext (funext fun v=> congr_arg x.val (Signed.act_one v))

lemma tryst (P:Patch)(F H:Pal (Vote D) (Woods G n))(p:shellK k F)(q:shellK l H)(s:Signed)(x:Wreathe F H s)(w:Site P.L) : Wreathe (gatherT P w (wrap n (lift w)) F) (gatherT P (s.act w) (wrap n (lift (s.act w))) H) s:=by
    intro c
    let y:= foldWord P (s.act w) D c
    have ht:rollTest (flash (jot y H)) (flash (jot (spinV s D y) F)) s 0:=by intro Z I x' X X' A; exact x y A
    intro Z I q' X X' he
    have hx:=rotation_needed s _ _ (jot_length y q) (jot_length (spinV s D y) p) (ht) (wrap n (lift w)) he
    rw [show jot c (gatherT P (s.act w) (wrap n (lift (s.act w))) H)=(fun j r=> revolve (s.act (wrap n (lift w))) (jot y H j r)) from ?st]
    rw [show jot _ (gatherT P w _ F)=(fun j r=>revolve _ (jot _ F j r)) from ?eq]; exact hx
    case st=> rw [Ratio.lift_signed_of_odd P.odd_side,wrap_signed]; rfl
    case eq=> rw [← show foldWord P w D (spinV s D c)=spinV s D y from envy s P w c]; rfl

lemma flash_mu {U:Type*}[Fintype U]{P:Pal ℝ U}(c:ℝ)(g:shellK l P): flash (c • P)=c • flash P := by
    ext1 n; rw [coeff_smul,flash,coeff_mk]; rw [flash,coeff_mk]; exact visible_μ (finite_shell g n) c
lemma flash_term {U:Type*}[Fintype U](A:Finset ι){P:ι→ Pal ℝ U}(h:∀ i∈A,shellK l (P i)): flash (∑ i∈ A,P i)=∑ i∈A,flash (P i):= by
    ext1 n; simp only [flash, map_sum,coeff_mk,Finset.sum_apply]; exact visible_sum fun i p=>finite_shell (h i p) _

lemma swellG {P Q: Pal (Vote D) (Woods G n)}{s}(H: Wreathe P Q s)(p:shellK l P)(q:shellK l Q)(c:ℝ): Wreathe (c•P) (c•Q) s:=by
    intro b Z I x X X' he; rw [map_smul,map_smul, flash_mu c (jot_length b q),flash_mu c (jot_length _ p),train_smul,train_smul, H b he]
lemma pulseJ {P Q:ι→Pal (Vote D) (Woods G n)} (A:Finset ι){s}(H:∀ i∈ A,Wreathe (P i) (Q i) s)(p:∀ i∈A,shellK l (P i))(q:∀ i∈A,shellK l (Q i)): Wreathe (∑ i∈A,P i) (∑ i∈A,Q i) s:=by
    intro b Z I x X X' he; rw [map_sum,map_sum, flash_term _ (fun i h=> jot_length _ (q i h)), flash_term _ (fun i h=> jot_length _ (p i h)),map_sum,map_sum]; exact Finset.sum_congr rfl (fun i hi=> H i hi b he)
end YM.WilsonCoeffUV.Soil
