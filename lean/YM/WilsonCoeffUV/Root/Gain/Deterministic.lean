import YM.WilsonCoeffUV.Root.Gain.PerBlock
/-!
# From Hall to marked step. Mean vs down-gradient and post; only leading r α=tags. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {P:Patch}{n c:Side}{U V:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}
lemma canopy (P:Patch)(w:Site P.L)(q:Drip P G)(Y:ChamberTen G (Vote D) r)(p:Smooth Y): Smooth (pulseS P w q Y):=by
    intro σ x; unfold pulseS Bank.pump; let T:= (σ.symm).arrowCongr (Equiv.refl (YForest G))
    rw [← T.tsum_eq]; refine tsum_congr fun y=>?_;
    rw [show T y=y ∘ σ from rfl]; unfold spinJob featherS revolve; simp only [Function.comp_apply]
    rw [← Function.comp_assoc,p]; congr 1; exact Equiv.prod_comp σ (fun i=> owns P.L q i y (x i))
lemma hall_grace (P:Patch)(q:Drip P G)(Y: ChamberTen G (Vote D) r)(h)(u:Smooth Y): Smooth (hall P h q Y):=(Blue.Smooth.sum (fun i _=>canopy P i q Y u)).smul _
lemma windy (o x:Cover)(p:Fin r→YForest G): stance 0 (-o+x) (jog (-o) ∘ p) = stance o x p:= by
   let X: Fin (r+2)→Cover:= Fin.cons o (stud x p)
   have ht i: (Fin.cons 0 (stud (-o+x) (jog (-o) ∘ p)):Fin (r+2)→Cover) i = -o+X i:=by
       refine Fin.cases (by simp [X]) (fun j=>?_) i; refine Fin.cases rfl (fun a=>by simp [stud,X,jog]) j
   unfold stance league; simp_rw [ht,Bank.terrain,add_sub_add_left_eq_sub]; rfl
lemma feather_roar {Y:ChamberTen G (Vote D) (r+1)}(he:roaring 0 Y s A)(P:Patch)(w:Site P.L): roaring (lift w) (featherS P w Y) s A:=by
   let o:=lift w; let T:= soprano P w D
   refine ⟨he.1,fun x i=>⟨he.1,fun y=>?_⟩⟩
   let a:= -o+x; let F:=fun x k=> windsL x k Y
   have ht (y):windsL x i (featherS P w Y) y=T (F a i (jog (-o) ∘ y)):=by
      unfold F windsL T; simp only [Finset.sum_apply,map_sum,Pi.sub_apply, map_sub]; apply Finset.sum_congr rfl; intro b _
      unfold prune featherS revolve; rw [Function.comp_apply,Function.comp_apply]; congr 2
      · rw [← comps_head]; rfl
      rw [← comps_head]; congr 2; unfold jog stone; simp [a,o]; abel
   rw [ht y]; have h:= ((he.2 a i).2 (jog (-o) ∘ y)); rw [show stance _ _ _= _ from windy o x y] at h
   exact (T.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (budgetS ..)).trans h)

-- difference Native vs deterministic leading estimate

def blur (G:Gauge)(P:Patch)(s t B:ℝ): ℕ→ℝ
    | 0=> 0
    | r+1=> (r+1:ℕ)* (B^(r+1)*Real.exp (8*s)*tiePay (Co P.L (Hooks G)) (r+1) (s-t))
lemma blur_nn (G:Gauge)(P:Patch)(s t B:ℝ)(h:t<s)(p:0≤B)(r): 0≤blur G P s t B r:=by
   cases r; exact le_rfl; rename_i r; unfold blur; exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (tieN_nn (r:=r+1) (sub_pos.mpr h)))
lemma Hall_cross (P:Patch)(Q R:Drip P G)(Y:ChamberTen G (Vote D) r)(w:Site P.L)(g:Smooth Y)(u:Twig 0 s A Y)(p: Wing 0 s X Y)(T:ReaderT P.L G)(hp:verdant R Q T)(hT:dragCup Bank.terrain t B T)(e:dragCup Bank.terrain t B Q)(v: dragCup Bank.terrain t B R)(hg:t/P.L.val≤s)(ht:0≤t')(h't:t'<t): Twig 0 t' (blur G P t t' B r *X) (pulseS P w Q Y-pulseS P w R Y):=by
   cases r with
   | zero=>
      have he (T:Drip P G) : pulseS P w T Y=pulseS P w 0 Y:=funext fun _=>by simp [pulseS,Bank.pump,spinJob]
      rw [he Q,he R, sub_self,blur, zero_mul]; exact Cork.zero
   | succ r=>
     have hx: Smooth (featherS P w Y):=fun σ x=> by unfold featherS revolve; rw [Function.comp_apply,Function.comp_apply,←Function.comp_assoc,g]
     change Cork Bank.terrain 0 t' (blur G P t t' B (r+1)*X) _; unfold pulseS
     convert! mixRoad (P:=featherS P w Y) (Cork.touch (soprano P w D) (Cork.turn (lift w) u)) v e hp hx (feather_roar p P w) hT hg ht h't using 1; unfold blur; ring
lemma hall_cross (P:Patch)(Q R:Drip P G)(Y:ChamberTen G (Vote D) r)(h:ℕ)(g:Smooth Y)(u:Twig 0 s A Y)(p: Wing 0 s X Y)(T:ReaderT P.L G)(hp:verdant R Q T)(hT:dragCup Bank.terrain t B T)(e:dragCup Bank.terrain t B Q)(v: dragCup Bank.terrain t B R)(hg:t/P.L.val≤s)(ht:0≤t')(h't:t'<t): Twig 0 t' ((P.L.val:ℝ)^h * (blur G P t t' B r*X)) (hall P h Q Y-hall P h R Y):=by
   unfold hall; rw [←smul_sub (tiara P h) (_ :ChamberTen G (Vote D) r),←Finset.sum_sub_distrib,←tier_cash]; exact Cork.μ (Cork.sum (fun w _=>Hall_cross P Q R Y w g u p T hp hT e v hg ht h't)) _
lemma wing0 {Y:ChamberTen G (Vote D) r}(p:Twig 0 s 0 Y): Y=0:= funext fun x=> norm_le_zero_iff.mp ((p.2 x).trans_eq (zero_mul _))

section
variable (I:Gear G)(P:Stand I)
-- Eng=h here LENGTH inherited h+e not used (must be attached)
-- prior mix. off diag price via prior shoulder + Wick spurs

def helmet (h:ℕ)(Y:Single G D):= chorus I.patch I.kernel I.angle P.R P.Q P.page h Y
def fanfare (h:ℕ)(Y:Single G D):= mix P.moving (helmet I P h Y)
def awning (Y:Single G D)(w:Site I.patch.L)(j k):= puck I.patch I.kernel I.angle P.R P.Q P.page (gatherT I.patch w (lift w) Y) j k

def carnival (h:ℕ)(Y:Single G D)(j k:ℕ): ChamberTen G (Vote D) k:=
    tiara I.patch h • ∑ w:Site I.patch.L, ∑ i∈Finset.range (h+3*j), scoop (awning I P Y w (i+1) j k)
lemma tier_owns (h:ℕ)(Y: Single G D)(k r): helmet I P h Y k r=hall I.patch h P.Q (Y k r) + carnival I P h Y k r:=by
    have hg (w:Site I.patch.L): scoop (awning I P Y w 0 k r)= pulseS I.patch w P.Q (Y k r) := by
       unfold awning puck; rw [level]; unfold slidesJ pulseS; rw [inspectFace]; ext1 x; rw [scoop,Bank.prism,climb_cut,climb_cut]; rfl
    unfold helmet chorus hall carnival tiara; simp_rw [Pi.smul_apply,Finset.sum_apply]; simp_rw [windsT]
    rw [← smul_add _ (_:ChamberTen G (Vote D) r),← Finset.sum_add_distrib]; congr 1; apply Finset.sum_congr rfl; intro w _; unfold sluice; simp_rw [show 1+h+3*k=(h+3*k)+1 by omega,Finset.sum_range_succ']; funext x; simp only [scoop, Finset.sum_apply,Pi.add_apply];
    change _+awning I P Y w 0 k r _=_; rw [show awning _ _ _ _ _ _ _ _= _ from congr_fun (hg w) x]; exact add_comm ..

def veering (h:ℕ)(Y:Single G D)(j k):= ∑ i∈ Finset.range j, coeff (j-i) (P.moving^i*(P.moving⁻¹)^k) • helmet I P h Y i k
lemma helmet_bows (Y:Single G D)(h j k): fanfare I P h Y j k =hall I.patch h P.Q (Y j k)+ (carnival I P h Y j k+veering I P h Y j k):=by
   unfold fanfare Blue.mix; rw [Finset.sum_range_succ,Nat.sub_self,coeff_zero_eq_constantCoeff_apply]
   simp only [map_mul,map_pow,Stand.moving,constantCoeff_inv,back_cc P.sunshine,inv_one,one_pow, mul_one,one_smul]; rw [tier_owns]; unfold veering Stand.moving; abel
lemma clamped (j:ℕ){Y:Single G D}(p:shellK e Y)(r:ℕ)(w:Site I.patch.L)(g:e<r+2*j): awning I P Y w j 0 r=0:=by
   induction j generalizing r with
   | zero =>
      unfold awning puck; rw [level]
      have he: (gatherT I.patch w (lift w) Y) 0 r=0:= by unfold gatherT revolve; simp_rw [p 0 r (by omega)]; exact funext fun _=> map_zero _
      ext1 x; unfold slidesJ Bank.prism; rw [climb_cut]; simp [tiles,bend,he,turnTen]
   | succ j ih=>
      have hA (k): P.rays k 0=0:= P.negative _
      have he (Q:ropes Cover (Helms I) (Helms I)): paintC Q P.rays (fun j k=>awning I P Y w j k) j 0=0:= by
         simp only [paintC]; apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro u hu; have hx : u.1=0:=by have h:=Finset.mem_antidiagonal.mp hu; omega
         rw [hx,hA]; unfold rondel; funext r; apply Finset.sum_eq_zero; intro v hv; have hk:= Finset.mem_antidiagonal.mp hv
         have hR (R:Gen (Vote D) (Cloth (Helms I))):rill Q (0:Gen ℝ _) R r v.1 v.2=0:=by subst r; ext x y; simp_rw [rill_spell]; simp
         rw [hR _]; funext x; simp [swivel,ruins]
      have hp:= ih (r+2) (by omega)
      unfold awning puck; rw [inchC]
      change (((j+1:ℕ):ℝ)⁻¹ • (rime P.payMat _+paintC P.payMat P.rays (awning I P Y w) j 0+paintC P.payMat.transpose P.rays (awning I P Y w) j 0):Gen (Vote D) (Cloth (Helms I))) r=0
      rw [he,he,add_zero,add_zero]; funext x; simp_rw [Pi.smul_apply,rime,ruins,rain_spell]; unfold awning puck at hp; simp [hp]
lemma fanLead (h':ℕ)(Y:Single G D)(p:shellK r Y): fanfare I P h' Y 0 r= hall I.patch h' P.Q (Y 0 r):=by
    rw [helmet_bows]; simp only [veering, Finset.range_zero, Finset.sum_empty,add_zero]; unfold carnival
    rw [Finset.sum_eq_zero,smul_zero,add_zero]; intro w _; apply Finset.sum_eq_zero; intro j _; rw [clamped I P (j+1) p r w (by omega)]; rfl
end
end YM.WilsonCoeffUV.Cosmos
