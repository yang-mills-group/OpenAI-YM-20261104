import YM.IntegrationR2.Rose.Outer
/-!
# Unmasked top readout and conditional carrier

Top patch local warm cylinder for PT packet. NOT putting polynomial expansions
into K merges where uncharged. The kernel all-state prescription uses full K
and masks. A representation normally chosen on such R'-β may not be in the
same path; comparison here deliberately at SAME parameters & construction.
Even exhibit precise Step input-ratio invariance for any *one-priced-origin*
mark coefficient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Rose
open Function Filter RG Wilson Lattice Design Work Ac Padded Start
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
open Ovens Ovens.Pipes Quad.Rose Progress.DirectedRecipe Rack
open YM.FullVolume.Urns PhysicalNext.Repeat Set
variable {G : Gauge} {n : Side} {b : BudgetPoint} {θ:ℕ} {v w β a ε:ℝ}
variable {c:Clip} {M:Berry G θ} {W:PathData G}
section program
abbrev Lu (p : ℕ) (u:G.El) := pre (4+p) (G.curvature u)
def wholeP (p:ℕ)(c:Clip)(u:G.El):= G.price u* c.direct + Lu p u * Design.bulk c
lemma wholeE (p:ℕ)(c:Clip)(u:G.El) : G.price u = wholeP p c u+ Design.bulk c * stub (4+p) u := by unfold wholeP stub Lu Design.bulk; ring
private def rawBonus (b: BudgetPoint)(M:Berry G θ)(U:Config G n)(i:Cell n):= masked b.threshold (touched i) (M.bud i) U
private lemma bonusKey (U:Config G n)(β:ℝ)(b:BudgetPoint)(c:Clip) (M: Berry G θ) : (payload M n c β).additive b U= weight c β*∑ i : Key n, rawBonus b M U i.positive:=by
   unfold Activities.additive
   rw [totals (α:=Sheet n) (g:=fun i => masked b.threshold (eInfo i).support (word M c i β) U) (fun i=>?_), Fintype.sum_sum_type]
   swap; · unfold Activities.regularOccurrence; simp only [payload,Ovens.Pipes.pours,dictionary,leader]; split; rfl; exact masked_zero ..
   have he (q: Blank n) : word M c (Sum.inr q) β=0:=rfl
   simp_rw [he,masked_zero,Finset.sum_const_zero,add_zero,Finset.mul_sum]
   refine Finset.sum_congr rfl fun i _=> ?_
   change masked b.threshold i.skin (Start.weight c β • (colors M i)) U = _
   rw [Key.skin_positive]; unfold rawBonus
   by_cases h:Healthy b.threshold (touched i.positive) U
   · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
   rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero]
private lemma bonusShift (i:Cell n)(s:Signed)(U:Config G n): rawBonus b M U (Key.shifted s i).positive = rawBonus b M U (Face.send s 0 i):=by
   have h0:(Key.shifted s i).root.1=0:=rfl; have he: ((Key.shifted s i).root.1+i.1,(Key.shifted s i).root.2)=i:=by change (0+i.1,i.2)=i; simp
   let r:= Key.shifted s i; let V:= pull s 0 U; have hh : Healthy b.threshold r.skin U ↔ Healthy b.threshold (touched i) V:= by
       rw [Key.spins_healthy, Key.shift_frame, translate_health,he]
   have hx: Healthy b.threshold (touched i) V↔Healthy b.threshold (touched (Face.send s 0 i)) U:=by
      rw [H03.touched_send, Healthy, Healthy, ← H03.flags_send s (0:Site n) b.threshold U,Finset.disjoint_image (aff_inj ..)] -- shift halo
   unfold rawBonus; by_cases h:Healthy b.threshold (touched i) V
   · rw [masked_eq _ _ _ _ (r.skin_positive ▸ hh.mpr h), masked_eq _ _ _ _ (hx.mp h),M.bud_send]; change M.bud r.positive U = M.bud i (pull s 0 U); rw [Key.positive,M.bud_send]; change M.bud (Key.shifted s i).root ((Key.shifted s i).frame U)=_; rw [Key.shift_frame, Berry.bud, translate_face,he]; rfl
   rw [masked_ne _ _ _ _ (r.skin_positive ▸ (show ¬Healthy _ r.skin _ from fun hu=> h (hh.mp hu))), masked_ne _ _ _ _ (fun hu=> h (hx.mpr hu))]
def bonus (b:BudgetPoint)(M:Berry G θ)(c:Clip)(β:ℝ)(U:Config G n):= β*Design.bulk c*∑ i:Cell n,masked b.threshold (touched i) (M.bud i) U
lemma rises (b:BudgetPoint)(M:Berry G θ)(c:Clip)(β:ℝ)(U:Config G n) : (area n M b c β).additive b U=bonus b M c β U:=by
    have he : (area n M b c β).additive b U=(payload M n c β).additive b U:= congr_fun ((preserves (dictionary G n) (raw M c n β) b).same_sum) U
    rw [he,bonusKey,Fintype.sum_prod_type]
    have hm (s:Signed) : (∑ p:Cell n, rawBonus b M U (Key.positive (s,p)))=∑ i:Cell n,rawBonus b M U i:=by
       calc _=∑ i:Cell n,rawBonus b M U (Face.send s 0 i):= by
               rw [← Equiv.sum_comp (Key.shift s)]; refine Finset.sum_congr rfl fun i _=> bonusShift i s U
            _=_:= Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send s (0:Site n), Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩) (rawBonus b M U)
    simp_rw [hm]; unfold bonus Start.weight; let Y:= ∑ p:Cell n, rawBonus b M U p; change β*share*bulk c*(∑ _s:Signed,Y)=β*bulk c*Y; nth_rw 2 [← fair Y]; ring
section stage
local notation "O"=> original n W c b β
local notation "X"=> sketch n W c b β M
local notation "KK"=>area n M b c β
variable {p:ℕ}
local notation "θ0"=> jetTail G (4+p)
-- all-U identity. On flags choose explicitly paid unmasked factor; equation does not make it cheap in any stronger support norm in decay.
variable (H:(original n W c b β).activities.Valid b v w)(ho:(original n W c b β).eval= Wilson.bare β)(he:(payload (jetTail G (4+p)) n c β).EBound b ε)
include H ho he
lemma formal (U:Config G n) : (sketch n W c b β θ0).eval U = Real.exp (-β* energy U+bonus b θ0 c β U):=by
   rw [tilt (M:=θ0) H (by omega) he U,rises,ho]; unfold Wilson.bare; rw [Real.exp_add]; exact mul_comm .. --]
lemma healthyEval (U:Config G n)(hf:flags b.threshold U=∅): (sketch n W c b β θ0).eval U=Real.exp (-β * ∑ i:Cell n, wholeP p c (faceValue U i)):=by
    rw [formal H ho he]; apply congr_arg
    unfold energy bonus; rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_; rw [masked_eq _ _ _ _ (by simp [Healthy,hf]),wholeE p c]; change (_ + β*bulk c*stub (4+p) (faceValue U i))=_; ring
omit H ho he
-- Full termwise decomposition
lemma budZero (n : Side)(W:PathData G)(c:Clip)(b:BudgetPoint)(β:ℝ): (original n W c b β).activities.E=toll n (jetTail G 4) c β:=by
   apply congr_arg (stuff _)
   funext i; simp only [Start.payload,leader]; split
   · cases name (Start.Sheet n) i with
     | inr=>rfl
     | inl j=>
         apply congr_arg (Start.weight c β • ·)
         rw [Key.accrual_def]; exact funext fun U=>(reveal4 (faceValue U j.positive)).symm
   rfl
private lemma weave (M A Z : ℕ → Config G n→ℝ) (hh:M=A+Z) {f:ℕ↪ℕ} : stuff f M=stuff f A+stuff f Z:=by
   rw [hh]; funext i; by_cases he:i∈range f
   · obtain ⟨i,rfl⟩:=he; rw [stuffed]; simp only [Pi.add_apply,stuffed] -- likely unused simp
   rw [Pi.add_apply,blank _ _ he,blank _ _ he,blank _ _ he,add_zero]
lemma oneAdd (M:Gauge)(n:Side)(c:Clip)(β:ℝ)(p:ℕ): toll n (jetTail M p) c β=toll n (jetTail M (p+1)) c β+toll n (jetRow M p) c β:=by
    apply weave; funext i; simp only [leader,Pi.add_apply]; split
    · cases name (Start.Sheet n) i with
      | inl j=>
          funext U; change (Start.weight c β * _)=Start.weight c β * (Berry.bud (jetTail M _) _ U)+Start.weight c β * (Berry.bud (jetRow M _) _ U); unfold Berry.bud; rw [read_row]; change Start.weight c β*stub p (faceValue U j.positive)=Start.weight c β*stub (p+1) _+_; rw [peel p]; ring
      | inr j=> exact Eq.symm (add_zero _)
    exact Eq.symm (add_zero _)
lemma newWords (n:Side)(c:Clip)(W:PathData G)(b:BudgetPoint)(β:ℝ)(p:ℕ): (sketch n W c b β (jetTail G (4+p))).activities.E= ∑ j∈ Finset.range p, toll n (jetRow G (4+j)) c β:=by
    rw [leaves .. |>.1,budZero]; induction p with
    | zero=> simp
    | succ p ih=> have h:= oneAdd G n c β (4+p); rw [Finset.sum_range_succ,← ih,show 4+(p+1)=4+p+1 by omega]; rw [h]; abel
-- on origin carrier. Actually ANY θ Berry, proving format/priced/insertion equivalence on full ratio across Taylor re-entry. Sym. density only.
variable {d:ℕ}{F:Labels.Frame G d}(T:Source.Coefficient F n)
lemma equivMark (c:Clip)(W:PathData G)(b:BudgetPoint)(M:Berry G θ)(β:ℝ)(x:Site n)(A: Source.Hol G)(τ z:ℝ):
    (T.Format x A (original n W c b β)↔ T.Format x A (sketch n W c b β M))∧
    (T.remBound x (original n W c b β) τ z ↔ T.remBound x (sketch n W c b β M) τ z):=by
    refine ⟨⟨fun ⟨x,y,p,a,v,w,h,b,u⟩=>⟨x,y,p,a,v,w,h,b,u⟩,fun ⟨x,y,p,a,v,w,h,b,u⟩=>⟨x,y,p,a,v,w,h,b,u⟩⟩,Iff.rfl⟩
include H
lemma equivParts (hp: θ>2)(he:(payload M n c β).EBound b ε) (x:Site n)(S:Source.SectionData F)(U:Config G n): T.density x S (X) U=(Real.exp (bonus b M c β U) : ℂ)* T.density x S (O) U:=by
    unfold Source.Coefficient.density; rw [tilt H hp he,← totalRead H hp he U, rises,Real.exp_add]; rw [Complex.ofReal_mul,Complex.ofReal_mul]; rw [show T.exponentialEntry x S (X) U=T.exponentialEntry x S (O) U from rfl,show T.marked (X)=T.marked (O) from rfl]; ring
end stage
end program
end YM.WilsonStartup.Rose
