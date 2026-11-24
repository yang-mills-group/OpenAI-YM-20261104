import YM.RG17.Agenda
import YM.OPE.Portfolio.Solemn
/-!
 # End d0 single reading, exact ballast/tower/capture label.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
section elementary
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}{n:Side}
private lemma stillEmpty (T:Activities G n) (g:ℕ→ Config G n→ℂ)(Q: MergeProof.Box n)(hq:Q.2=∅)(U:Config G n): profile T g Q U=0:=by
    have he : IsEmpty {i//barcode T i=Q}:=by
       refine ⟨fun ⟨i,hi⟩=>?_⟩
       have ht:(T.forced i).inventory=∅:= (show _=_ from congr_arg Prod.snd hi).trans hq
       exact (T.forced i).inventory_ne.ne_empty ht
    exact tsum_empty
private lemma limpidField (T: MergeProof.Box n→Poly B)(ht:∀ i,i.2=∅→ T i=0): Accent.field T ∅=1:=by
   unfold Accent.field; rw [Finset.sum_eq_single_of_mem (a:=∅) (by simp)]
   · rw [Accent.grid,if_pos (by simp [Accent.Pattern]),Finset.prod_empty]
   intro b hb he
   unfold Accent.grid; split
   next H=> obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr he; apply Finset.prod_eq_zero hi (ht i ?_)
            exact Finset.eq_empty_iff_forall_notMem.mpr (fun x hx=> Finset.notMem_empty _ (H.2 ▸ Finset.mem_biUnion.mpr (show ∃ j ∈ b,x∈j.snd from ⟨i,hi,hx⟩)))
   next=> exact rfl
lemma sunnyZero (T: Rep G n) (a:Motion) (i:Site n)(b:ℕ → Config G n → ℂ)(t:ℂ)(Q: MergeProof.Box n) (U:Config G n)(h:Q.2=∅): sunny T b a i t Q U=0:=by
   dsimp only [sunny,floatUp,stepUp,Pi.smul_apply,smul_eq_mul]; rw [stillEmpty,scalar_z,mul_zero]; change ((sky a i).symm Q.2)=∅; rw [h]; simp [sky]
lemma soloCrown (R: Rep G n){F:V→ Config G n→ℂ}{S:V→MergeProof.Box n→ Config G n→ℂ}{P:Config G n→Poly B}{x:V→Site n}{e a :ℝ}{w:V→ℝ} (h: Served R F S P x w e a)(U:Config G n)(hc:flags R.p.threshold U=∅)(v:V) (hs:∀ j Q,Q.2=∅→S j Q U=0) : (P U).part (B.fire v)= (R.eval U:ℂ)*F v U:=by
   obtain ⟨H,K,h,_,_,hz⟩:=h
   have hv:R.eval U=Real.exp (R.exponent U):=by rw [Rep.eval,Activities.gas_one _ _ hc,mul_one]
   rw [hv,hz,restore,hc,limpidField,mul_one,Poly.part_smul, whisper]
   · rw [Poly.part_plus,sing,Poly.part_sum, Finset.sum_eq_zero (fun i _=>hop₁ B _ ((h.exp i).2 U) v),add_zero]
   · rw [Poly.part_plus,Accent.mute,Poly.part_sum, Finset.sum_eq_zero (fun i _=>hop B _ ((h.exp i).2 U)),zero_add]
   intro i hi
   have hh:K i U=0:= by by_contra hv; exact ((h.flag i).1.permits U hv|>.2.1.ne_empty) hi
   rw [hh,bar,stillEmpty _ _ i hi,Mach]; simp only [hs _ i hi,Poly.send_zero,sum_const_zero];simp
end elementary
section passage
variable {G:Gauge}(T:History G) (N p:ℕ){i j k:ℕ}
open GridApprox
lemma canvasVac (h:T.Selected)(hk:i ≤ j)(ht:j ≤ N) : pushTo T N p hk (liftVac T N p j)=liftVac T N p i:=by
    induction j,hk using Nat.le_induction with
    | base=> exact pushTo_self ..
    | succ j he ih=> rw [pushTo_next _ _ _ he,← vac_transfer T N p j h ht]; exact ih ((Nat.le_succ _).trans ht)
lemma canvasBills (h:T.Selected)(hk:i ≤ j)(ht:j ≤ N) (z:ℂ) (f:Config G (T.S.side j p)→ℂ)(he: Integrable f (prior G _)) :
     pushTo T N p hk (f+z • liftVac T N p j)=pushTo T N p hk f+ z • liftVac T N p i:=by
   induction j,hk using Nat.le_induction with
   | base=> simp
   | succ j hh ih=> rw [pushTo_next _ _ _ hh,pushTo_next _ _ _ hh, StepData.push_add (T.levels.transition_mass ..) _ _ he ((vac_integrable T N p (j+1) h ht).smul _),StepData.push_smul _ _ _ _ (vac_integrable T N p (j+1) h ht), ← vac_transfer T N p j h ht]; exact ih ((Nat.le_succ _).trans ht) _ (StepData.push_integrable (T.levels.transition_mass ..) _ he)
lemma pastPass (hk:i ≤ j)(he:j ≤ k)(f:Config G (T.S.side k p)→ℂ) : pushTo T N p hk (pushTo T N p he f)=pushTo T N p (hk.trans he) f:=by
    induction k,he using Nat.le_induction with
    | base=> rw [pushTo_self]
    | succ k he ih=> rw [pushTo_next _ _ _ he, ih,pushTo_next _ _ _ (hk.trans he)]
end passage
section
variable {G:Gauge}(C:Family G)(N k m p J:ℕ)(H:C.Makes) (ht:k≤N) (h:J≤k)
open GridApprox
set_option quotPrecheck false
variable (hw:J ≤ m)(hk:m ≤ k)(f:Config G (C.side N p)→ℂ)(z:ℂ)
local notation "T"=> C.path
local notation "B'"=> Stock.census (Site (C.side J p))
local notation "hJ"=> center C.S p (hw.trans (hk.trans ht)) 0
local notation "K"=> birth (B') (C.path.rep N p N) (fun i=> -(hJ|>.copy i (-f)))
local notation "A"=> gust T N p N K k ht
local notation "W"=> center C.S p (hw.trans hk) 0
local notation "Y"=> (couple A (fun i=> (W).copy i (fun _: Config G (C.side k p)=>z)))
local notation "P"=> (pushTo C.path N p (hk.trans ht) (fun U=> (liftVac T N p N U)*f U))
include H
lemma singleFare (hC: Integrable K (prior G _)) (hQ:Integrable Y (prior G _)):
    (fun U=> (gust T N p k Y m hk U).part ((B').fire 0))= P + z • liftVac T N p m :=by
    let γ (U):=liftVac T N p N U*f U
    have hh : (fun U=>(K U).part (B'|>.quiet))= liftVac T N p N:=funext fun U=>by dsimp only [Accent.birth];rw [Poly.part_smul, Poly.pass_part _ (Accent.mute ..),mul_one]; rfl
    have hp : (fun U=>(K U).part (B'|>.fire 0))=γ:=by
       let V:= hJ
       have he : -(V.copy 0 (-f))= f:= (handneg C N p J (hw.trans (hk.trans ht)) f 0).trans (Ribbons.cappid C J p N (hw.trans (hk.trans ht)) (fun _=>f) true) -- gh
       funext U; rw [boot]; change _* (-(V.copy 0 (-f))) U = _; rw [he];rfl
    let ℓ(u:Config G (C.side k p)):= z; have ht' : (W).copy 0 ℓ=ℓ:= Ribbons.cappid C J p k (hw.trans hk) (fun _=>ℓ) true
    have hx : Integrable γ (prior G _):= hp ▸ (show Integrable _ _ from ((Poly.get ((B').fire 0)).restrictScalars ℝ).integrable_comp hC)
    have ha:(fun U=>(A U).part (B'|>.fire 0))=pushTo T N p ht γ:= (gust_choose T N p K hC ht _).trans (congr_arg _ hp)
    have hA:(fun U=>(A U).part (B'|>.quiet))=liftVac T N p k:= (gust_choose T N p K hC ht _).trans ((congr_arg _ hh).trans (canvasVac T N p H.wilson ht le_rfl))
    have hz : (fun U=>(Y U).part (B'|>.fire 0))=pushTo T N p ht γ + z • liftVac T N p k:=by
       funext U; unfold couple; rw [shock,whisper _ _ (Accent.mute ..), Poly.pass_part _ (Accent.mute ..),sing]
       rw [show (A U).part _=_ from congr_fun ha U,show (A U).part _=_ from congr_fun hA U]; change _ * (W).copy 0 ℓ U + _ = _; rw [show (W).copy 0 ℓ U=z from congr_fun ht' U]; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
    rw [gust_choose T N p Y hQ,hz,canvasBills _ _ _ H.wilson hk ht _ _ (pushTo_integrable T N p ht γ hx), pastPass]
include ht in
lemma lensZero (L:C.label 0) : lens C N k p 0 L=(fun _=> L 0):=by
   have hc := Ribbons.ManyCopies.Cadet.Studio.ZeroDegree.one_core (F:=C.labels.level 0) L
   rw [scopes C N k p 0 L H ht,hc]; funext U; unfold alto; rw [pow_zero,inv_one,one_mul]
   suffices h : masked _ _ (candidate C k p 0 0) U=0 by rw [h,add_zero]
   unfold candidate initial masked; simp only [map_zero,Set.indicator]; split
   · let B:=C.localSection 0; have he:B.evaluate 0=0:= (B.eval_linear.mk' B.evaluate).map_zero
     change _ * B.evaluate 0 _=0; rw [he]; exact mul_zero _
   · exact rfl
variable (hG:G.Simple)
include hG
lemma capZero (he:C.ref 0≤ N)(L:C.label 0) : C.O N p L (0:Site _)= (fun _=> RG17.send0 C L) :=by
    obtain ⟨c,hc⟩:= RG12.unit_spans hG C 0 (C.ref 0) (by decide) L
    change L=c • C.refUnit 0 at hc; rw [hc,map_smul,(C.linearO N p 0 (0:Site _)|>.map_smul c _ : C.O N p (c • C.refUnit 0) (0:Site _) = _),C.constant H 0 he (p:=p), show RG17.send0 C (C.refUnit 0)=(1:ℂ) from ?_]; rfl
    simp only [Family.refUnit,Source.unitVec,pow_zero, one_smul]; rfl
end
end YM.MergeProof
