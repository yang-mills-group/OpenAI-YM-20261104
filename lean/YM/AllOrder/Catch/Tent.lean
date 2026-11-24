import YM.AllOrder.Catch.Outlook
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {ι:Type*} {T:Clock ι} {X Y:ι→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)][∀ i,Fintype (Y i)][∀ i,DecidableEq (Y i)]
variable (V:∀ i:ι,ℝ×(X i × Body (Y i))→ℝ) (W:∀i,X i)
    {A B:∀i,X i× Body (Y i)→ℝ}{M:∀i,X i→ Matrix (Y i) (Y i) ℝ}{ρ:∀ i,X i→Body (Y i)}
-- Morph to EVERY Y filter allowed. require growth Flow for given tableau.N.Incr order exact same Hess (paid.Octane). Need n+3 derivatives on Venue + Lift.Enough requested. Choose Holder proof rewriting.N=H+3. Good.
variable (D u v b p:ι→ℝ) {s z₁:ℝ}{k j:ℕ}
local notation "Ω" x=> X x × Body (Y x)
local notation "Γ"=> fun i=> grace (A i) (B i) (ρ i) (M i)
variable {W b V D u p} (U:Vaccine (k+3) D u p T A B ρ M)(N:North W b u T) (S:Flood V T (k+3))
local notation "F"=> fun i=> course (W i)
local notation "Pt"=> Clock.tier (fun i=>Body (Y i)) T
local notation "Ph"=> T.book (fun i=> closedBall (0:Body (Y i)) (D i))
variable {η:Type*}
local notation "H₀"=> T.Meter
local notation "N₀"=> (k+3)
local notation "ℍ"=> T.book (fun i:ι=>closedBall (0:ℝ) (b i))
local notation "L"=> k+3
local notation "T'"=> T.liftF
local notation "R₁"=> fun i=> slopeP (course (W i)) (A i) (B i) (M i) (ρ i)
local notation "AP"=> fun i t=> enrolling (course (W i)) 0 (A i) (ρ i) t
local notation "V₁"=>fun i=> dropP (course (W i)) (B i) (M i) (ρ i)
variable {v}
include N U
lemma bareF (hv:∀ᶠ i in T.rail, |v i|≤b i): Cover T (L) 0 (fun _=>1) (AP) v∧ Cover T (L) 0 (fun _=>1) (V₁) v:= by
 let P:=AP; let Q i (t:ℝ) := (F i t, ρ i (F i t)); have hx:= part_small N hv; let h' := U.D_live.and hx; have he:= Cover.has (k:=k+3) (U:=fun i=> Body (Y i)) (V:=X) (f:=ρ) U.price (h'.mono fun i hi=> (hi.1.1.curve _ hi.2.1).smaller (show L ≤ (k+3)+2 by omega));
 let h₀:Cover T (L) 0 (fun _=>1) (F) v:= (ray W le_rfl ((pole N hv).weak (by norm_num : -(1/2:ℝ)≤0)) N.W_age).weak (by simp); let hh:=h₀.join (h₀.comp (x:=v) (U:=_) (u:=ρ) le_rfl he|>.weak (by simp)) -- argument order?
 have hX : ∀ᶠ i in T.rail, Brush (L) (p i) 1 (A i) (Q i (v i)) ∧ Brush (L) (p i) 1 (B i) (Q i (v i)):= by
   filter_upwards [h'] with i hi; have hv := hi.1.1.color 0 0 ((0:ℝ),F i (v i)) (norm_zero.trans_le hi.1.1.off) (by simp) (norm_zero.trans_lt hi.1.1.pos') hi.2.1; simp only [visit,smul_zero, add_zero] at hv; exact ⟨hv.1.smaller (by omega),hv.2⟩
 let hu:= fun (i:ι) (x:X i)=> Lantern.shade (M i) x-Lantern.shade (M i) 0; have ha :Cover T (L) 0 (fun _=>1) (fun i=> B i∘ Q i) v:= (Cover.comp (a:=0) (b:=0) (x:=v) le_rfl hh (Cover.has U.price (hX.mono fun i hi=> hi.2))|>.weak (by simp)); have hp : Cover T (L) 0 (fun _=>1) (fun i=> A i ∘ Q i) v:= (Cover.comp le_rfl hh (Cover.has U.price (hX.mono fun i hi=> hi.1))|>.weak (by simp));
 have hz : Cover T (L) 0 (fun _=>1) (fun i=> hu i ∘ F i) v:= Cover.weak (Cover.comp le_rfl h₀ (u:=hu) (Cover.has U.price (h'.mono fun i hi=> (hi.1.1.gram _ hi.2.1).2))) (by simp); rw [show (V₁)=fun i=> (B i ∘ Q i) + (hu i ∘ F i) from funext fun i=> funext fun x=>by unfold hu Q dropP; dsimp only [Pi.add_apply,Function.comp_apply]; ring]; simp_rw [enrolling,smul_zero,add_zero]; exact ⟨hp,ha.add hz⟩ -- lem.Tech.Shift manually parser
lemma receiptA : TaylorCap T k b (fun i=>R₁ i (b i)) (fun i=> someJ (R₁ i)) := by
 let K (x:Σ i:ι,{y:ℝ//y∈Metric.closedBall 0 (b i)}):=x.1
 have he:= bareF (T:=ℍ) (u:=u ∘ K) (v:=fun i=> i.2) (U.reposition K (T.liftF K)) (N.way K (T.liftF K)) (Eventually.of_forall (fun i=> mem_closedBall_zero_iff.mp i.2.2))
 have h' (i:ι)(hi:Accent (A i) (B i) (M i) (ρ i)):= avows hi (F i) (course_claim hi (W i)).cont (course_claim hi (W i)).p0 0;
 let f i:= climb2 (AP i); let hh:= U.D_live; have ht:∀ᶠ i in T.rail,0 < b i:= N.early.mono fun i hi=> hi.1
 have hp:TaylorCap T k b (fun i=>f i (b i)) (fun i=> someJ (f i)):= by
   refine TaylorCap.shiftT N.low ht ?_ (TaylorCap.shiftT N.low ht ?_ (TaylorCap.paintT (b:=b) (f':=AP) N.high ht (by omega : k+2 < L) he.1))
   · filter_upwards [hh] with i hi; let h:=h' i hi.2; exact ⟨(by rw [shift,dslope_same]; exact h.2.1), shifty h.2.2⟩ -- not def
   exact hh.mono (fun i hi=> ⟨(h' i hi.2).1,(h' i hi.2).2.2⟩)
 let hg:= hp.negate.less (TaylorCap.paintT N.high ht (by omega : k < L) (f':=V₁) he.2); refine hg.fit (EventuallyEq.refl ..) (fun j hj=> ?_); filter_upwards [hh] with i hi; let v:=course_claim hi.2 (W i); have hz:= nice_drop hi.2 _ v.cont v.p0; have h:ContDiffAt ℝ ω (f i) 0:= shifty (shifty (h' i hi.2).2.2); change _=someJ (-(f i)-V₁ i) j; rw [some_sub (show ContDiffAt ℝ ω (-(f i)) 0 from h.neg) hz, exact_neg h]; rfl
local notation "λ'"=> fun i v=> warmP (A i) (B i) (M i) (ρ i) (V i) (W i) v
local notation "Q"=> fun i z t=> Real.exp (λ' i z t)
local notation "μ"=> fun i=> sweep ((M i) 0)⁻¹
local notation "Ξ₀"=> fun i=> closedBall (0:Body (Y i)) (D i)
local notation "Z'"=> fun i=> ∫ z in Ξ₀ i,Q i z (b i) ∂(μ i)
local notation "ξ"=> fun i j=> coin (V i) (W i) (A:=A i) (B:=B i) (ρ:=ρ i) (M:=M i) j
include S
lemma healthE : ∀ᶠ i in T.rail, IntegrableOn (fun z=> Q i z (b i)) (Ξ₀ i) (μ i):= by
 let K:= Σ i:ι,{z:Body (Y i)//z∈Ξ₀ i}; let P:K→ι:= Sigma.fst; let t:= T.liftF P
 have hp : ∀ᶠ i in T.rail,|b i|≤ b i:= N.early.mono fun _ hi=> (abs_of_pos hi.1).le; have hx:=part_small N hp; have h':= T.booked (Ξ₀) (fun i z=>‖uplift (F i) (ρ i) z (b i)‖ < 1)|>.mp ((alert (U.reposition _ t) (N.way _ t) (v:=b ∘ P) (t.tends.eventually hp) (fun i=>i.2.1) (Eventually.of_forall fun i=> mem_closedBall_zero_iff.mp i.2.2)).2)
 filter_upwards [U.D_live,S.ticket 1 zero_lt_one,h',hx,S.rise,N.early] with i hu ht hp he hh hv; let A' y:= plunge (V i) (W i) y (b i) (ρ:=ρ i); let Y₀ i:= Ξ₀ i; apply ContinuousOn.integrableOn_compact (isCompact_closedBall ..); refine Real.continuous_exp.comp_continuousOn (f:=fun z=> λ' i z (b i)) ?_; unfold warmP; apply ContinuousOn.sub; -- instance.IsProbability.sweep.He
 · exact Lantern.gallon (D i) hu.1 he.1 he.2
 intro y hy; let B' x:=(climb2 (plunge (V i) (W i) x (ρ:=ρ i)) (b i)); have hb:B'=(fun x=> A' x / (b i)^2):=funext fun z=> Eq.symm ((div_eq_iff (pow_ne_zero _ (hv.1.ne'))).2 ((Laplace.SigmaP.shift_two (sign _ (W i) hu.2 hh z).1 (sign _ (W i) hu.2 hh z).2.1 _).trans (mul_comm ..)))
 have hL: ContinuousAt (fun (z:Body (Y i))=> (uplift (F i) (ρ i) z (b i))) y:= by unfold uplift; fun_prop;
 change ContinuousWithinAt B' _ y; rw [hb]; unfold A'; exact (((ht _ (hp y hy)).smooth.continuousAt.comp (f:=fun z=> (uplift (F i) (ρ i) z (b i))) hL).div_const _).continuousWithinAt
lemma lease (hj:j≤k):∀ᶠ i in T.rail, Measurable (fun z=> someJ (Q i z) j):= by
 filter_upwards [U.D_live,S.rise] with i hi hI; exact accessible _ (W i) hi.2 1 (r:=1-Laplace.curvature _ _ _) (by rw [add_sub_cancel]; exact zero_lt_one) hI zero_lt_one j
lemma estimated : TaylorCap T k b (Z') (ξ) := by
 let K:= Σ i:ι,{z:Body (Y i)//z∈Ξ₀ i}; let P:K→ι:= Sigma.fst; let t:= T.liftF P
 have hl:= dream (U.reposition P t) (N.way P t) (S.paint P t) (fun i=> i.2.1) (Eventually.of_forall fun i=> mem_closedBall_zero_iff.mp i.2.2)
 apply Gate.part (fun i=> (M i 0)⁻¹) D (fun i z=> Q i z (b i)) b (fun i z=> someJ (Q i z)) U.rate hl (Exists.intro _ N.high) (healthE U N S) (fun _=>surge U N S) (fun j hj=>(lease U N S hj).mono fun _ hi=> hi.aestronglyMeasurable) -- order / implicit include
lemma ahead (hj:j≤k):∀ᶠ i in T.rail,Integrable (fun z=> someJ (Q i z) j) (μ i):= Gate.healthy U.rate (he:=(surge U N S hj)) (hx:=((lease U N S hj).mono fun _ hi=> hi.aestronglyMeasurable))
lemma early_line : Tendsto (Z') T.rail (𝓝 1) ∧ TaylorCap T k b (fun i=>Real.log (Z' i)) (fun i=> logS (ξ i)):= by
 have h:=estimated U N S; have hp : Tendsto (fun i=> ξ i 0) T.rail (𝓝 1):= by
    refine tendsto_const_nhds.congr' ?_; filter_upwards [U.D_live,S.rise] with i hi hx; have ht (z:Body (Y i)): Q i z 0=1:=by dsimp only; rw [Catch.initial hi.2 hx, Real.exp_zero]; -- parser
    unfold coin; simp_rw [someJ_zero]; change 1=(∫ z,(Q i z 0) ∂ (μ i)); simp [ht] -- be careful
 exact ⟨h.tends hp, TaylorCap.process _ (Real.contDiffAt_log.mpr one_ne_zero) h hp N.high (N.early.mono fun i hi=> hi.1)⟩
end YM.AllOrder.Catch
