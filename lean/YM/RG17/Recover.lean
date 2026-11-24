import YM.RG17.Board

/-!
Constructing the P⁻¹U_m readout. Solve true perturbed mixed/full
panels from the diagnostic expansions just derived at HORIZON ZERO.
No assumption on perturbative expansions of the true canonical maps.
The formal readout and associated identities through the claimed
precision are required only on the selected diagnostic probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open OPE.Nesting
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    {F:Final C f S} {L:Layout F} (Z:Ledger L)
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (H:Services C f S) {n:ℕ}{d:Fin n→ℕ}
set_option quotPrecheck false
local notation "ρ"=>OPE.run
section pointwise
variable {E E':Type*} [NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
    [NormedAddCommGroup E'][NormedSpace ℂ E']
private lemma sumOp {J:Type*}[Fintype J](b:Module.Basis J ℂ E)(M:E →L[ℂ] E') :
    ‖M‖≤ ∑ i, ‖((b.coord i).toContinuousLinearMap)‖ * ‖M (b i)‖ := by
   apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)); intro v
   conv_lhs => arg 1; rw [← b.sum_repr v, map_sum]
   rw [Finset.sum_mul]; apply (norm_sum_le _ _).trans (Finset.sum_le_sum _)
   intro i _; rw [map_smul,norm_smul,mul_right_comm]; exact mul_le_mul_of_nonneg_right (((b.coord i).toContinuousLinearMap).le_opNorm _) (norm_nonneg _)
lemma pointwiseBare {M:ℝ→ E→L[ℂ] E'} {p:ℕ} (h:∀ v,Bare Z p (fun r=> M r v)):Bare Z p M:=by
   let b:= Module.finBasis ℂ E
   have hz(i):=Cost.transfer (z:=fun r (_:Unit)=> ‖M r (b i)‖) (h (b i)) (Eventually.of_forall fun r _=> by simp)
   let K i:=‖(b.coord i).toContinuousLinearMap‖
   have hm(i) : Bare Z 0 (fun _=> K i):= Cost.insert_single ‖K i‖ 0 (norm_nonneg _) (Eventually.of_forall fun _=>by simp)
   apply Cost.transfer (Cost.sum (k:=fun i r (_:Unit)=> K i * ‖M r (b i)‖) (H:=Finset.univ) (fun i _=>?_)) (Eventually.of_forall fun r _=> (sumOp b (M r)).trans (Real.le_norm_self _))
   rw [← zero_add p]; exact Cost.bareProduct (hm i) (hz i) (Eventually.of_forall fun r _=> norm_mul_le ..)
lemma pointwiseCoarse {M:ℝ→ E→L[ℂ] E'} {b:ℝ} (h:∀ v,RateLE home ρ (fun r=> M r v) b):RateLE home ρ M b:=by
   let a:=Module.finBasis ℂ E
   apply RateLE.of_norm_le (RateLE.sum (S:=Finset.univ) (f:=fun i r=> ‖(a.coord i).toContinuousLinearMap‖ * ‖M r (a i)‖) ageLarge (fun i _=> ?_)) (Eventually.of_forall (fun r=> sumOp a _))
   simpa only [zero_add] using (RateLE.const ‖(a.coord i).toContinuousLinearMap‖ ageLarge).mul ((h (a i)).norm)
end pointwise
variable {p D:ℕ}
set_option quotPrecheck false
local notation "U"=>Free C D
local notation "s"=>Slot C D

def toFrame (L:Layout F)(D:ℕ) (r:ℝ) : S.Field D →L[ℂ] Free C D:= (L.frame D r).symm.toContinuousLinearEquiv.toContinuousLinearMap
def entry (L:Layout F)(D:ℕ)(r:ℝ):C.label D→L[ℂ]Free C D := (toFrame L D r).comp ((master L D r).toContinuousLinearMap)
structure Diagnostics {D:ℕ} (A:Ports C) (Z:Ledger L) (W:Finset (Stud C D))
    (b: Stud C D → ℕ → ℝ → (Free C D →L[ℂ] ℂ)) (p:ℕ) : Prop where
    framePrice (T:Stud C D)(ht:T∈W) : ∀ q≤p, Bare Z 0 (b T q)
    readPrice : ∀ q≤p,Bare Z 0 (A.read D q)
    agrees (T:Stud C D)(ht:T∈W) (v:Free C D): ∀ q≤p,Bare Z (q+1)
       (fun r=> forecast Z q (A.moments (T.twins (.inr v))) r T.test - accrue Z q (b T) r v)
    cross (T:Stud C D)(ht:T∈W) (v:C.label D) : ∀ q≤p,Bare Z (q+1)
       (fun r=> forecast Z q (A.moments (T.twins (.inl v))) r T.test -
          forecast Z q (combine (b T) (fun j r (_:Unit)=> A.read D j r v)) r ())
    -- All-coefficient reference identity/caps/opening in Phi are OPEN.
    -- Use free lower det at the offset length, polynomials allowed.
    lower : ∃ K:ℝ,∃ j:ℕ, 0≤K∧∀ᶠ r in home, ∀ v, ‖v‖≤ K*Z.Λ r^j*∑ T∈W, ‖b T 0 r v‖
structure ProbesAt {D:ℕ} (A:Ports C) (Z:Ledger L) (W:Finset (Stud C D)) (p:ℕ) : Prop where
    uses : ∀ T∈W,∀ v:Slot C D, Returns Z A (T.twins v) 0 (tsupport T.test) p ∧ VacuumCompat Z A (T.twins v) (tsupport T.test) p

variable {A:Ports C}{W:Finset (Stud C D)}{b: Stud C D → ℕ → ℝ → (Free C D →L[ℂ] ℂ)}
    (loc:Located L) (h:Diagnostics A Z W b p) (hz:ProbesAt A Z W p) {T:Stud C D}
include P H loc hz
lemma probeBills (he:T∈W)(v:s){q:ℕ}(hq:q ≤ p) : Bare Z (q+1) (fun r=> board L T r (input L r D v) - forecast Z q (A.moments (T.twins v)) r T.test) := by
   let K:=tsupport T.test
   obtain ⟨hb,hB⟩:= hz.uses _ he v
   let x : Viewers F × Test 2:=(none,T.test)
   have hk (i:ℕ):∃ a:ℝ,(joins K (Viewers F)).pay i x a:=by
       obtain ⟨A,hA⟩:= demandAccessible i T.test
       exact ⟨A,subset_rfl,hA⟩
   refine ((horizonZero Z P H loc T.test.hasCompactSupport T.fits hq hB hb).incurs x hk).congr ?_
   filter_upwards [positiveLength] with r hr _; rw [board_apply L T r hr,seated L T r]

include h
lemma pivotBills (he:T∈W){q:ℕ}(hq:q≤p) : Bare Z (q+1) (fun r=> panel L T r - accrue Z q (b T) r) := by
   apply pointwiseBare; intro v
   refine ((probeBills Z P H loc hz he (.inr v) hq).add (h.agrees _ he v q hq)).congr (Eventually.of_forall fun r _=> ?_)
   change board L T r (L.frame D r v) - _ + (_-_) = board L T r (L.frame D r v) - _; abel

def Detect {D:ℕ} (Z:Ledger L) (W:Finset (Stud C D)) : Prop :=
    ∃ K:ℝ,∃ j:ℕ,0≤K∧∀ᶠ r in home,∀ v:Free C D,‖v‖ ≤ K*Z.Λ r^j*∑ T∈W, ‖panel L T r v‖

lemma detects : Detect Z W := by
   obtain ⟨K,j,hK,hL⟩:=h.lower
   let x (T:Stud C D) (r:ℝ):= panel L T r - b T 0 r
   have hv (T) (ht:T∈W):Bare Z 1 (x T):=by
       simpa only [x,wt,accrue,Nat.zero_add,Finset.sum_range_one,pow_zero,Complex.ofReal_one,one_smul] using! (pivotBills Z P H loc h hz ht (Nat.zero_le p))
   have hs:Bare Z 1 (fun r=> ∑ T∈W, ‖x T r‖):= Cost.sum (H:=W) (fun i hi=>Cost.transfer (z:=fun r _=> ‖x i r‖) (hv i hi) (Eventually.of_forall fun r _=>norm_norm (x i r)|>.le))
   let z r := K * Z.Λ r^j
   have hp r:0≤z r:=mul_nonneg hK (pow_nonneg (zero_le_one.trans (Z.above r)) _)
   have hE: Bare Z 0 z:= Cost.insert_single K j hK (Eventually.of_forall fun r=>by rw [Real.norm_of_nonneg (hp r),pow_zero,mul_one])
   obtain ⟨c,i,hc,he⟩:= Cost.bound_single (Cost.bareProduct (z:=fun r _=> z r* ∑ T∈W, ‖x T r‖) hE hs (Eventually.of_forall fun r _=>norm_mul_le ..))
   refine ⟨2*K,j,mul_nonneg (by norm_num) hK,?_⟩
   have hm:Tendsto (fun r=> c*Z.g r*Z.Λ r^i) home (𝓝 0):=by simpa only [mul_zero,mul_assoc] using (Z.dominant i).const_mul c
   filter_upwards [hL,he,hm.eventually (gt_mem_nhds (show (0:ℝ)< 1/2 by norm_num))] with r hr h' ht v
   have hT : z r * ∑ T∈W, ‖x T r‖≤ 1/2:= (Real.le_norm_self _).trans (h'.trans ((by simpa using ht.le)))
   have hP(T:Stud C D) : ‖b T 0 r v‖≤ ‖panel L T r v‖+ ‖x T r‖*‖v‖:=by
       refine (le_trans (le_of_eq (congr_arg norm (show b T 0 r v= panel L T r v - x T r v from (sub_sub_cancel ..).symm))) (norm_sub_le ..)).trans (add_le_add_right ((x T r).le_opNorm _) _)
   have hw:= (hr v).trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum («s»:=W) (fun i _=>hP i)) (hp r)); rw [Finset.sum_add_distrib,← Finset.sum_mul,mul_add, ← mul_assoc _ (∑ i∈W, ‖x i r‖)] at hw
   have hx := hw.trans (add_le_add_right (mul_le_mul_of_nonneg_right hT (norm_nonneg v)) (z r * ∑ T∈W, ‖panel L T r v‖))
   unfold z at hx; linarith only [hx]

lemma mixedBills (he:T∈W) (v:C.label D) {q:ℕ}(hp:q ≤ p):Bare Z (q+1) (fun r=>
    panel L T r ((entry L D r - accrue Z q (A.read D) r) v)):=by
   let R j r (_:Unit):= A.read D j r v
   have hv: Cost Z wears (q+1) (fun r _=> panel L T r (entry L D r v) - forecast Z q (combine (b T) R) r ()):=by
       apply ((probeBills Z P H loc hz he (.inl v) hp).add (h.cross _ he v q hp)).congr
       refine Eventually.of_forall fun r _=>?_
       change _= board L T r (L.frame D r ((L.frame D r).symm (master L D r v))) - _
       rw [LinearEquiv.apply_symm_apply]; dsimp only [R,input,Sum.elim]; abel
   have hC: Cost Z wears (q+1) (fun r x => panel L T r (forecast Z q R r x) - forecast Z q (combine (b T) R) r x):=by
       have h': Bare Z 0 (fun _=>v):= Cost.insert_single ‖v‖ 0 (norm_nonneg _) (Eventually.of_forall fun _=>by simp)
       exact Cost.payAt (b:=b T) (v:=R) (fun i hi=> Cost.op (h.readPrice _ (hi.trans hp)) h') (fun i hi=>h.framePrice _ he _ (hi.trans hp))
         ((Cost.zero Z wears _ _).congr (Eventually.of_forall fun _ _=>(sub_self _).symm)) (pivotBills Z P H loc h hz he hp)
   apply (hv.sub hC).congr; refine Eventually.of_forall fun r a=> ?_
   have ht: accrue Z q (A.read D) r v=forecast Z q R r a:=by unfold forecast accrue; rw [ContinuousLinearMap.sum_apply]; rfl
   change _ - forecast _ _ _ _ _ - _ = panel L T r (entry L D r v - accrue Z q (A.read D) r v)
   cases a; rw [ht,map_sub]; abel

lemma columnBill {q:ℕ}(hq:q ≤ p) :Bare Z (q+1) (fun r=> entry L D r - accrue Z q (A.read D) r):=by
   obtain ⟨K,j,hK,hL⟩:= detects Z P H loc h hz
   let z r:= K*Z.Λ r^j; have hp r:0≤z r:=mul_nonneg hK (pow_nonneg (zero_le_one.trans (Z.above r)) _)
   have he:Bare Z 0 z:= Cost.insert_single K j hK (Eventually.of_forall fun r=>by rw [Real.norm_of_nonneg (hp r),pow_zero,mul_one])
   apply pointwiseBare; intro v
   let F' r := (entry L D r - accrue Z q (A.read D) r) v
   have hw : Bare Z (q+1) (fun r=> ∑ T∈W, ‖panel L T r (F' r)‖):=
       Cost.sum (H:=W) (fun i hi=> Cost.transfer (z:=fun r _=> ‖panel L i r (F' r)‖) (mixedBills Z P H loc h hz hi v hq) (Eventually.of_forall fun r _=> norm_norm ..|>.le))
   have hx:= Cost.bareProduct (z:=fun r _=> z r * ∑ T∈W, ‖panel L T r (F' r)‖) he hw (Eventually.of_forall fun r _=> norm_mul_le ..)
   rw [zero_add] at hx; exact hx.transfer (hL.mono fun r hr _=> (hr _).trans (Real.le_norm_self _))
lemma frameBound : RateLE home ρ (fun r=> toFrame L D r) D := by
   obtain ⟨K,j,hK,hL⟩:= detects Z P H loc h hz
   apply pointwiseCoarse; intro v
   let z r:= K* Z.Λ r^j; have hp:RateLE home ρ z 0:= by simpa only [z,mul_zero,zero_add] using (RateLE.const K ageLarge).mul (Z.cheap.pow j ageLarge)
   have hi:= hp.mul (RateLE.sum ageLarge (S:=W) (fun i _ => (rawBoard L P H i loc v).norm)); rw [zero_add] at hi
   refine RateLE.of_norm_le hi (hL.mono fun r hr=> ?_)
   refine (hr (toFrame L D r v)).trans (le_of_eq (congr_arg (z r * ·) (Finset.sum_congr rfl (fun i _=>congr_arg norm ?_))))
   change board L i r (L.frame D r ((L.frame D r).symm v))=_; rw [LinearEquiv.apply_symm_apply]
end YM.RG17

