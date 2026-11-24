import YM.MS.Osc.Shelter
/-!
# Any order quadrature.E operator budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Osc.Snap
open Set Filter Function Finset Metric MeasureTheory Real
open Momentum Tone Lattice Landau Native
open scoped Topology ContDiff
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [CompleteSpace F]
  {S:Scale I} {x y K:ℝ}{a b:I→ℝ}{f:I→ QP× E→ F}
abbrev fee (S:Scale I)(i:I): ℝ:= (S.length i^4)⁻¹ -- avoid ambiguous
variable (h:pole S f a)(hp:∀ i,0<b i)(hx:0≤K)(hK:∀ i,S.length i*b i≤ K)
include h hp hx hK
lemma quad : Bound S (fun i p=>∫ q,f i (q,p) ∂rail (b i)) (fun i=>a i*fee S i):= h.consumes ( local_p hp hx hK (show 5>4 by omega) ) ( sane h ) (spending hp hx hK (show 5>4 by omega))
omit h hp hx hK [NormedSpace ℝ E] in
lemma tom (S:Scale I)(j:ℕ)(h:j>4) : S.full.Le (fun i (_:E)=>∫ q,S.dust j i q ∂planeF) (fun i _=> fee S i):= by
    convert Reserve.cutoff_mass (S:=S) (μ:=planeF) (F:=E) (D:=fun _=> Set.univ) j (by simpa [QP,Momentum,Axis]) using 1; ext; simp; ext; simp [ QP,Momentum,Axis,fee ]
omit hp hx hK in
lemma quadF : Bound S (fun i p=>∫ q,f i (q,p) ∂planeF) (fun i=>a i*fee S i):= h.consumes ( Tall S 5 (by omega)) (sane h ) (tom _ _ (by omega))
def Sugar (b:I→ℝ)(f:I→QP× E→ F)(i:I)(p:E):= TreeSum (fun q=> f i (q,p)) (b i)
lemma lactose : Bound S (Sugar b f) (fun i=>a i*fee S i):= Costs.sub (quad h hp hx hK) (quadF h)
abbrev Spring (f:I→ QP × E→ F)(k:ℕ)(i:I)(p:E)(q:QP):= iteratedFDeriv ℝ k (fun w:E=> f i (q,w)) p
lemma lactose_s (j:ℕ)(i:I)(p:E) : iteratedFDeriv ℝ j (Sugar b f i) p=TreeSum ( Spring f j i p ) (b i):= by
    have hu:= Rapid.major (local_p hp hx hK (show 5>4 by omega)) h i; have hv:=Rapid.major (Tall S 5 (by omega)) h i;
    change iteratedFDeriv ℝ j (( fun p:E=>∫ q, f i (q,p)∂rail (b i) )-(fun p:E=>∫ q,f i (q,p)∂planeF)) p=_
    rw [iteratedFDeriv_sub_apply ( hu.contDiff.contDiffAt.of_le (by exact_mod_cast le_top) ) ( hv.contDiff.contDiffAt.of_le (by exact_mod_cast le_top)), hu.identity,hv.identity ]
-- iterate whole I by explicit induction binder universal. norm integral.No derivative of shell required.
omit hK h hp hx in
lemma nods (k:ℕ){F:Type}[NormedAddCommGroup F][NormedSpace ℝ F] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace F]: ∀ (I:Type)(S:Scale I)(f:I→ QP × E→ F)(a b:I→ℝ), pole S f a→ (∀ i,0<b i)→(0≤K)→ (∀ i,S.length i * b i ≤ K) → Bound S (Sugar b f) (fun i=> a i*fee S i* ( S.length i*b i)^k ) := by
   induction k with
   | zero=> intro I S f a b hf hp hx hK; simpa using lactose hf hp hx hK
   | succ k ih=>
      intro I S f a b hf hp hx hK; let J:= Σ i:I,{p:QP // ‖p‖≤b i}; let P:J→I:= Sigma.fst; let Y:= borrow S P; let W:J→ℝ:=fun i=>a (P i)* (S.length (P i)*b (P i)); let Q:J→QP:= fun i=>i.2.val; let F' : J→ QP × E→F:= fun i=> f (P i); let G:= shift Q F'; let U : J→ℝ:= b∘P
      have he: pole Y F' (a∘P):= by
          intro k; refine ⟨fun i=>(hf k).smooth (P i),fun i=>?_⟩; obtain ⟨C,hC,w,hW⟩:= (hf k).quoted i; exact ⟨ C,hC,w,fun i p hx=> hW (P i) p hx⟩
      have hsub(i:J): ‖Q i‖ ≤ b (P i):= i.2.property; have hM(i:J): Y.length i *‖Q i‖ ≤ S.length ( P i ) * b ( P i ):= mul_le_mul_of_nonneg_left (hsub i) (Y.pos i|>.le)
      have hD:= Osc.step he (fun i=> (hM i).trans (hK (P i))) hx; have hG:pole Y G W:= Rapid.monotone hD ( Cost.of_le fun i _ _=> mul_le_mul_of_nonneg_left ( hM i ) (sane he i));
      have hI : Bound Y (Sugar U G) (fun i=> W i*fee Y i*(Y.length i*U i)^k):= ih J Y G W U hG (fun i=> hp _) hx (fun i=> hK (P i)); have hL:= lactose hf hp hx hK;
      refine ⟨ hL.smooth, fun j=>?_⟩; obtain ⟨C,hC,o,hO⟩:= hI.quoted j; refine ⟨C,hC,o,fun i p hu=>?_⟩; dsimp only; rw [lactose_s hf hp hx hK];
      haveI: IsProbabilityMeasure (region (b i)):= μprob (hp i); let Z:= C*S.full.cheap i p^o*( (a i*fee S i*( S.length i * b i)^(k+1))* S.length i^j)
      rw [ tree_avg (hp i) ((Rapid.major ( Tall S 5 (by omega)) hf i).integ j p) ( (Rapid.major ( local_p hp hx hK (show 5>4 by omega) ) hf i).integ j p) ]; apply (norm_integral_le_of_norm_le (integrable_const Z) ?_)|>.trans_eq; · simp; rfl
      refine (rounding (hp i)).mono fun q hq=>?_ ; let I': J:=⟨i,q,hq⟩; have ht:= hO I' p trivial; dsimp only at ht; rw [lactose_s hG (b:=U) (fun i=>hp _) hx (fun i=> hK (P i)) ] at ht;
      rw [show (fun x=> Spring f j i p x-Spring f j i p (x+q))= Spring G j I' p from ?_]; exact ht.trans_eq (by change C*S.full.cheap i p^o * (( a i*( S.length i*b i) *fee S i*(S.length i*b i)^k)*S.length i^j) = Z; unfold Z; rw [pow_succ]; ring)
      funext z; have hu(x:QP) : ContDiff ℝ j (fun p:E=> f i (x,p)):= ( (hf.smooth i).comp (f:=fun p:E=> (x,p)) (by fun_prop)|>.of_le (by exact_mod_cast le_top)); unfold Spring; rw [show (fun w:E=> G I' (z,w))= (fun w:E=> f i (z,w)) - (fun w:E=> f i (z+q,w)) from funext fun p=> by unfold G Osc.shift; simp; rfl]; exact Eq.symm ( iteratedFDeriv_sub_apply (hu _).contDiffAt (hu _).contDiffAt ) -- placeholder rfl?
lemma funds (k:ℕ): Bound S (Sugar b f) (fun i=> a i * fee S i*( S.length i*b i)^k):= nods k I S f a b h hp hx hK
end YM.MS.Osc.Snap
