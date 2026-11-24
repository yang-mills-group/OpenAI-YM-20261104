import YM.FormalOPE.RG10.Position.Polys
/-! # Coefficient cost of adjusted scale dilations.
No matching-stencil boundedness derived from here before converting the raw stencils.
`relocation` requires the pre-adjusted scale law; here assuming only continuity of the
**formal** jets supplied and group laws, derive budget polynomial in log(T). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J K:Type*} {g:Flow} {w:J→ℕ} [Fintype J] [DecidableEq J]

namespace Cycle
variable (h: Cycle g)
include h
lemma progress (s t:ℝ): g.psi (s+t)=g.warp t (g.psi s):=by
 have hv s : g.psi s=g.warp s X:= by rw [Flow.warped,PowerSeries.subst_X (by exact Triangle.good _ (g.interior _))]
 rw [hv (s+t),hv s,← RingHom.comp_apply,h.uses,add_comm]
lemma steady (hm:∀ n, Continuous (fun s=>coeff n (g.psi s))) (n : ℕ) : Polys (fun s=>coeff n (g.psi s)) := by
 induction n using Nat.strong_induction_on with
 | _ n ih=>
   have he (t:ℝ) : Polys (fun s=> coeff n (g.psi (s+t))-coeff n (g.psi s)):=by
     simp_rw [h.progress (t:=t),g.through, add_sub_cancel_left]; apply Polys.sum; intro i hi; exact (ih i (mem_range.mp hi)).muls (Polys.const _)
   exact Polys.steps (hm n) (he 1) (he (-1)) -- defeq?
end Cycle

variable (Y:Passe g w)
namespace Passe
/-- `check B_t` scale dilation, without the engineering. -/
def lift (t:ℝ) := (Matrix.diagonal (fun i=> C (Real.exp (t*w i)))) * Y.drive t
lemma lift_apply (t:ℝ)(i j:J):Y.lift t i j = C (Real.exp (t*w i)) * Y.drive t i j := by unfold Passe.lift; simp
lemma lift_base (t:ℝ): stamp (Y.lift t) 0=1 := by
 ext i j; rw [stamp_apply, Y.lift_apply,coeff_C_mul, ← stamp_apply, Y.stationed,stone]; by_cases h:i=j<;> simp [Matrix.one_apply,h,Real.exp_neg]
lemma lift_entrance (t:ℝ)(i j:J): Y.drive t i j = C (Real.exp (-t*w i))*Y.lift t i j := by
 rw [Y.lift_apply,← mul_assoc,← map_mul,neg_mul,Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne',map_one,one_mul]
lemma lift_layer (t:ℝ): Layer w (Y.lift t) := fun i j hv=> by rw [Y.lift_apply,Y.station_block t i j hv,mul_zero]
lemma lift_group (t s:ℝ): ((Y.lift t).map (g.warp s))*Y.lift s=Y.lift (t+s):= by
 let B t:= Matrix.diagonal (fun i=> C (Real.exp (t*w i))); have he:(B t).map (g.warp s)=B t:= by
   ext i j:1; by_cases hi:i=j<;> simp [B,hi,g.at_const]
 have hh : B t*B s=B (t+s) := by
   unfold B; rw [Matrix.diagonal_mul_diagonal]; ext i j:1; by_cases hi:i=j <;> simp [hi,add_mul, Real.exp_add]
 have hp : (Y.drive t).map (g.warp s)*B s=B s*(Y.drive t).map (g.warp s):= by
   ext i j:1; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases h:w i=w j
   · simp only [h,mul_comm (C _)]; -- orientation
   simp [Y.station_block t i j h]
 unfold Passe.lift; rw [Matrix.map_mul];
 change (B t).map (g.warp s)*_* (B s *_) = B (t+s)*_
 rw [he,mul_assoc,← mul_assoc _ (B s),hp,mul_assoc (B s),Y.station_law,← mul_assoc,hh]
private lemma clipped {M:ℝ→Matrix J J fps} {P:Matrix J J fps} (θ:ℝ)(n) (hm:stamp P 0=1)
    (hr:∀ i<n,∀ j k, Polys (fun t=>coeff i (M t j k))) (j k:J):
    Polys (fun t=> coeff n (((M t).map (g.warp θ) *P) j k)-coeff n (M t j k)) := by
 let S := Finset.HasAntidiagonal.antidiagonal n; let S':= S.erase (n,0)
 let f (a:ℕ×ℕ) (t:ℝ) := ∑ i, coeff a.1 (g.warp θ (M t j i))* coeff a.2 (P i k)
 have hw : ∀ t, coeff n (((M t).map (g.warp θ) *P) j k) = coeff n (g.warp θ (M t j k)) + ∑ a∈ S',f a t := by
    intro t; rw [← stamp_apply, Retry.stamped, ← Finset.add_sum_erase S (f:=fun a=>stamp ((M t).map (g.warp θ)) a.1 * stamp P a.2) (a:=(n,0)) (mem_antidiagonal.mpr (show n+0=n from by omega))]; -- inspect
    simp only [hm,f,S',S,Matrix.sum_apply,Matrix.mul_apply,stamp_apply,Matrix.map_apply, Matrix.add_apply,mul_one]
 have hx (a i t) : coeff a (g.warp θ (M t j i))=coeff a (M t j i)+(∑ b∈range a,coeff b (M t j i)*coeff a (g.psi θ ^ b)):=g.through ..
 have hl (i) {a} (hn:a ≤ n) : Polys (fun t=> ∑ b∈range a, coeff b (M t j i)*coeff a (g.psi θ ^ b)) := Polys.sum _ _ fun l hl=> (hr l ((mem_range.mp hl).trans_le hn) ..).muls (Polys.const _)
 have hz : Polys (fun t=> ∑ a∈S',f a t):= by
   apply Polys.sum; intro a ha; have hi : a.1 < n:= by obtain ⟨hm,hp⟩:= mem_erase.mp ha; obtain hr:= mem_antidiagonal.mp hp; grind
   unfold f; simp_rw [hx]; apply Polys.sum; intro y _; exact ((hr a.1 hi ..).added (hl _ hi.le)).muls (Polys.const _)
 simp_rw [hw,hx,add_assoc,add_sub_cancel_left]; exact (hl k le_rfl).added hz

lemma uniform_lift (hm : ∀ n (j k:J), Continuous (fun s=> coeff n (Y.train s j k))) (n:ℕ) : ∀ i j, Polys (fun t=>coeff n (Y.lift t i j)) := by
 induction n using Nat.strong_induction_on with
 | _ n ih=>
    intro i j; have he (s:ℝ) : Polys (fun x=> coeff n (Y.lift (x+s) i j)-coeff n (Y.lift x i j)):= by
      simp_rw [← Y.lift_group (s:=s)]; exact clipped _ _ (lift_base Y s) ih _ _
    apply Polys.steps ?_ (he 1) (he (-1)); simp_rw [Y.lift_apply,coeff_C_mul]
    by_cases h:w i=w j
    · unfold Passe.drive tile; simp only [Matrix.of_apply,h,if_true]; exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul (hm n i j)
    simp_rw [station_block Y _ i j h,map_zero,mul_zero]; exact continuous_const
end Passe
namespace Cycle
variable (E: Cycle g)(hc:∀ n, Continuous (fun s=>coeff n (g.psi s)))
private lemma multiplied (a b:ℝ→ fps) (ha:∀ n,Polys (fun s=>coeff n (a s)))(hb:∀ n,Polys (fun s=>coeff n (b s))) (n:ℕ): Polys (fun s=>coeff n (a s*b s)):= by
  simp_rw [coeff_mul]; exact Polys.sum (fun _ s=>_) _ (fun k _=> (ha k.1).muls (hb k.2))
include E hc
lemma wheels (a:ℕ) (n:ℕ): Polys (fun s=> coeff n (g.psi s ^ a)):= by
 induction a generalizing n with
 | zero=> simp_rw [pow_zero]; exact Polys.const _
 | succ a ih=> simp_rw [pow_succ]; exact multiplied _ _ ih (Cycle.steady E hc) n
lemma fares {f:ℝ→fps} {n} (ht:∀ i≤n,Polys (fun s=>coeff i (f s))): Polys (fun s=>coeff n (g.warp s (f s))):= by
 simp_rw [Flow.through]; apply Polys.added (ht n le_rfl) (Polys.sum _ _ fun i hi=> Polys.muls (ht i (mem_range.mp hi |>.le)) (wheels E hc i n))
end Cycle
end YM.FormalOPE.RG10.Position.Grade
