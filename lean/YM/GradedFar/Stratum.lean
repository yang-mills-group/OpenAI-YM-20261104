import YM.OPE.Orbits.System
/-!
# The physical graded basis in the proof (one fixed Reader)

Used for the *field prices*, not guessed powers of some scale by slot.
No matched MS dictionary assumed for this basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
variable (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {q m h:ℕ}
abbrev Cast (h:ℕ) := (j:Fin (h+1)) × R.channels j.val
namespace Cast
def cost (p:Cast F R h) := p.fst.val
lemma costs (p:Cast F R h) : p.cost F R ≤ h := Nat.le_of_lt_succ p.fst.isLt
def push (q:Cast F R h): S.Field h:= F.sector.derivatives.rise (q.costs F R) (R.actor (q.cost F R) q.snd)
def stratum (j:ℕ) := (R.cutTest j h).codRestrict (R.stratum j) (fun _=> R.knife_mem j _)
def judge (p:Cast F R h): S.Field h→ₗ[ℂ] ℂ:= ((R.basis (p.cost F R)).coord p.snd) ∘ₗ Cast.stratum F R (p.cost F R)
lemma coefficient (p q:Cast F R h) : judge F R q (push F R p)=if q=p then 1 else 0:=by
  rcases p with ⟨⟨j,hj⟩,p⟩; rcases q with ⟨⟨i,hi⟩,q⟩
  change (R.basis i).coord q ((Cast.stratum F R i) (F.sector.derivatives.rise (d:=j) (e:=h) _ (R.actor j p)))=_
  by_cases he:i=j
  · subst j
    rw [show Cast.stratum F R _ (F.sector.derivatives.rise (d:=i) (e:=h) _ (R.actor i p))=R.basis i p from Subtype.ext
       (Eq.trans (R.cut_rise ..) (R.test_fixes i _ (R.basis i p).property))]
    by_cases hp:q=p
    · subst q; simp
    · simp [hp]
  rw [show Cast.stratum F R _ (F.sector.derivatives.rise (d:=j) (e:=h) _ (R.actor j p))=0 from Subtype.ext
     (Eq.trans (R.cut_rise ..) (R.test_orthogonal i j _ (R.basis j p).property he)), map_zero, if_neg]
  intro H; exact he (congrArg (cost F R) H)
lemma produce (v:S.Field h): ∑ i:Cast F R h, judge F R i v • push F R i = v:= by
  -- later via mathlib sum_sigma'
  have ht:= R.reconstruct h h le_rfl v; rw [F.sector.derivatives.arrival R.continuum.laws.toSymmetric R.lifts v] at ht
  apply Eq.trans _ ht; rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl; intro i hi
  have e:= congrArg (F.sector.derivatives.rise (Nat.le_of_lt_succ i.isLt) ∘ₗ (R.stratum i.val).subtype)
     ((R.basis i.val).sum_repr (Cast.stratum F R i.val v))
  simp only [map_sum,map_smul] at e; exact e
lemma independent : LinearIndependent ℂ (push F R (h:=h)) := by
  apply Fintype.linearIndependent_iff.mpr; intro z hz i
  have hf:= congrArg (judge F R i) hz
  simpa only [map_sum,map_smul,map_zero,coefficient, smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,if_true] using hf

def role (h:ℕ): Module.Basis (Cast F R h) ℂ (S.Field h):= Module.Basis.mk (independent F R) (fun x _=>by
  rw [← produce F R x]; apply _root_.sum_mem; intro i _; exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self _)))
@[simp] lemma role_apply (p:Cast F R h) : role F R h p=push F R p:= by simp [role]
lemma packet_judged {I:Type}[Fintype I]{d:I→ℕ} (p:Cast F R h)(x:I→E4)(u:Labels S d)(o:E4) : judge F R p (R.packet h x u o)=R.coef (p.cost F R) p.snd x u o:= by
  apply congrArg ((R.basis _).coord p.snd); exact Subtype.ext (R.filtered_packet _ h (costs F R p) x u o)

-- the D_r of this physical fixed presentation (used paired with H in G2)
def lift (d:ℕ)(r:ℝ): S.Field d →ₗ[ℂ] S.Field d := ∑ j:Cast F R d, (judge F R j).smulRight (((r:ℂ)^(cost F R j)) • push F R j)
lemma lift_apply (r:ℝ)(p:Cast F R h): lift F R h r (push F R p)= ((r:ℂ)^(cost F R p)) • push F R p:=by
  rw [lift,LinearMap.sum_apply,Finset.sum_eq_single p]; simp [coefficient]
  · intro q _ h; rw [LinearMap.smulRight_apply,coefficient,if_neg h,zero_smul]
  exact fun h=>False.elim (h (Finset.mem_univ ..))
lemma lift_one (v:S.Field h): lift F R h 1 v=v:=by
  conv_lhs=>rw [← produce F R v]
  rw [map_sum]; simp_rw [map_smul,lift_apply]
  simp only [Complex.ofReal_one,one_pow,one_smul]; exact produce F R v
lemma lift_mul (r t:ℝ) : (lift F R h r).comp (lift F R h t)=lift F R h (r*t):=by
  apply (role F R h).ext ; intro i; rw [role_apply,LinearMap.comp_apply,lift_apply,map_smul,lift_apply,lift_apply,
     smul_smul,Complex.ofReal_mul,mul_pow,mul_comm (_^ cost ..)]
lemma lifted_grade {r:ℝ} (v:S.Field h) (p:Cast F R h): judge F R p (lift F R h r v)=((r:ℂ)^cost F R p)*judge F R p v:= by
  rw [lift,LinearMap.sum_apply,map_sum,Finset.sum_eq_single p]
  · simp only [LinearMap.smulRight_apply,map_smul,coefficient,if_true,smul_eq_mul,mul_one]; ring
  · intro i _ hi; rw [LinearMap.smulRight_apply,map_smul,map_smul,coefficient,if_neg (Ne.symm hi),smul_zero,smul_zero]
  exact fun h=>False.elim (h (Finset.mem_univ ..))
end Cast
end YM.Integration.GradedFar.Fork
