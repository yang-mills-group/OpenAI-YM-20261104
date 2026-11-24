import YM.OPE.Compatible.Words.Stamp
/-!
# Matrix stockings. natural Lift
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module Matrix Cascade Cascade.Paver
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {I J K:Type}[Fintype I][Fintype J]{n k d:ℕ}
local notation "Λ"=> PAD I
local notation "Γ"=> PAD J
lemma harmon_loose {W:ℕ→Submodule ℝ (Song Λ)}(h:Monotone W){A:End ℝ (Song Λ)}(hp:reduces W A)(t:ℝ)(n k:ℕ) (p:Song Λ)(hx:p∈ W k):fixExp A t n p ∈ W k:=by rw [Hflow]; refine (W k).sum_mem ?_; intro i _; exact (W _).smul_mem _ (h (Nat.sub_le k i) ((iterateD hp hx i).1))
lemma harmonic : Monotone (harmon Λ):= fun a _ hh p hp=> ⟨fun i hi=> (show ∀ i,i>a→p i=0 from hp.1) i (lt_of_le_of_lt hh hi),hp.2⟩
lemma peak {A:Mat I}(t:ℝ)(n k:ℕ)(p:Song Λ)(hp:p∈ harmon Λ k): fixExp (opus A) t n p∈harmon Λ k:=harmon_loose harmonic (by simpa only [one_smul] using opusReducer A 1) t n k p hp
variable {A B X Z: Mat I}{M:Matrix I J ℝ}{D: Mat J}
lemma netscape (p:Song Λ)(h:∀ i:ℕ,Reserve A (p i)) (hp:B=M*D*Mᵀ)
    (hz: ∀ x:Λ,Health A (Z*ᵥ x))(ht:∀ x:Λ,Health A x→Z*ᵥ x=x)(hq:∀ x y:Λ,Health A x→Health A y→x ⬝ᵥ (X*ᵥy)=x ⬝ᵥ(B*ᵥ y)):
    pulling M (opus X p)=opus D (pulling M p):=by
         funext k; change (wind k • Semester X (p (k+2))).compContinuousLinearMap _= wind _ • Semester D ((p (k+2)).compContinuousLinearMap _); rw [busbar A X B Z _ hz ht hq (h _), columnAlong B D M hp]; rfl
lemma OpusCoef {W:Mat I}(x:Song Λ)(he:∀ i:ℕ,Reserve A (x i)) : ∀ i,Reserve A (opus W x i):=by intro i j v a h; change (wind i • Semester _ _) _=0; rw [_root_.smul_apply,(Reserve.hits (x (i+2)) (he (i+2)) W) j v a h, smul_zero]
lemma carriedZ {p:Song Λ}(h:∀ i:ℕ, Reserve A (p i))(hp:B=M*D*Mᵀ)
    (hz: ∀ x:Λ,Health A (Z*ᵥ x))(ht:∀ x:Λ,Health A x→Z*ᵥ x=x)(hq:∀ x y:Λ,Health A x→Health A y→x ⬝ᵥ (X*ᵥy)=x ⬝ᵥ(B*ᵥ y))(t:ℝ) : pulling M (fixExp (opus X) t n p)=fixExp (opus D) t n (pulling M p):=by
         have he(i:ℕ): pulling M ((opus X^i) p)=(opus D^i) (pulling M p) ∧ ∀ j:ℕ,Reserve A (((opus X^i) p) j):=by
              induction i with
              | zero=> simpa
              | succ i ih=> rw [pow_succ',pow_succ',End.mul_apply,End.mul_apply]; exact ⟨(netscape _ ih.2 hp hz ht hq).trans (congr_arg (opus D) ih.1),OpusCoef _ ih.2⟩
         rw [Hflow,Hflow,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul,(he i).1]
-- Wick Clock. sign
lemma switching (t:ℝ)(n:ℕ) : fixExp (-(opus A)) t n=fixExp (opus A) (-t) n:=by
     unfold fixExp; refine Finset.sum_congr rfl ?_; intro i _
     cases i.even_or_odd with
     | inl h=> rw [h.neg_pow t, h.neg_pow (opus A)]
     | inr h=> rw [h.neg_pow t, h.neg_pow (opus A),smul_neg, neg_div]; exact (neg_smul _ _).symm
lemma flavourMinus (A B: Mat I): opus (A-B)= opus A-opus B:=by apply eq_sub_of_add_eq; rw [← flavorDist,sub_add_cancel]
lemma enterV (p:Song Λ)(M:Matrix I J ℝ)(x:Γ)(n:ℕ): Strike n p (M*ᵥ x)=Strike n (pulling M p) x:=rfl
-- Wick natural lemma
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]
variable (μ:Measure E)[μ.IsAddHaarMeasure] (T:Law E) (S:E→L[ℝ] PAD I)
lemma sprouted (p:Song Λ)(u:Γ)(hp:p∈ harmon Λ n)(he:∀ i:ℕ,Reserve A (p i)) (hz: ∀ x:Λ,Health A (Z*ᵥ x))(ht:∀ x:Λ,Health A x→Z*ᵥ x=x)
   (hr:∀ x y:Λ,Health A x→Health A y→x ⬝ᵥ(X*ᵥ y)= (Mᵀ*ᵥ x) ⬝ᵥ(D*ᵥ (Mᵀ*ᵥ y)) +x ⬝ᵥ ((chamber T S)*ᵥ y)):
   T.average μ (fun y=> Strike n (fixExp (opus X) (-(1/2:ℝ)) n p) (M *ᵥ u+S y))= Strike n (fixExp (opus D) (-(1/2:ℝ)) n (pulling M p)) u:=by
        let f:=fixExp (opus X) (-(1/2:ℝ)) n p; have hg:= basisH μ T S (M*ᵥu) 1 f (peak _ _ _ _ hp)
        simp only [one_smul,one_pow] at hg; rw [show _= _ from hg]; let H:= chamber T S
        have hD: ∀ x y:Λ,Health A x→Health A y→x ⬝ᵥ ((X-H)*ᵥ y)= x ⬝ᵥ (((M*D)*Mᵀ)*ᵥ y):=by intro x y h hP; rw [Matrix.sub_mulVec,dotProduct_sub,hr x y h hP,← mulVec_mulVec,← mulVec_mulVec,entrusted M,add_sub_cancel_right]
        have hx:fixExp (opus H) (1/2:ℝ) n f= fixExp (opus (X-H)) (-(1/2:ℝ)) n p:=by
             unfold f; rw [← switching,← switching]; let U:= harmon Λ
             have hb: (-1:ℝ) • opus X= -opus X:= (neg_smul (1:ℝ) (opus X)).trans (by rw [one_smul])
             rw [equations (V:=U) (show reduces U (opus H) from by simpa only [one_smul] using opusReducer H 1) (show reduces U (-opus X) from by simpa only [hb] using opusReducer X (-1)) (fun i q h=> by simpa only [hb,one_smul] using! commuteO q h H X 1 (-1)) p hp (1/2:ℝ) n le_rfl, flavourMinus,show opus H+ -opus X= -(opus X- opus H) from by abel]
        rw [hx,enterV _ M u n,carriedZ he (show M*D*Mᵀ= _ from rfl) hz ht hD]
end YM.OPE.Silt
