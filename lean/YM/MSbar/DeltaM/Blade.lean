import YM.MSbar.DeltaM.Hills
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar MvPolynomial Analysis Bakery Lattice
variable {ι σ τ: Type}[Fintype σ][Fintype ι][Fintype τ][DecidableEq σ][DecidableEq ι][DecidableEq τ]
   {n:Side}{l:σ→ Site n}{x:Site n}{F : View σ→ℝ}{k k' :Matrix σ σ ℝ} {A:Matrix ι ι ℝ} {B :Matrix τ τ ℝ}{φ : Matrix σ ι ℝ}{i : Matrix σ τ ℝ}
    {μ ν: View σ}
local notation "Y!"=>φ*A*φ.transpose
local notation "X!"=>i*B*i.transpose
local notation "P"=> Pot σ
noncomputable def play (L:List σ): Pot σ:= (L.map (fun i=>MvPolynomial.X i)).prod
-- choose uniform for all petals Ω.Pin number.F finite.Fill.Ope.Core. no gauge estimate from polynomial here.
def raffle (p:ℕ)(g : ℝ) := match p with |0=>(1:ℝ)|n+1=> g*raffle n g
-- define Wire currency.Both vector.Axis.World.Jet.Calls
variable {Trea β α v r C u d b a t : ℝ}{S:Finset σ}{m:ℕ} {q:Finset σ}
structure Cash (φ:Matrix σ ι ℝ)(A:Matrix ι ι ℝ)(i:Matrix σ τ ℝ)(B:Matrix τ τ ℝ)(μ ν: View σ) (l:σ→Site n)(F:View σ→ℝ)(v :Site n) (w D a t:ℝ)(k:ℕ)(q:Finset σ): Prop where
    alive : A.PosDef
    able : B.PosDef
    helm : Canopy F
    chances : Gain l v 0 a 0 (φ*A*φ.transpose) (i*B*i.transpose) w D
    budgets : 0≤t
    rent (j:σ) : j∈q→ |μ j| ≤ w ∧ |ν j|≤w ∧ |μ j-ν j|≤ D*w ∧ Eve a v (l j) ≤w
    aim (j:σ)(L:List σ) : L.toFinset⊆q→ L.length≤k→ |pillar φ μ j F (play L) A| ≤ t ∧ |pillar i ν j F (play L) B|≤ t ∧
         |pillar φ μ j F (play L) A - pillar i ν j F (play L) B| ≤ D* Eve a v (l j)*t
-- derivative as sum of lower lists.Ar.
def shake (i:σ) (C: Matrix σ σ ℝ) (L:List σ) (A : List σ → ℝ): ℝ:= match L with
    | []=> 0
    | j::T=> C i j*A T + shake i C T (fun T=> A (j::T))
lemma sift (l:List σ)(i:σ)(C:Matrix σ σ ℝ)(t:P→ₗ[ℝ]ℝ): t (tureen C i (play l))= shake i C l (fun i=> t (play i)):=by
    have hs(Z R : Pot σ): tureen C i (Z*R)=tureen C i Z*R+Z*tureen C i R:=by rw [drink,drink,drink,sum_mul,mul_sum,←sum_add_distrib]; refine sum_congr rfl fun j _=>?_ ; rw [pderiv_mul,smul_add,mul_smul_comm,smul_mul_assoc]
    have hc(v:σ) : (tureen C i) (MvPolynomial.X v)= C i v • (1:P) := by rw [drink]; simp [pderiv_X,Pi.single_apply,smul_ite]
    induction l generalizing t with
    | nil=> simp [play,drink,shake]
    | cons j L ih=>
       let g : P→ₗ[ℝ]ℝ:= t.comp (LinearMap.mul ℝ P (MvPolynomial.X j))
       have hv(L:List σ) : play (j::L)=MvPolynomial.X j*play L:=rfl
       rw [hv,hs,hc,map_add,smul_mul_assoc,one_mul,map_smul,show t (MvPolynomial.X j*tureen C i (play L))=_ from ih g]
       rw [shake]; simp only [smul_eq_mul]; congr
-- stage recursion costs Theta
variable (H:Cash φ A i B μ ν l F x Trea d a t m q)
local notation "L!"=> hint μ φ A F
local notation "C!"=> hint ν i B F
local notation "E!"=> (fun j T=> pillar φ μ j F (play T) A)
local notation "e!"=> (fun j T=> pillar i ν j F (play T) B)
namespace Cash
variable {ι' :σ}
include H
lemma inks (W :Matrix σ ι ℝ)(j:σ):True :=trivial
lemma per_se (j b:σ)(v:j∈q): |(Y!) j b|≤ Trea ∧ |(X!) j b|≤ Trea∧ |(Y!) j b - (X!) j b| ≤Trea*d:= by
    obtain ⟨hc,hV,hW,h₀,h₁,h₂⟩:=H.chances; refine ⟨h₀.single (by linarith : 0≤0+a) j b,h₁.single (by linarith:0≤0+a) j b,?_⟩
    exact (h₂.flip.wet hc j b).trans (mul_le_mul_of_nonneg_right (H.rent j v|>.2.2.2) hW)
-- bound sum over Γ.Pillar
lemma shine (j :σ)(hv:j∈q)(T:List σ)(hb:T.toFinset⊆q)(hp:T.length≤m):
   let D:=∑ i:σ, (φ*A*φ.transpose) j i* pillar φ μ i F (play T) A
   let D':=∑ z:σ,(i*B*i.transpose) j z * pillar i ν z F (play T) B
   |D|≤Trea*t ∧|D'|≤Trea*t∧|D-D'|≤ d*( (Trea*t)+Trea^2*t) :=by
      intro D D'; obtain ⟨hA,ht,hZ,hP,hQ,hE⟩:=H.chances; have hh:= H.budgets
      let s (i k:σ):= Eve a (l i) (l k); have ht₀(i v:σ): liftW (0+a) 0 (separation (l i) (l v))=s i v:=by simp [liftW,Eve,s]
      have hk(p q: Site n): 1≤ Eve a p q:=Real.one_le_exp (mul_nonneg ht (Nat.cast_nonneg _)); let A':= φ*A*φ.transpose; let B':= i* B*i.transpose
      have hm (f : Matrix σ σ ℝ)(h:LoopNet l (0+a) 0 f Trea)(a':σ→ℝ)(hv:∀ i,|a' i|≤ t): |∑ k,f j k *a' k|≤Trea*t:=by
          refine (Finset.abs_sum_le_sum_abs ..).trans (le_trans (b:=(∑ k', |f j k'| *s j k')*t) ?_ ?_); · rw [Finset.sum_mul]; apply sum_le_sum; intro k' _; rw [abs_mul]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (hk ..)) (hv k') (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
          have he:=h.glow j; simp_rw [ht₀] at he; exact mul_le_mul_of_nonneg_right he hh
      let D₀:= fun i:σ=> pillar φ μ i F (play T) A; let D₁:= fun j:σ=>pillar i ν j F (play T) B; let f i:= A' j i*D₀ i; let g i:=B' j i*D₁ i; have hp(i):= H.aim i T hb hp -- shadows. rename
      refine ⟨hm A' hP D₀ (fun i=>(hp i).1),hm B' hQ D₁ (fun i=>hp i|>.2.1),?_⟩
      let N i:= |A' j i-B' j i|; let V(i:σ):= N i*t+ ( (d*Trea*t) * (|B' j i| * s j i)); have he(i:σ): |f i-g i| ≤ V i:=by
          rw [show f i-g i=(A' j i-B' j i)*D₀ i+B' j i*(D₀ i-D₁ i) from (by unfold f g; ring)]
          apply (abs_add_le ..).trans (add_le_add ?_ ?_) -- tactic?
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hp i|>.1) (abs_nonneg _)
          rw [abs_mul]; have ht : Eve a x (l i) ≤ Trea * s j i:= (eve_t ht ..).trans (mul_le_mul_of_nonneg_right (H.rent j hv|>.2.2.2) (Real.exp_pos _).le); exact (mul_le_mul_of_nonneg_left ((hp i|>.2.2).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hZ) hh)) (abs_nonneg _)).trans_eq (by ring)
      have hz := hE.upper j; simp_rw [show ∀ (d:ℕ), liftW 0 0 d=1 from fun i=>by simp [liftW],mul_one] at hz
      change |(∑ i,f i)-∑ i,g i| ≤ _; rw [← sum_sub_distrib]; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=>he i)).trans ?_); unfold V; rw [sum_add_distrib,← sum_mul,← mul_sum]; have he:= hQ.glow j; simp_rw [ht₀] at he; exact (add_le_add (mul_le_mul_of_nonneg_right (hz.trans (mul_le_mul_of_nonneg_right (H.rent j hv|>.2.2.2) hZ)) hh) (mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg hZ hP.hope) hh))).trans_eq (by ring)
end Cash
end YM.MSbar.Kelvin
