import YM.FVAAlt2.RealPlane
import YM.FVAAlt2.Hessian
import YM.FVAAlt2.SuperEnd

/-! The propagator induced from the explicit MS matrix is exactly the Landau
Gaussian and mean-zero Grassmann propagator, with antighost-conjugate basis
as in `Land.lean`. Factors 1/2 and precision normalization are essential.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Native MS.Plane MS.Book MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl MS.Swirl.Near MS.Native.Wilsonian MS.Cylinder MS.Cylinder.Lab
open Function Lattice Finset Matrix SchemeRG11.Sway Pert.Orb

variable {G:Gauge}{n:Side}
local notation "S" => Site n
local notation "A" => Mode G n
local notation "M" => QuotK G n
local notation "p" => Draft.DotFlip
local notation "H" => posHessian G n
local notation "F" => fourier G n
local notation "P" => posCov G n true
local notation "ℙ" => (2:ℂ) • posCov G n true

lemma inv4L (t : A→ℂ): ∃ s,(F)ᵀ *ᵥ s=t := ⟨(backwards G n).transpose *ᵥ t,by rw [Matrix.mulVec_mulVec,← transpose_mul,backwards_fourier,transpose_one,Matrix.one_mulVec]⟩
lemma inv4R (t : A→ℂ): ∃ s,(F) *ᵥ s=t:= ⟨backwards G n *ᵥ t,by rw [Matrix.mulVec_mulVec,fourier_back,Matrix.one_mulVec]⟩
lemma range_pos (t:A→ℂ): (∃ u,P *ᵥ u=t) ↔ SpaceField n t:= by
  obtain ⟨t,rfl⟩:= inv4L t; change (∃ u,(pullCov M F)*ᵥ u=_ )↔_
  unfold SpaceField pullCov; rw [← sample_range t, ← mirror_sampled t,← Quotient_range]
  simp_rw [mul_assoc,←Matrix.mulVec_mulVec]; constructor
  · rintro ⟨u,hu⟩; exact ⟨_, inverse_inj hu⟩
  rintro ⟨u,hu⟩; obtain ⟨s,h⟩:= inv4R u; exact ⟨s,by rw [h,hu]⟩

lemma green_t (n:Side)(G:Gauge) :
    let C': Matrix (Mode G n) (Mode G n) ℂ := (2:ℂ) • QuotK G n
    C' * ((fourier G n) * posHessian G n * (fourier G n).transpose) * C' = -C' := by
  intro C'
  let V:= (1/2:ℂ) • docket n (Wilsonian.core G 0)
  rw [show (fourier G n) * posHessian G n * (fourier G n).transpose = pairMatrix (pull (fourier G n) V) from Eq.symm (pull_pairMatrix ..)]
  have he : pull (fourier G n) V=pay true • flatH G n:=by
     unfold V; rw [map_smul]; change (1/2:ℂ) • pull (fourier G n) (sumHome (shown n (Wilsonian.core G 0))).val=_; rw [all_bulk]; change ((1/2:ℂ) • flatH G n)=_; simp [pay]
  rw [he]; ext x y; obtain hv:= planeS (G:=G) (n:=n) (b:=true) (fun _=>1)|>.reads x y
  simp only [Function.comp_apply,one_mul, neg_mul] at hv
  simp_rw [Matrix.mul_apply,Finset.sum_mul]; rw [Finset.sum_comm]; exact hv

lemma green_pos : (ℙ) * H * (ℙ) = -(ℙ) := by
  let C': Matrix A A ℂ := (2:ℂ) • M; have he : ℙ=(F).transpose*C'*F:=by
     change _ • ((F).transpose* M*F)=_; rw [mul_smul_comm, smul_mul_assoc] -- orientation
  rw [he]; calc
    _ = (F).transpose * (C' * (F*H*(F).transpose) * C') * F:= by simp only [mul_assoc]
    _ = _:= by rw [green_t]; simp only [mul_neg,neg_mul]; rfl

lemma pull_odd (j:A)(i:A) : (P) j i= cross true (p i)* (P) i j:= by
  unfold posCov pullCov
  let T : Matrix A A ℂ:= QuotK G n
  have hv(x y:A): F x i * T y x * F y j = cross true (p i)*( F x i*T x y * F y j):= by
     by_cases h: F x i=0; · simp [h]
     by_cases hl:T x y=0
     · have hx:T y x=0:= by rw [show T y x= cross (p y) (p x)*T x y from paySym (G:=G) (n:=n) true y x,hl,mul_zero]
       simp [hl,hx]
     have hx : p x=p y:= zeroM (G:=G) (n:=n) true _ _ hl; have hi : p i=p x:= fourier_Tie n G _ _ h
     rw [show T y x=cross (p y) (p x)* T x y from paySym true y x,← hx,hi]; cases hq:(p x) <;> simp -- inference
  change ((F).transpose*T*F) j i=_ * ((F).transpose*T*F) i j
  simp_rw [Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_comm]; apply sum_congr rfl; intro x hx; apply sum_congr rfl; intro y _; dsimp only [Matrix.transpose_apply]; rw [← hv y x]; ring

section rankLemma
variable {I J:Type} [Fintype I] [Fintype J]
lemma column_condition (T:Matrix I J ℂ)(K:Matrix I I ℂ)
    (h:∀ u, ∃ f,T *ᵥ f=K.transpose *ᵥ u): ∃ E:Matrix I J ℂ, K=E*T.transpose:= by
  classical
  choose V hV using h; let Z:J→ I →ℂ:=fun j i=> V (Pi.single i 1) j; refine ⟨ (show Matrix I J ℂ from fun i j=> Z j i),?_⟩; ext i j
  have hh:= congrFun (hV (Pi.single i 1)) j; rw [mulVec_single_one] at hh; rw [Matrix.mul_apply]; change K i j=∑ k, Z k i*T j k; rw [← show ∑ k,T j k*Z k i=K i j from hh]; exact sum_congr rfl fun k _=> mul_comm ..
lemma uniqueness_cov {K C : Matrix I I ℂ}
    {Jt Y : Matrix J J ℂ} [DecidableEq J] (T : Matrix J I ℂ)(h:∀ x:J→ℂ,∃ u, K *ᵥ u=T.transpose *ᵥ x) (hp:∀ u,∃ v,T.transpose *ᵥ v=K.transpose *ᵥ u) (hx:K*C*K= -K)(hv:T*C*T.transpose=Jt) (hy:Jt*Y= -1): K=T.transpose*Y*T:=by
  have hi: K*C*T.transpose= -T.transpose:= by
     apply Matrix.ext_of_mulVec_single; intro i
     obtain ⟨x,hx'⟩:= h (Pi.single i 1); rw [← mulVec_mulVec, Matrix.neg_mulVec, ← hx',mulVec_mulVec,hx,Matrix.neg_mulVec]
  obtain ⟨E,hE⟩:= column_condition T.transpose K hp; rw [transpose_transpose] at hE; rw [hE, Matrix.mul_assoc E, Matrix.mul_assoc E, hv] at hi -- orientation
  have he:= congrArg (· * Y) hi; change E*Jt*Y = (-Tᵀ)*Y at he; rw [Matrix.mul_assoc,hy,Matrix.mul_neg,Matrix.mul_one,Matrix.neg_mul] at he; rw [hE,neg_inj.mp he]
end rankLemma
variable {ι κ:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A' : Module.Basis ι ℝ (Land G n)) (b : Module.Basis κ ℝ (ScalarGhost G n))

local notation "L" => embeddingM A' b
lemma rankC (f:A→ℂ) : (∃ u,(ℙ)*ᵥ u=f)↔ ∃ v,(L).transpose *ᵥ v=f:= by
  rw [← realizes_fields A' b,← range_pos]
  constructor
  · rintro ⟨u,rfl⟩; exact ⟨(2:ℂ) • u,by rw [Matrix.mulVec_smul,Matrix.smul_mulVec]⟩ -- 2 ℂ
  rintro ⟨u,rfl⟩; exact ⟨(1/2:ℂ) • u,by rw [Matrix.smul_mulVec,Matrix.mulVec_smul, smul_smul]; norm_num⟩
lemma rankCT (f:A→ℂ) : ∃ u,(L).transpose *ᵥ u=(ℙ).transpose *ᵥ f:= by
  apply (rankC A' b _).1; refine ⟨fun x=> cross true (p x)*f x,?_⟩; ext1 j; unfold Matrix.mulVec dotProduct;
  apply Finset.sum_congr rfl; intro i _; simp only [Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul]; -- orientation P i j needs P_odd? P i j = cross true (p j)*; alternatively cross true (p i) times via ±. 
  rw [pull_odd j i]; cases hr : p i <;> simp

theorem slice_covariance : ℙ=(L).transpose * Rcov A' * L := by
  apply uniqueness_cov (T:=L) _ ?_ (green_pos (n:=n) (G:=G)) (RGHpair A' b) (Rinverse A') -- args
  exacts [ fun v=> (rankC A' b _).2 ⟨v,rfl⟩,rankCT A' b]

abbrev propagator (A':Module.Basis ι ℝ (Land G n)) : Matrix (Alpha ι κ) (Alpha ι κ) ℂ := (1/2:ℂ) • Rcov A'
lemma desired_c : pullCov (propagator A') L=P := by
  unfold pullCov propagator; rw [Matrix.mul_smul,Matrix.smul_mul,← slice_covariance A' b, smul_smul]; norm_num

-- All-orders fixed-regulator reduction to the actual slice, no analytic estimates after this point
open MS.Puff.Mom MS.Puff.Actors MS.Fleet 
variable {W:Type}[LinearOrder W]

/-- SuperEnd after the Landau slice restriction. Quantifies full MS moments at the
same norm and combination conventions, not separate-normalized mark-by-mark; *all*
arities/all polynomial degrees. Includes actual terminal quotient cov.
Still need: integrate fermions & match analytic stencils. -/
theorem slice_end (t : Program.Team) (z:ℝ)(c: W→ Cover)(u:Cover)
    (V: W→ Actor G) (hs:∀ w i,Symm p (V w z i).val) (hu:∀ w i, ∃ k:ℤ,Limit (V w z i).val k) (s:Finset W)(Z:ℕ→ℂ): PhysicalSum G t z n true s c u V Z ↔
      Endμ (propagator A') isOdd
        (pullSeries L (posEnergy (style G (Stripped t) z) n true))
        (pullSeries L (Font p (stencil (fun w=> V w z) (fun w=>wrap n (u+c w))) s)) Z:= by
  rw [superEnd V _ _ _ hs hu s t true Z,end_pull (embTie A' b) _ (Γ_posStyle _ _ _) (fontΓ (Γ_stencil _ _ hs hu)),desired_c]
end YM.FVAAlt2
