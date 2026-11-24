import YM.FVA2.Graph
import YM.FVA2.FlatComparison

/-!
# Based LPT exponent: every coefficient closed
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Ends
open Finset Function Set Filter Matrix MeasureTheory MS MS.Koszul MS.Book MS.Book.Convolve
open MS.Bare MS.Bare.Maurer MS.Cylinder MS.Native MS.Swirl MS.Orbit MS.Orbit.LogReal
open MS.Puff MS.Puff.Actors MS.Puff.Mom MS.Cylinder.Taylor
open Letter Inserted
open scoped Topology ContDiff

variable {P A : Type} (R : FVA2.Ends A P) (G : Gauge) [DecidableEq P] [DecidableEq A]
  [Fintype P][Fintype A]
variable {G}
variable (S : Links G A → ℝ)

local notation "Φ" => R.locus (G:=G)
local notation "θ" => focus (Z G A) (Z G P)
local notation "Ω" => (glowGraph (A:=A) (P:=P) (G:=G))
local notation "α" => tangentVec (A:=A) (P:=P) (G:=G)
local notation "λΛ" => colorTerm G P
local notation "ΔΔ" => Letter.Δ (X:=Z G A) (Y:=Z G P)
local notation "pp" => (@Letter.p (Z G A) (Z G P))
local infixl:70 " ⋄ " => product pp

/-- Full action before perturbation and removal of quantum quadratic.
S is the *exponent sign*, not the positive energy cost. -/
def actionBody : Raw (Alphabet G A P) ℂ := Focus.Sourced S λΛ Φ Ω

lemma action_ghost : R.actionBody S = ink α S +
    ((∑ i:Z G A, atLetter (Letter.k i) ⋄ Focus.stone Ω Φ i) -
      ∑ j : Z G P, atLetter (Letter.b j) ⋄ Focus.shadow θ λΛ j) := by
  unfold actionBody Focus.Sourced Bonded.hung
  rw [Fintype.sum_sum_type]
  have he (i:Z G A) : Focus.launch Ω λΛ Φ (Sum.inl i)= Focus.stone Ω Φ i:= Focus.launch_stone ..
  have hu (v:Z G P) : Focus.launch Ω λΛ Φ (Sum.inr v)= Focus.shadow _ _ v:= Focus.launch_shadow ..
  simp_rw [he,hu,show ∀ i:Z G A, ((bond (Z G A) (Z G P)).fee (.inl i):ℂ)=1 from fun _=>rfl,
    show ∀ i:Z G P, ((bond (Z G A) (Z G P)).fee (.inr i):ℂ)=-1 from fun _=>rfl, one_smul, neg_smul,
    one_smul, Finset.sum_neg_distrib,sub_eq_add_neg]; rfl

lemma stone_terms (i : Z G A) : Focus.stone Ω Φ i =
    ∑ j:Z G P, atLetter (Letter.c j) ⋄ ink α ((projector i) ∘ R.locus j) := rfl

structure Action : Prop where
  base : S 0=0
  prime : fderiv ℝ S 0=0
  smooth : germ S
  inert : Focus.Inert Φ S

abbrev HaarBody (P : Type) (G : Gauge) (A : Type) [DecidableEq A] [Fintype A] :=
  ink (tangentVec (A:=A) (P:=P) (G:=G)) measure_term
local notation "Y" => HaarBody P G A
local notation "X" => R.actionBody S

def total := rankLevel 2 X + rankLevel 0 Y
local notation "F" => R.total S

lemma action_even : Pure pp false X :=
  (ink_p _ (Ω).never _).add (Focus.lifting Ω λΛ Φ R.smooth_locus).acted_e

lemma action_s (h : germ S) : Symm pp X :=
  (ink_s _ (Ω).never h).add (Focus.lifting Ω λΛ Φ R.smooth_locus).acted_s

lemma total_start : F 0 = Book.mask 2 X := by
  simp only [total, Pi.add_apply, rankLevel, Nat.cast_zero, add_zero,zero_add,add_eq_left]
  funext l; cases l
  · rw [enough _ (h:=0) (by simp : (([]:List (Alphabet G A P)).length:ℤ)=0)]; have hx : measure_term (0:Links G A) = 0 := by
      simp [measure_term,lac,LocalH.spin_zero]
    change ((measure_term (0:Links G A):ℝ):ℂ) = 0; simp only [hx,Complex.ofReal_zero]
  exact strange _ (by simp; omega)


variable {S} (H : Action R S)

lemma from_ghost : From (X-ink α S) 2 := by
  rw [action_ghost,add_sub_cancel_left,sub_eq_add_neg, ← neg_one_smul ℂ]
  have ht (v: Alphabet G A P) : From (atLetter v (R:=ℂ)) 1 := by
    rintro (_|a) ha; rfl; simp at ha; omega
  have hv (u : Z G A) : From (Focus.stone Ω Φ u) 1 := by
    rw [stone_terms]; refine From.sum _ (fun i _ => ?_)
    exact (ht _).pair (hx:=0) (fun l hl=> (by omega))
  have hU (v : Z G P) : From (Focus.shadow θ λΛ v) 1 := by
    unfold Focus.shadow; refine From.sum _ (fun i _=> From.sum _ (fun j _=> ?_))
    apply From.smul; intro l hl
    exact (ht _|>.pair (ht _)) l (by omega)
  apply From.add; exact From.sum _ (fun i _=> (ht _).pair (hv i));
  exact From.smul _ (From.sum _ fun i _=> (ht _).pair (hU i))

include H
lemma from_action : From X 2 := by
  have hs : From (ink α S) 2 := by
    rintro (_|⟨i,_|a⟩) hh
    · simp [H.base]
    · change ((fderiv ℝ S 0 (α i) : ℝ):ℂ)=0; rw [H.prime]; simp
    simp at hh; omega
  rw [← sub_add_cancel X (ink α S)]
  exact From.add (from_ghost R) hs

omit H
omit [Fintype P] [Fintype A] [DecidableEq A] [DecidableEq P] in
lemma pure_mask {Q : Raw (Alphabet G A P) ℂ} (h : Pure pp false Q) (i:ℤ): Pure pp false (Book.mask i Q):= fun l hl=> by
  by_cases he:(l.length:ℤ) = i; exact (enough _ he).trans (h l hl); exact strange _ he
omit [Fintype P] [Fintype A] [DecidableEq A] [DecidableEq P] in
lemma sym_mask {Q : Raw (Alphabet G A P) ℂ} (h : Symm pp Q) (i : ℤ): Symm pp (Book.mask i Q):= fun l a b v=>by
  by_cases he: ((l++a::b::v).length:ℤ)=i
  · rw [enough _ he, enough _ (by simpa using he), h]
  rw [strange _ he, strange _ (by simpa using he),mul_zero]

include H
lemma mark_insert (E : Links G A→ℝ) (v : ℤ) (he : germ E) (hf : From (ink α E) v)
    (hi : Focus.Inert Φ E) : MarkOK (Letter.bond (Z G A) (Z G P)) F (rankLevel v (ink α E)) := by
  let V := rankLevel v (ink α E)
  have hp : Pure pp false (ink α E) := ink_p _ (Ω).never _
  refine ⟨(even_coeff _).mpr fun i=> pure_mask hp ((i:ℤ)+v),
    fun i _=> ⟨sym_mask (ink_s α (Ω).never he) ((i:ℤ)+v),minH (Limit.mod _ _)⟩,
    fun n i=> ?_,?_⟩
  · rw [mask_conn,ink_off α ((Ω).dual_off i)]; unfold rankLevel; exact map_zero _
  funext n
  have heq : link ΔΔ true p X (ink α E)=0 := by
    refine ((vibes R).onto Ω he).trans ?_
    simp_rw [inkit (Ω).e0 (hi _), ink_zero,map_zero,Finset.sum_const_zero]
  unfold total modulo
  have hv : From Y 0 := fun l hl=>by omega
  rw [LinearMap.add_apply,map_add,LinearMap.add_apply, Pi.add_apply, Pi.add_apply,
    promised, lap_level]
  rw [show pairW (tokenL (Letter.bond (Z G A) (Z G P)).BV true p) (rankLevel 2 X) (rankLevel v (ink α E)) n=_ from link_level (Letter.bond _ _) _ (from_action _ H) hf,
    show pairW (tokenL ΔΔ true p) (rankLevel 0 Y) (rankLevel v (ink α E)) n=_ from link_level (Letter.bond _ _) _ hv hf,
    heq, show link ΔΔ true p Y (ink α E)=0 from Focus.link_g Ω measure_term E,
    show ΔΔ (ink α E)=0 from Focus.lap_g Ω E]; simp [rankLevel]
lemma master_eq : tokM (Letter.bond (Z G A) (Z G P)) F=0 := by
  have hL : ΔΔ X + link ΔΔ true pp X Y=0 :=
    (vibes R).quantum_pay Ω measure_germ (kernel_haar R)
  have hv : link ΔΔ true pp X X=0 := (vibes R).classicalGauge Ω H.smooth H.inert
  have hw : From Y 0:= fun l hl=>by omega
  have hU : Pure pp false Y:= ink_p _ (Ω).never _
  have hX := from_action _ H
  have hs : ∀ (v u : Raw (Alphabet G A P) ℂ)(i j:ℤ), From v i → From u j →
      pairW (tokenL ΔΔ true pp) (rankLevel i v) (rankLevel j u)=rankLevel (i+j-2) (link ΔΔ true pp v u) :=
    fun i j x y hv hy=> funext fun n=> link_level _ _ hv hy
  unfold tokM total
  simp only [map_add,LinearMap.add_apply]
  rw [hs _ _ _ _ hX hX, hs _ _ _ _ hX hw, hs _ _ _ _ hw hX, hs _ _ _ _ hw hw,
    link_commute _ hU (action_even R S), hv, show link ΔΔ true pp Y Y=0 from Focus.link_g Ω _ _]
  funext n; simp only [promised, Pi.add_apply,Pi.smul_apply, lap_level,Pi.zero_apply]
  rw [show ΔΔ Y=0 from Focus.lap_g Ω measure_term]; unfold rankLevel; simp only [map_zero, zero_add,add_zero]
  change mask (n+0) (ΔΔ X) + (1/2:ℂ) • (mask (n+0) _ + mask (n+0) _) = 0
  rw [smul_add,← add_smul,show (1/2:ℂ)+(1/2)=1 by norm_num,one_smul, ← map_add, hL,map_zero]

omit H in
lemma total_even : EvenSeries pp F := (even_coeff _).mpr fun i =>
  (pure_mask (action_even _ _) (i+2)).add (pure_mask (ink_p _ (Ω).never _) (i+0))
lemma total_limits : Γ F p := fun i _=> ⟨ (sym_mask (action_s _ S H.smooth) (i+2)).add
  (sym_mask (ink_s _ (Ω).never measure_germ) (i+0)),
   (Mini _).add_mem (minH (Limit.mod X (i+2))) (minH (Limit.mod Y (i+0)))⟩

omit H
/-- Physical QME Hessian, with A/A sign for positive precision. -/
def costMatrix (S : Links G A→ℝ) : Matrix (Z G A) (Z G A) ℝ :=
  Matrix.of fun i j=> -fderiv ℝ (layer (priv i) S) 0 (priv j)

def gradientGraph : Matrix (Z G A) (Z G P) ℝ := Matrix.of fun i j=> projector i (Φ j 0)

lemma stone_linear (i:Z G A)(k':Alphabet G A P) : Focus.stone Ω Φ i [k']=match k' with
   | Letter.c v => (R.gradientGraph i v : ℂ)
   | _ => 0 := by
  have hs(u : Z G P)(x' : Alphabet G A P) :
      (atLetter (Letter.c u) ⋄ ink α (projector i ∘ Φ u)) [x'] = if x'= Letter.c u then (R.gradientGraph i u:ℂ) else 0 := by
    by_cases he:x'=Letter.c u
    · rw [if_pos he, he,D_eval _ (product _ _ _),D_product,hear,coin_product,one_smul]
      simp only [Pi.add_apply, nil_product,MS.Koszul.at_sign,
        degree_nil,cross_false',one_mul, show atLetter (Letter.c u : Alphabet G A P) []=(0:ℂ) from rfl,
        zero_mul,add_zero]; rfl
    rw [if_neg he,D_eval _ (product _ _ _),D_product,unheard _ he]
    simp only [Pi.add_apply,nil_product,MS.Koszul.at_sign, degree_nil,cross_false',one_mul,
      show atLetter (Letter.c u : Alphabet G A P) []=(0:ℂ) from rfl, Pi.zero_apply,zero_mul,add_zero]
  simp_rw [stone_terms, Finset.sum_apply, hs]; rcases k' with _|_|u|_ <;> simp

include H
lemma total_hessian : Letter.Hessian ((costMatrix S).map Complex.ofReal)
    ((R.gradientGraph).map Complex.ofReal) (F 0) := by
  let W := Focus.launch Ω λΛ Φ; let ζ := bond (Z G A) (Z G P)
  let K := ζ.hung W
  have ht := Focus.lifting Ω λΛ Φ R.smooth_locus
  have hV (t:Alphabet G A P) (j:Alphabet G A P) : F 0 [t,j]= X [t,j]:= by rw [total_start,enough _ (by simp)]
  have hd(k : Z G A)(x:Alphabet G A P) : X [Letter.k k,x]=Focus.stone Ω Φ k [x]:= by
    have hv:=ht.acted (.inl k)
    have hk := ink_off (Ω).e0 ((Ω).dual_off (.inl k)) S
    change D (Letter.k k) (ink α S+ K) [x]= _; rw [map_add, show D (Letter.k k) (ink α S)=0 from hk,zero_add]
    change D (ζ.dual (.inl k)) _ [x]= _; rw [show D _ K= _ from hv,show ((bond _ _).fee (.inl k):ℂ)=1 from rfl,one_smul,← Focus.launch_stone]; rfl
  have hb(k : Z G P)(x:Alphabet G A P) : X [Letter.b k,x]=0:= by
    have hv:=ht.acted (.inr k)
    have hk := ink_off (Ω).e0 ((Ω).dual_off (.inr k)) S
    change D (Letter.b k) (ink α S + K) _= _; rw [map_add,show D (Letter.b k) (ink α S)=0 from hk,zero_add];
    change D (ζ.dual (.inr k)) _ _= _; rw [show D _ K=_ from hv];
    have hh : Focus.shadow θ λΛ k [x]=0:= by
      unfold Focus.shadow; simp_rw [Finset.sum_apply]; refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=>?_
      rw [Pi.smul_apply,D_eval x (product _ _ _), D_product,Pi.add_apply]; simp [Focus.spark,atLetter]
    change (_:ℂ) • W (.inr k) [x]=0; rw [show W (.inr k)=Focus.shadow θ λΛ k from Focus.launch_shadow ..,hh,smul_zero]
  -- remaining coefficients without an antifield
  have hz (i j: Z G A⊕ Z G P) : K [ζ.plain i, ζ.plain j]=0:= by
    unfold K Bonded.hung; rw [Finset.sum_apply]; refine Finset.sum_eq_zero fun u _=> ?_
    rw [Pi.smul_apply,D_eval _ (product _ _ _),D_product,unheard _ (ζ.diff _ _),map_zero,
      LinearMap.zero_apply,zero_add, D_eval _ (product _ _ _), D_product]
    rw [sign_D,unheard _ (ζ.diff _ _), map_zero,smul_zero,map_zero,LinearMap.zero_apply,zero_add]
    simp [atLetter]
  have hc(k: Z G P)(x: Z G A⊕ Z G P) : X [Letter.c k,ζ.plain x]=0:=by
    have ht := ink_off (Ω).e0 (show (Ω).e0 (Letter.c k)=0 from rfl) S
    change (D (Letter.c k) (ink (Ω).e0 S)) [_] + K [ζ.plain (.inr k),_]=0
    rw [ht,hz,add_zero]; rfl
  have hs := action_s R S H.smooth
  have he(x y:Alphabet G A P) : X [x,y]= MS.Koszul.cross (p x) (p y)*X [y,x]:= hs [] x y []
  refine ⟨ ?_,(even_coeff _|>.mp (total_even _) 0), ?_,fun i t=> by rw [hV,hd,R.stone_linear]; cases t <;> rfl,?_,fun i t=> (hV _ _).trans (hb i t)⟩
  · rw [total_start]; exact rankMod _ _
  · rintro i (j|j|j|j) <;> rw [hV]
    · have hq: X [a i,a j]=ink α S [a i,a j]:= by change _+ K [ζ.plain (.inl i),ζ.plain (.inl j)] = _; rw [hz]; exact add_zero _
      rw [hq]; change _= -(↑(-(layer (priv j) (layer (priv i) S) (0:Links G A))) : ℂ)
      push_cast; rw [neg_neg]; rfl
    · rw [he,hd,R.stone_linear]; exact mul_zero _
    · rw [he,show X [Letter.c j,a i]=0 from hc j (.inl i),mul_zero]
    rw [he,hb,mul_zero]
  rintro i (j|j|j|j) <;> rw [hV]
  · exact hc i (.inl j)
  · rw [he,hd,R.stone_linear]; change (-1:ℂ)*_= -_; simp
  · exact hc i (.inr j)
  rw [he,hb,mul_zero]

omit [Fintype P] in
lemma cost_symmetric : (costMatrix S)ᵀ=costMatrix S := by
  ext i j
  exact congr_arg Neg.neg ((alter S H.smooth (priv i) (priv j)).eq_of_nhds)

omit [Fintype P] in
lemma cost_kernel : (costMatrix S)*R.gradientGraph (G:=G)=0 := by
  ext i j; rw [Matrix.mul_apply,Matrix.zero_apply]
  have ht := H.inert j
  let f := fderiv ℝ S
  have hf : DifferentiableAt ℝ f 0:=
    (H.smooth.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  let g := Φ j
  have hg : DifferentiableAt ℝ g 0:= (smooth_locus R j).differentiableAt (by simp)
  have hL : fderiv ℝ (fun u=>f u (g u)) 0=0:= by rw [Filter.EventuallyEq.fderiv_eq (show (fun u=> f u (g u)) =ᶠ[𝓝 0] (fun _=>0) from ht)]; simp
  have hr : fderiv ℝ f 0 (priv i) (g 0)=0:= by
    have he := (hf.hasFDerivAt.clm_apply hg.hasFDerivAt).fderiv
    rw [hL] at he; have hv:= DFunLike.congr_fun he.symm (priv i)
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      show f 0=0 from H.prime,_root_.zero_apply,zero_add] at hv
    exact hv
  have hh : fderiv ℝ (layer (priv i) S) 0 (g 0)=0 := by
    have hz := H.smooth.isSymmSndFDerivAt_of_omega
    unfold layer; rw [(hf.hasFDerivAt.clm_apply (hasFDerivAt_const (priv i) (0:Links G A))).fderiv]
    -- simplify
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      map_zero, _root_.zero_apply,zero_add]; exact (hz (g 0) (priv i)).trans hr
  rw [← @neg_zero ℝ]; change (∑ x:Z G A,-(fderiv ℝ (layer (priv i) S) 0 (priv x))*projector x (g 0))=-0
  nth_rw 1 [← Native.frame (g 0)] at hh; simp_rw [map_sum,map_smul] at hh
  simp_rw [neg_mul,mul_comm _ (projector _ _), Finset.sum_neg_distrib]; exact congr_arg Neg.neg hh
end YM.FVA2.Ends
