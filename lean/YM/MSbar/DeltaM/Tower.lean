import YM.MSbar.DeltaM.Blade
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
variable {Trea β α v r C u d b a t : ℝ}{S:Finset σ}{m:ℕ} {q:Finset σ}
variable (H:Cash φ A i B μ ν l F x Trea d a t m q)
local notation "L!"=> hint μ φ A F
local notation "C!"=> hint ν i B F
local notation "E!"=> (fun j T=> pillar φ μ j F (play T) A)
local notation "e!"=> (fun j T=> pillar i ν j F (play T) B)
namespace Cash
variable {ι' :σ}

private def veil (x y a b:ℝ):Prop:= |x|≤ a∧|y| ≤ a∧|x-y| ≤ b
private lemma veil_w {p P' a b c d:ℝ} (h: veil p P' a b) (ha:a≤ c)(hb:b≤d): veil p P' c d:=⟨h.1.trans ha,h.2.1.trans ha,h.2.2.trans hb⟩
private lemma veil_add {a b p P' x X' y y':ℝ}(h: veil a b x X')(he:veil p P' y y'):veil (a+p) (b+P') (x+y) (X'+y'):=by
    refine ⟨(abs_add_le ..).trans (add_le_add h.1 he.1),(abs_add_le ..).trans (add_le_add h.2.1 he.2.1),?_⟩; rw [show a+p-(b+P')=(a-b)+(p-P') by abel]; exact (abs_add_le ..).trans (add_le_add h.2.2 he.2.2)
private lemma veil_mul {a b p P' x X' y y':ℝ}(h: veil a b x X')(he:veil p P' y y'): veil (a*p) (b*P') (x*y) (x*y'+X'*y) := by
    have hx :0≤ x:= (abs_nonneg _).trans h.1; have hX':0≤ X':=(abs_nonneg _).trans h.2.2
    rw [veil]; refine ⟨(abs_mul ..).trans_le (mul_le_mul h.1 he.1 (abs_nonneg _) hx),(abs_mul ..).trans_le (mul_le_mul h.2.1 he.2.1 (abs_nonneg _) hx),?_⟩; rw [show _ - _ = a*(p-P')+(a-b)*P' by ring]; exact (abs_add_le ..).trans (add_le_add ((abs_mul ..).trans_le (mul_le_mul h.1 he.2.2 (abs_nonneg _) hx)) ((abs_mul ..).trans_le (mul_le_mul h.2.2 he.2.1 (abs_nonneg _) hX')))
include H
private lemma chop (j:σ) (hq:j∈q)(L : List σ)(he:L.toFinset⊆q)(t X:List σ→ℝ) (hv:0 ≤ u)(hp:∀ M: List σ, M.toFinset⊆q → M.length<L.length→veil (t M) (X M) u (d*u)) : veil (shake j (φ*A*φ.transpose) L t) (shake j (i*B*i.transpose) L X) (L.length*(Trea*u)) (L.length*(2*d*(Trea*u))) := by
    induction L generalizing t X with
    | nil=> simp [veil,shake]
    | cons c T ih=>
       let H₀:=H; let V:= Trea*u
       have ht:T.toFinset⊆ q:=by exact subset_trans (by rw [List.toFinset_cons];apply subset_insert) he
       have hg: c ∈ q:=he (by simp)
       have he :=hp T ht (by simp); let g L:=t (c::L); let f L:=X (c::L)
       have hG(l:List σ) (hy:l.toFinset⊆q)(hk:l.length<T.length): veil (g l) (f l) u (d*u):= hp (c::l) (by simpa only [List.toFinset_cons] using Finset.insert_subset_iff.mpr (And.intro hg hy)) (by simpa using hk) -- membership notation
       have hm:= veil_add (veil_mul (show veil ((Y!) j c) ((X!) j c) Trea (Trea*d) from per_se H j c hq) he) (ih ht g f hG) -- order
       simp_rw [shake,List.length_cons]; push_cast; exact veil_w hm (le_of_eq (by ring)) (le_of_eq (by ring))
private lemma singleE (j:σ)(L:List σ) :
    L! (play (j::L))=μ j* L! (play L)+ shake j (Y!) L (fun i=> L! (play i)) + ∑ z:σ,(Y!) j z*E! z L := by
    obtain ⟨F,hF⟩:=pint φ μ H.alive H.helm; rw [show play (j::L)= play L * MvPolynomial.X j from mul_comm .., atop φ μ H.alive H.helm]; rw [mul_comm _ (μ j)]; simp_rw [← hF]; rw [sift]
omit H in
noncomputable def glow_cost (w t :ℝ)(n:ℕ): ℝ := match n with
    | 0=> 1
    | p+1=>
       let u:= glow_cost w t p; let V:=w*u; u+(p+1:ℝ)*2*V + w*t+w^2*t
private lemma gather (j:σ)(p' : List σ) : C! (play (j::p'))=ν j*C! (play p')+ shake j (X!) p' (fun k=>C! (play k)) + ∑ l,(X!) j l * e! l p' := by
    obtain ⟨F,hF⟩:=pint i ν H.able H.helm; rw [show play (j::p')= play p' * MvPolynomial.X j from mul_comm .., atop i ν H.able H.helm]; rw [mul_comm _ (ν j)]; simp_rw [← hF]; rw [sift]
-- finite j quotas, cost proportional δ.
private lemma pulse_cost (k:ℕ)(hk:k≤m) : ∀ T : List σ,T.toFinset⊆q→ T.length ≤ k → veil (L! (play T)) (C! (play T)) (glow_cost Trea t k) (d*glow_cost Trea t k):=by
    have hb:= H.chances.full.hope; have ht:= H.budgets; have hd:= H.chances.soft
    induction k with
    | zero=> intro p hx hf; have ht : p=[]:= List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hf); rw [ht]; unfold veil hint play; simp [glow_cost, hd] -- ∫1
    | succ k ih=>
       specialize ih (by omega); intro T htH hw; let u:=glow_cost Trea t k; have hU:= (abs_nonneg _).trans ((ih [] (by simp) (Nat.zero_le k)).1); let S':=glow_cost Trea t (k+1); have hxU: u≤ S' :=by unfold S'; rw [glow_cost]; have hh:0≤u:=hU; change u≤ u+_+_+_; linarith only [hh,mul_nonneg hb ht, mul_nonneg (sq_nonneg Trea) ht,(show 0 ≤ (k+1:ℝ)*2*(Trea*u) from by positivity)]
       by_cases he:T.length ≤ k; exact veil_w (ih T htH he) hxU (mul_le_mul_of_nonneg_left hxU hd)
       cases T with
       | nil=>simp at he
       | cons j T=>
          rw [List.toFinset_cons,Finset.insert_subset_iff] at htH; rw [List.length_cons] at he hw; have ha:T.length=k:=by omega
          obtain ⟨hj,hT⟩:=htH; obtain ⟨he,hf,hx,-⟩:= H.rent j hj
          have hh(v:List σ)(hi:v.toFinset⊆q)(he:v.length<T.length):veil (L! (play v)) (C! (play v)) u (d*u) := ih v hi (by omega)
          rw [singleE H j T,gather H j T]; have hx:=veil_mul (show veil (μ j) (ν j) Trea (d*Trea) from ⟨he,hf,hx⟩) (ih T hT ha.le)
          have hL :0 ≤ u:= hU; have hQ := veil_add hx (chop H j hj T hT _ _ hL hh); have hζ:= shine H j hj T hT (show _ ≤ m by omega)
          refine veil_w (veil_add hQ (show veil _ _ _ _ from hζ)) ?_ ?_
          · rw [ha,glow_cost]; have hv:0≤Trea*u:=mul_nonneg hb hU; change Trea*u+(k:ℝ)* (Trea*u)+Trea*t ≤ u+(k+1:ℝ)*2*(Trea*u)+Trea*t+_ ; linarith only [hL,hv,mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) hv,mul_nonneg (sq_nonneg Trea) ht]
          rw [ha,glow_cost]; change Trea*(d*u)+(d*Trea)*u+(k:ℝ)*(2*d*(Trea*u))+d*(Trea*t+Trea^2*t)≤ d*(u+(k+1:ℝ)*2*(Trea*u)+Trea*t+Trea^2*t); linarith only [mul_nonneg hd hL]
lemma blade (W:List σ) (ht:W.toFinset ⊆q)(hp: W.length≤m):
    |L! (play W)|≤ glow_cost Trea t m ∧ |C! (play W)|≤ glow_cost Trea t m ∧ |L! (play W)-C! (play W)|≤ d*glow_cost Trea t m:= pulse_cost H m le_rfl W ht hp
end Cash
end YM.MSbar.Kelvin
