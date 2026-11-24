import YM.MSbar.Pole.Scale.Regular
import YM.MSbar.Pole.Dimension.Coherent
import YM.MSbar.Pole.Dimension.Flow
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! # Dimensionally renormalized continuum convention

Precise measure: d^Dℓ/(2π)^D per free integration, with the exp-normalized body supplied
by `Dimensional`. MS-bar additionally includes the scale factor `κ_ε`, using derivative
Euler convention in that factor. Parameterize by μ>0 in physical units; no need to fix
at one when scaling momenta. Complex powers use logs real on positive arguments.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Radial
open scoped Topology ContDiff Classical BigOperators Real
variable {I : Type} [Fintype I]

structure Meridian (U : Set ℂ) (F : ℂ → Cloud I) : Prop where
  budget n : Wall U (ticket (@id (External I n))) 1 (fun z => F z n)
  tensor (z:ℂ) : z∈U → Tensor (F z)
structure Sweep (U : Set ℂ) (F : ℂ → Screened I) : Prop where
  budget n : Wall U (ticket (@Prod.snd (place n) (External I n))) (ticket (@Prod.fst (place n) (External I n))) (fun z => F z n)
  texture (z:ℂ) : z∈U → Texture (F z)
namespace Sweep
variable {U : Set ℂ} {F : ℂ→Screened I}
lemma breeze (h : Sweep U F) {z:ℂ} (hz : z∈U) : Breezes (F z) := by
  intro n; rw [Domain,univ_prod_univ]; exact (h.budget n).fixed hz
lemma mono (h : Sweep U F) {V : Set ℂ} (hp : V⊆U) : Sweep V F := ⟨fun n => (h.budget n).mono hp, fun z hz => h.texture z (hp hz)⟩
end Sweep
namespace Meridian
variable {U : Set ℂ} {F : ℂ → Cloud I}
lemma mono (h : Meridian U F) {V : Set ℂ} (hp : V⊆U) : Meridian V F:=⟨fun n => (h.budget n).mono hp,fun z hz => h.tensor z (hp hz)⟩
lemma weight (h : Meridian U F) {b : ℂ→ℂ} (hh : Differentiable ℂ b) (R : ℝ) (hr : ∀ x∈U,‖x‖≤ R) : Meridian U (fun z n x=> F z n x*b z) := by
  refine ⟨fun n => ?_, fun z hz => ⟨fun n J x=> ?_,fun n x=>?_⟩⟩
  · exact Wall.mul (h.budget n) (Wall.entire hh R hr)
  · rw [(h.tensor z hz).moves]
  rw [(h.tensor z hz).agrees]
end Meridian
open place
private abbrev Axis (I:Type) [Fintype I] (n:ℕ) := ℂ × External I n
private abbrev Later (I:Type) [Fintype I] (n:ℕ) := place n × Axis I n
-- angular lift map, adjoint no changing external indices
private def ascent (n:ℕ): ℝ × Later I n →L[ℝ] ℂ × (place (n+1) × External I (n+1)) :=
    let A := Axis I n
    let Y:= Later I n
    let D := ContinuousLinearMap.snd ℝ ℝ Y
    let S := (ContinuousLinearMap.snd ℝ (place n) A).comp D
    let P := ContinuousLinearMap.fst ℝ (place n) A
    let T := (portal n).toContinuousLinearMap.comp ((P.comp D).prod (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ Y)))
    let X := (ContinuousLinearMap.snd ℝ ℂ (External I n)).comp S
    ((ContinuousLinearMap.fst ℝ ℂ (External I n)).comp S).prod (T.prod (ContinuousLinearMap.pi fun i : I=> pad n |>.comp ((ContinuousLinearMap.proj i).comp X)))
private lemma staged (n : ℕ) (t:ℝ) (p : place n) (z:ℂ) (x : External I n) : ascent n (t,p,z,x)= (z,portal n (p,t),pad n ∘ x):=rfl
private lemma pad_norm (n : ℕ) (x : External I n) : ‖pad n ∘ x‖ = ‖x‖ := by
  have hh (i : place n) : ‖pad n i‖ = ‖i‖ := by
    have ht:= squared (n:=n) (i,0); simp only [← pad_at,norm_zero,zero_pow (by decide : 2 ≠ 0), add_zero
      ] at ht
    nlinarith [norm_nonneg (pad n i),norm_nonneg i]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i; rw [comp_apply,hh]; exact norm_le_pi_norm _ _
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]; intro i; rw [← hh]; exact norm_le_pi_norm (pad n ∘ x) i
private lemma aperture (n : ℕ) (x : place n) (t : ℝ):
    (1+|t|)*(1+‖x‖)≤(1+‖portal n (x,(t:ℂ))‖)^2:=by
  have hh := squared (n:=n) (x,(t:ℂ)); simp only [Complex.norm_real] at hh -- reduction
  have hh : ‖portal n (x,(t:ℂ))‖^2= ‖x‖^2+|t|^2:= by simpa only [← Real.norm_eq_abs,Complex.norm_real] using! hh
  have ht: 1+|t| ≤1+‖portal n (x,(t:ℂ))‖:=by nlinarith [abs_nonneg t,norm_nonneg x,norm_nonneg (portal n (x,(t:ℂ)))]
  have hy : 1+‖x‖≤1+‖portal n (x,(t:ℂ))‖:=by nlinarith [abs_nonneg t,norm_nonneg x,norm_nonneg (portal n (x,(t:ℂ)))]
  rw [pow_two]; exact mul_le_mul ht hy (by positivity) (by positivity)

variable {U : Set ℂ} {F : ℂ→ Screened I}
private def future (F : ℂ→Screened I) (n:ℕ) (v : ℝ × Later I n) :=
    (fun x : ℂ × (place (n+1) × External I (n+1)) => F x.1 (n+1) x.2) (ascent n v)
private lemma brought (n : ℕ) (h : Sweep U F) :
   let G := future F n; let q:= ticket (@id (External I n)); let t:= strip (External I n) U
   let s:= univ ×ˢ (Domain n t); let Y : Axis I n := (1,0); let Z : Axis I n:= (Complex.I,0)
   Packet s (((stretch q).back (@Prod.snd (place n) _)).back Prod.snd) (Moment (screen n 1)) G ∧
   EvenOn (Domain n t) G ∧ ∀ u∈s,CR ((0:ℝ),(0:place n),Y) ((0:ℝ),(0:place n),Z) G u:=by
  intro G q t s Y Z
  have hm := (h.budget (n+1)).stream
  have hv x (hx:x∈ s) : ascent (I:=I) n x ∈ strip (place (n+1) × External I (n+1)) U := ⟨hx.2.2.1,mem_univ _⟩
  refine ⟨?_,?_,fun u hu=> ?_⟩
  · let p := (((stretch q).back (@Prod.snd (place n) _)).back (@Prod.snd ℝ (Later I n))); let b:= Moment (screen n (1:Price (Axis I n)))
    have he:=comp_affine_bill (ascent n) 0 hm (p:=p) (q:=b) (U:=s) (fun x hx=> ?_) ?_ ?_
    · simp only [zero_add] at he; exact he
    · simpa only [zero_add] using hv x hx
    · refine bill_byprice (p:=p) (s:= (stretch (ticket (@Prod.snd (place (n+1)) (External I (n+1))))).back (fun x=> 0+ascent (I:=I) n x)) ?_
      rintro ⟨r,x,z,w⟩ hw; change 1 + ‖(0+ascent n (r,x,z,w)).2.2‖≤1 + ‖w‖; rw [zero_add,staged,pad_norm]
    refine bill_single (l:=2) zero_le_one fun u hu=>?_; obtain ⟨r,x,z,w⟩:=u
    change ‖b (r,x,z,w)‖ ≤ 1*(1+‖(0+ascent n (r,x,z,w)).2.1‖)^_; rw [Real.norm_of_nonneg (b.pos _).le,zero_add,one_mul]
    change (1+|r|)*((1+‖x‖)*1) ≤ _; rw [mul_one]; exact aperture n x r
  · rintro ⟨x,z,w⟩ ⟨-,hz,-⟩ a; exact symmetric (h.texture z hz) n (x,w) (mem_univ _) a
  have hh : ascent n ((0:ℝ),(0:place n),Y)=(1,0) := by
    dsimp only [Y]; rw [staged]; simp only [Complex.ofReal_zero,← Prod.zero_eq_mk,map_zero]; congr 2; funext i; exact map_zero (pad n)
  have hh' : ascent n ((0:ℝ),(0:place n),Z)=(Complex.I,0) := by
    dsimp only [Z]; rw [staged]; simp only [Complex.ofReal_zero,← Prod.zero_eq_mk,map_zero]; congr 2; funext i; exact map_zero (pad n)
  exact CR.pull _ (ascent n|>.hasFDerivAt (x:=u)) ((hm.smooth _ (hv u hu)).differentiableAt (by simp)) (by rw [hh,hh']; exact (h.budget _).cr _ (hv u hu))

def dimension (z:ℂ) := 4-2*z
private lemma Body_rule (R:ℝ) (hr : ∀ z∈U, ‖z‖≤R) (o:IsOpen U) (h : Sweep U F) :
    Meridian U (fun z n x=> omega n (F z) x (dimension z)):=by
  refine ⟨fun n=>?_,fun z hz=> operations (h.breeze hz) (h.texture z hz) _⟩
  let p := ticket (@id (External I n)); let t:= strip (External I n) U; let G := future F n
  let L := -(2:ℂ) • (ContinuousLinearMap.fst ℝ ℂ (External I n))
  have he (x:Axis I n) : 4+L x=dimension x.1:=by dsimp [L,dimension]; simp [sub_eq_add_neg]
  obtain ⟨hp,hh,hJ⟩:= brought n h
  obtain ⟨-,hV,hK⟩ := internal (p:=stretch p) (L:=L) (b:=4) (o.prod isOpen_univ)
    (show ContinuousOn (fun x:Axis I n=> 1+‖x.2‖) t from continuousOn_const.add continuousOn_snd.norm) hp hh
    (‖(4:ℂ)‖+‖(2:ℂ)‖*R) (fun x hx => by rw [he]; unfold dimension; refine (norm_sub_le ..).trans (add_le_add_right ?_ _); rw [norm_mul]; gcongr; exact hr _ hx.1)
  let f (x:Axis I n):=omega n (F x.1) x.2 (dimension x.1)
  have hx : f=fun x=>inside n G x (4+L x):=by
    funext x; rw [he]; unfold f omega inside; congr 1; refine integral_congr_ae ?_; filter_upwards with u
    exact congr_fun (recorded (f:=lifting n (F x.1)) (g:=G) (x:=(u,x.2)) (y:=(u,x)) (fun _=>rfl)) _
  have hc : Packet t (stretch p) (stretch 1) f:= by rw [hx]; exact hV
  refine ⟨hc,fun z hz x=> ?_⟩; let v:Axis I n:=(1,0); let w:Axis I n:=(Complex.I,0)
  have hj : L w=Complex.I* L v:= by simp [v,w,L,mul_comm]
  have hg : CR v w f (z,x) := by rw [hx]; exact hK v w hj hJ _ ⟨hz,mem_univ _⟩
  exact (coordinates (U:=f) ((hc.smooth _ (mem_prod.mpr ⟨hz,mem_univ x⟩)).differentiableAt (by simp))).mp hg

/-- exp Euler convention. -/
def euler : ℝ := -deriv Real.Gamma 1
def factor (μ:ℝ) (z : ℂ) :=
    -- because body already normalized by Gaussian mass
    (((Real.exp euler*μ^2/(4*π):ℝ):ℂ)^z) * ((π:ℂ)^(dimension z/2))/((2*π:ℝ):ℂ)^(dimension z)
lemma factor_entire (μ:ℝ) (hμ:0<μ) : Differentiable ℂ (factor μ):=by
  have h₀ : (((Real.exp euler*μ^2/(4*π):ℝ):ℂ))≠0:=by norm_cast; positivity
  have h₁ : (π:ℂ)≠0:=by exact_mod_cast Real.pi_pos.ne'
  have h₂ : ((2*π:ℝ):ℂ)≠0:=by norm_cast; positivity
  unfold factor
  simp_rw [Complex.cpow_def_of_ne_zero h₀,Complex.cpow_def_of_ne_zero h₁,Complex.cpow_def_of_ne_zero h₂,dimension,div_eq_mul_inv,← Complex.exp_neg]; fun_prop

/-- Free momentum integration including MS-bar weight. -/
def Integrates (μ:ℝ) (F:ℂ→Screened I) (z:ℂ) : Cloud I:=fun n x=> omega n (F z) x (dimension z)*factor μ z
lemma integrates (R:ℝ) (hr : ∀ z∈U, ‖z‖≤R) (o:IsOpen U) (h : Sweep U F) (μ:ℝ) (hμ:0<μ) : Meridian U (Integrates μ F):=
  (Body_rule R hr o h).weight (factor_entire μ hμ) R hr
end YM.MSbar.Pole
