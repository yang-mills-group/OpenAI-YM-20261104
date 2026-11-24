import YM.OPE.Compatible.Loire.Wool
import YM.OPE.Compatible.Words.Stem
/-! # Wick calculus. Gaussian shifts are injective even for semidef joint -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open MeasureTheory Function Set Topology Filter
open Silt Libra Shrew PertExtension Series GaussianScore Flock
open scoped Topology BigOperators Classical ContDiff
variable {I J E F:Type}[Fintype J]
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
def Crest : ℕ→ (E→ℝ)→ Prop
 | 0,u=>u=0
 | n+1,u=>∀ v:E,Crest n (poke v u)
variable {n k:ℕ} {f g:E→ℝ}
omit [FiniteDimensional ℝ E] in
lemma zeroVisa (n:ℕ): Crest n (0:E→ℝ):=by
    induction n with
    | zero=> rfl
    | succ n ih=> intro v; rw [show poke v (0:E→ℝ)=0 from funext fun i=>by simp [poke]]; exact ih
omit [FiniteDimensional ℝ E] in
lemma successive (h:Crest n f)(hs:n≤k): Crest k f:=by
    induction n generalizing f k with
    | zero=> change f=0 at h; rw [h]; exact zeroVisa k
    | succ n ih=>cases k with | zero=>omega | succ k=> exact fun x=>ih (f:=poke x f) (h x) (by omega)
lemma visa_sum (hp:Bond f)(hq:Bond g)(h:Crest n f)(he:Crest n g): Crest n (f+g):=by
    induction n generalizing f g with
    | zero=> change f=0 at h; change g=0 at he; change _=0; rw [h,he,add_zero]
    | succ n ih => intro x; rw [show poke x (f+g)=poke x f+poke x g from Stranded.pointS x f g hp hq]; exact ih (hp.amount _) (hq.amount _) (h x) (he x)
lemma visa_ms (hp:Bond f)(hq: Bond g)(h:Crest n f)(he:Crest k g): Crest (n+k) (f*g) :=by
    induction n generalizing k f g with
    | zero=> change f=0 at h; rw [h,zero_mul]; exact zeroVisa _
    | succ n ih=>
      induction k generalizing g with
      | zero=> change g=0 at he; rw [he,mul_zero]; exact zeroVisa _
      | succ k il=>
        intro x
        rw [pokeA x hp hq]
        have hs:= ih (f:=poke x f) (hp.amount _) hq (h x) he; rw [show n+(k+1)=n+1+k from by omega] at hs; exact visa_sum ((hp.amount _).mul hq) (hp.mul (hq.amount _)) hs (il (g:=poke x g) (hq.amount _) (he x))
lemma visas (hp:Bond f):∃ k,Crest k f:=by
   have he(t:ℝ): Crest 1 (fun _ : E=>t):=fun i=>funext fun k=>by simp [poke]
   induction hp with
   | keep x=>exact ⟨_,he x⟩
   | glyph z=>exact ⟨2,fun i=>by rw [pokeP z i]; exact he _⟩
   | add hp h I D=> obtain ⟨a,u⟩:=I; obtain ⟨b,t⟩:=D; exact ⟨a+b,visa_sum hp h (successive u (by omega)) (successive t (by omega))⟩ -- notation
   | mul hp h IH IT=> obtain ⟨a,u⟩:=IH; obtain ⟨b,t⟩:=IT; exact ⟨_,visa_ms hp h u t⟩
variable [MeasurableSpace F][BorelSpace F](μ:Measure F)[μ.IsAddHaarMeasure](A:Law F)(Z:F→L[ℝ] E)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
lemma stayBond (p:Bond f)(x:E):Bond (fun y=> f (x+Z y)):=p.comp fun L=>by simp_rw [map_add]; exact (Bond.keep (L x)).add (Bond.glyph (L ∘ₗ Z.toLinearMap))
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace F][BorelSpace F] in
lemma towerBond (p:Bond f)(x v:E):Bond (fun q:ℝ×F=> f ((x+q.1 • v)+Z q.2)):=by
   apply p.comp; intro L; simp_rw [map_add,map_smul]; exact ((Bond.keep _).add ((Bond.glyph (LinearMap.fst ℝ ℝ F)).mul (Bond.keep (L v)))).add (Bond.glyph (L ∘ₗ Z.toLinearMap ∘ₗ LinearMap.snd ℝ ℝ F))
lemma chorus (p:Bond f)(h:Crest n f)(hp:∀ (x:E),A.average μ (fun y=> f (x+Z y))=0): f=0:=by
   induction n generalizing f with
   | zero=>exact h
   | succ n ih=>
       have ht(v:E):poke v f=0:=by
          refine ih (p.amount _) (h v) (fun i=>?_); let g (y:ℝ×F):=f ((i+y.1 • v)+Z y.2); have hv:= Silt.hotrod μ A g (towerBond Z p i v) 0; have hx:A.average μ (fun y=>deriv (fun t:ℝ=>g (t,y)) 0)=0:= hv.unique (by unfold g;simp_rw [hp];exact hasDerivAt_const ..); rw [← hx]; apply congr_arg; funext y
          have hu:HasDerivAt (fun t:ℝ=> ((i+t • v)+Z y)) v 0:=by simpa using (((hasDerivAt_id' (0:ℝ)).smul_const v).const_add i|>.add_const (Z y))
          have hw:= ((p.smooth.differentiable (by simp) ((i+ (0:ℝ) • v)+Z y)).hasFDerivAt.comp_hasDerivAt _ hu).deriv; change _= deriv (f ∘ fun t:ℝ=>i+t • v+Z y) 0; simpa only [poke,comp_apply,zero_smul,add_zero] using hw.symm -- Lean issue
       have hl:f=fun _=>f 0:=eq_of_fderiv_eq (𝕜:=ℝ) (p.smooth.differentiable (by simp)) (differentiable_const _) (fun i=>ContinuousLinearMap.ext (fun j=>by rw [show fderiv ℝ f i j=0 from congr_fun (ht j) i]; simp)) 0 rfl
       ext1 z; have hv:=hp z; rw [hl] at hv; rw [singleConst] at hv; exact (congr_fun hl z).trans hv
lemma inject_chant (hp:Bond f)(he:Bond g)(hh:∀ x:E,A.average μ (fun y=>f (x+Z y))= A.average μ (fun y=>g (x+Z y))): f=g:=by
    obtain ⟨n,h⟩:= visas (hp.sub he); apply sub_eq_zero.mp (chorus μ A Z (hp.sub he) h fun x=>?_); exact (Shrew.snow μ A (f:=fun y=> f (x+Z y)) (g:=fun y=> g (x+Z y)) (stayBond Z hp x) (stayBond Z he x)).trans (sub_eq_zero.mpr (hh x))
end YM.OPE.Prairies
