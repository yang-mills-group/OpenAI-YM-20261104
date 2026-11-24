import YM.X.Gauss.Expect
import YM.PertExtension.PolynomialWick
/-!
Complex ordinary polynomials in real dual variables, lookup via `blend 0`; and the FO projection assertion.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gauss
open Function Filter Set MeasureTheory PertExtension PertExtension.GaussianScore Next.Rank Next.Rank.Normal MvPolynomial
open scoped BigOperators Topology ContDiff Classical
variable {E F J : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (P:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
local notation "E₁"=>P.average μ
variable (Q:Law F) (ν:Measure F)[ν.IsAddHaarMeasure]
variable (T:E→ₗ[ℝ] F)(H:∀ (v:Module.Dual ℝ F),T (P.inverse (v.comp T))=Q.inverse v)
local notation "E₂"=>Q.average ν
variable (S:J→Module.Dual ℝ E)

def seen (L:ℂ→ₗ[ℝ] ℝ) (p:poly J) : E→ℝ:= fun x=> L (aeval (fun i:J=> (S i x:ℂ)) p)
private lemma seen_word {I:Type*} [Fintype I](f:I→J)(s:Finset I) (c:ℂ)(L:ℂ→ₗ[ℝ] ℝ): seen S L (c • glyphs f s)= L c • Law.product (S ∘ f) s:= by
   funext x; unfold seen glyphs Law.product; simp only [map_smul,map_prod,aeval_X,←Complex.ofReal_prod,smul_eq_mul]; change L (c*_)= L c * _; rw [mul_comm c,← Complex.real_smul,map_smul]; exact mul_comm ..
lemma plausible_seen (L:ℂ→ₗ[ℝ] ℝ)(p:poly J): Plausible (seen S L p):= by
   induction p using MvPolynomial.induction_on' with
   | monomial i c=>
     obtain ⟨Y,hY⟩:= Common.letter i
     rw [show monomial (R:=ℂ) i c=c • glyphs Y Finset.univ from (by rw [← hY, ← map_smul,smul_eq_mul,mul_one]),seen_word]
     refine (show Plausible _ from ?_).scale (L c)
     have he (I: Type) [Fintype I](v:I→J): Plausible (Law.product (S ∘ v) Finset.univ):= by
        rw [show Law.product (S ∘ v) Finset.univ=(∏ i:I,(S (v i):E→ℝ)) from funext fun x=> (Finset.prod_apply x Finset.univ (fun i:I=> (S (v i): E→ℝ))).symm]; exact Plausible.prod fun i _=>Plausible.line ..
     exact he _ _
   | add x y h g=> rw [show seen S L (x+y)= _ from funext (fun a=> (show seen S L (x+y) a=(seen S L x + seen S L y) a from (by unfold seen; rw [map_add,map_add];rfl)))]; exact h.add g
lemma expect_leads (L:ℂ→ₗ[ℝ]ℝ)(p:poly J): E₁ (seen S L p)= L (blend (formed S P) 0 p):= by
    induction p using MvPolynomial.induction_on' with
    | monomial i c=>
      obtain ⟨Y,hY⟩:= Common.letter i
      rw [show monomial (R:=ℂ) i c=c • glyphs Y Finset.univ from (by rw [← hY, ← map_smul,smul_eq_mul,mul_one]),seen_word,average_scale, map_smul (blend ..), ← glyph P μ S]; rw [smul_eq_mul,mul_comm c,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
    | add x y h g=> rw [show seen S L (x+y)= (seen S L x + seen S L y) from funext (fun a=> (by unfold seen; rw [map_add,map_add];rfl)), average_add P μ (plausible_seen ..) (plausible_seen ..),h,g,map_add,map_add]

lemma seen_from (f:E→ℝ)(h:Plausible f): ∃ p:poly (Module.Dual ℝ E), seen id Complex.reCLM.toLinearMap p=f:= by
    induction h with
    | atom c=> refine ⟨MvPolynomial.C (c:ℂ),funext fun x=>?_⟩; rw [seen,aeval_C];rfl
    | times g a _ h=> obtain ⟨p,rfl⟩:=h; exact ⟨p*X a,funext fun x=> (by unfold seen;rw [map_mul,aeval_X]; simp [Complex.mul_re])⟩
    | add h₁ h₂ h g=> obtain ⟨p,rfl⟩:=h;obtain ⟨q,rfl⟩:=g; exact ⟨p+q,funext fun _=> by unfold seen;rw [map_add,map_add];rfl⟩
include H
lemma moves {f:F→ℝ}(h:Plausible f): E₁ (f ∘ T)=E₂ f:= by
   obtain ⟨p,rfl⟩:= (seen_from f h)
   let v (a:Module.Dual ℝ F):= a.comp T; let L:=Complex.reCLM.toLinearMap
   change E₁ (seen v L p)=E₂ (seen id L p)
   rw [expect_leads,expect_leads]; rw [show formed v P= formed (id: Module.Dual ℝ F→_) Q from ?_]
   ext1; funext i j; exact congr_arg Complex.ofReal (congr_arg j (H _))
end YM.PositionX.Gauss
