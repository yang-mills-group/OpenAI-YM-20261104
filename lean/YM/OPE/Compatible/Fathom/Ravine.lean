import YM.OPE.Compatible.Fathom.Lodge
import YM.OPE.Compatible.Words.Stem
import YM.OPE.Compatible.Straws.Stoop
/-!
# Polynomial test degree and scalar IBP. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {I J:Type}{i j k r:ℕ}
local notation "V!"=> Module.Dual ℝ E
variable {p q z:E→ℝ}
open JetS
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable (μ:Measure E) [μ.IsAddHaarMeasure] (A:Law E)
variable [MeasurableSpace F][BorelSpace F][FiniteDimensional ℝ F]
variable (ν:Measure F) [ν.IsAddHaarMeasure] (L:Law F)
open Libra.Shift Flock
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in
lemma gains (f:E×F →ℝ)(h:anthem j f): anthem j (fun v:E=> L.average ν (fun y:F=> f (v,y))):=by
    suffices h:∀ q:F→ℝ,Bond q→anthem j (fun v:E=> L.average ν (fun y:F=> f (v,y)*q y)) by simpa only [Pi.one_apply,mul_one] using h 1 Bond.one
    induction h with
    | bank n b=> intro q _; exact anthem.bank n _
    | @add n f g h1 h2 ha hb=>
        intro q hp; convert (ha q hp).add (hb q hp) using 1; ext1 x; change L.average ν _= _+_; simp_rw [Pi.add_apply,add_mul]; exact sun ν L ((leanB _ h1.cost _).mul hp) ((leanB _ h2.cost _).mul hp)
    | @cons n u f hf ih=>
        intro q hq; let V':=u.comp (LinearMap.inl ℝ E F); let U':=u.comp (LinearMap.inr ℝ E F); let g(x:E)(y:F):= f (x,y); have hx(x) : Bond (g x):=leanB _ hf.cost x
        have he(x:E)(y:F): u (x,y)= V' x + U' y:=by rw[show (x,y)=(x,0)+(0,y) by simp,map_add];rfl
        let p:= ⇑U'*q; have hp: Bond p:=(Bond.glyph _).mul hq; convert (anthem.cons V' (ih q hq)).add ((ih p hp).bloat (Nat.le_succ _)) using 1; ext1 x; change L.average ν _= V' x*L.average ν (g x*q)+L.average ν (g x*p); rw [show (fun y:F=>_)=V' x • (g x*q)+(g x*p) from ?_,sun ν L (((hx x).mul hq).scale _) ((hx x).mul hp),scooted]; funext y; simp_rw [p,Pi.add_apply,Pi.mul_apply, Pi.smul_apply,smul_eq_mul,he]; unfold g; simp only [Pi.mul_apply];ring
-- compose.Inequalities product.Context Trim ≥k.F.
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma ArtBank (f:ℝ): anthem (E:=E) j (fun _=> f):=anthem.bank _ _
def skry (p:E→Token)(t:Fin 3)(i:E):ℝ:= (p i).seq t.val
-- simple α Prop.All frames f. choose order decreases cutoff `K+2−s`. Keep val≥.
abbrev Carat (p:E→Token): Prop:=∀ j:Fin 3, anthem (3*j.val) (skry p j)
def MoldH (A:Law E)(μ:Measure E)(k:ℕ)(p:E→Token):Prop:=∀ i:Fin 3, Husk μ A (k+3*(2-i.val)) (skry p i)
namespace Husk
variable {μ A ν L}
omit [FiniteDimensional ℝ E][BorelSpace E][μ.IsAddHaarMeasure] in lemma elementary (h:Husk μ A j p)(c:ℝ):Husk μ A j (c • p):=by
     refine ⟨h.coin.scale c,fun {k} hk q hq=>?_⟩; rw [smul_mul_assoc,scooted,h.pays hk q hq,mul_zero] -- simp direction
protected lemma split (h:Husk μ A j p)(h':Husk μ A j q): Husk μ A j (p+q):=⟨h.coin.add h'.coin,fun hk f hf=> by rw [add_mul,sun μ A (h.coin.mul hf.cost) (h'.coin.mul hf.cost),h.pays hk _ hf,h'.pays hk _ hf,add_zero]⟩
-- marginal
lemma meander {p:E×F→ℝ}(h:Husk (μ.prod ν) (united A L) j p): Husk μ A j fun i:E=> L.average ν (fun x:F=>p (i,x)):=by
     refine ⟨Shift.retake ν L _ h.coin,fun {k} hk g hg=>?_⟩; let X:= LinearMap.fst ℝ E F; have hf:= h.pays hk (g ∘ X) (hg.compLinear X); let f(x:E):=L.average ν (fun y:F=>p (x,y)); rw [harvested μ ν A L _ (h.coin.mul (hg.compLinear X).cost)] at hf
     convert! hf using 2; ext1 i; change f i*g i=L.average ν (fun v:F=> p (i,v)*g i); rw [show (fun v:F=>_)= g i • fun x:F=> p (i,x) from funext fun i=>mul_comm .., scooted]; apply mul_comm
end Husk
variable {μ A ν L}
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma skS {q s:E→Token} (h:Carat q) (ht: Carat s):Carat (q*s):=by
     intro j; fin_cases j
     · exact (h 0).times (ht 0)
     · exact ((h 0).times (ht 1)).add ((h 1).times (ht 0))
     exact (((h 0).times (ht 2)).add ((h 1).times (ht 1))).add ((h 2).times (ht 0))
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma tipC {p:E→Token}(h:Carat p)(hp:∀ i,(p i).s=1):Carat (fun i=>(p i)⁻¹):=by
     have hx:∀ v:ℕ,∀ p:E→ℝ,anthem v p→ anthem v (-p):=fun v p h=>by simpa only [neg_one_smul] using h.scale (-1)
     intro i; fin_cases i
     · unfold skry; simp only [JetS.seq, JetS.sp_s,hp,inv_one]; exact anthem.bank _ _
     · unfold skry; simp [JetS.seq,hp]; exact hx _ _ (h 1)
     unfold skry; have ht:= (h 1).powers 2; have hh:= ht.add (hx _ _ (h 2)); simpa only [JetS.seq,JetS.sp_h,hp,one_pow,div_one,sub_eq_add_neg] using! hh
omit [MeasurableSpace E][BorelSpace E] [FiniteDimensional ℝ E] in lemma casket {p:E×F→Token}(h:Carat p): Carat (crossT ν L p):=fun j=> by fin_cases j; all_goals exact gains _ _ _ (h _)
lemma teller {p q:E→Token}(h:MoldH A μ k p)(H:Carat q):MoldH A μ k (p*q):=by
      let K(z:Fin 3):= k+3*(2-z.val); have hv(i j l:Fin 3)(hp : K l + 3*j.val ≤ K i) : Husk μ A (K l) (skry p i*skry q j):= (h i).laysL _ _ (H j) hp
      intro j; fin_cases j
      · exact hv 0 0 0 (Nat.le_refl _)
      · exact (hv 0 1 1 (by dsimp[K];omega)).split (hv 1 0 1 (Nat.le_refl _))
      exact ((hv 0 2 2 (by dsimp[K];omega)).split (hv 1 1 2 (by dsimp[K];omega))).split (hv 2 0 2 (Nat.le_refl _))
lemma wrappedT {p q:E×F→Token}(h:MoldH (united A L) (μ.prod ν) k p)(H:Carat q)(hz:∀ i,(q i).s=1): MoldH A μ k (fun i=> crossT ν L (p*q) i / crossT ν L q i):=by
      let P:=p*q; have ht:= teller h H; apply teller (A:=A) (μ:=μ) (k:=k) (p:= crossT ν L P) (q:= fun i:E=> (crossT ν L q i)⁻¹)
      · intro i; fin_cases i; exact Husk.meander (ht 0); exact Husk.meander (ht 1); exact Husk.meander (ht 2)
      exact tipC (casket H) (fun i=> headD ν L _ fun j=> hz (i,j))
end YM.OPE.Cloud
