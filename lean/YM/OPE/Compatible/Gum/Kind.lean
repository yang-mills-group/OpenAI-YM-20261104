import YM.OPE.Compatible.Gum.Herc
/-!
# Normalized. single and cross polymer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
local notation "W"=> ScriptJ E
variable (p:Ask→E→ℝ)(hp:p 0=p 1)(hs:∀ i,Bond (p i))
include hp hs
lemma βpair (f g:E→ℝ)(hf:Bond f)(hg:Bond g):
    fair μ L (Stell p) (fun i=> coin (f i)*coin (g i))-fair μ L (Stell p) (fun i=>coin (f i))*fair μ L (Stell p) (fun i=>coin (g i))=rich (fun s=> πc μ L s p f g 4):=by
        let D(s:Finset Ask):=πc μ L s p f g 4; let U:Finset Ask→ℝ:=Tap μ L p (f*g); let V:= Tap μ L p f; let W':=Tap μ L p g; have ht(t:Finset Ask)(h:(4:Ask)∉t) : D t= U t-Con V W' t:= cpair μ L t p 4 f g h
        have hA (a:Finset Ask)(h:∀ v:Ask,v∈a→v≠4):D a=U a-Con V W' a:=ht a fun ha=>h _ ha rfl
        have hv : V {0}=V {1}:=by unfold V; rw [payA,payA,hp]
        have hw : W' {0}=W' {1}:=by unfold W';rw [payA,payA,hp]
        have hB(t: Ask): Con V W' {t}=V ∅ * W' {t}+V {t}*W' ∅:=by
            unfold Con;rw [show ({t}:Finset Ask).powerset= {∅,{t}} from ?_]; swap; · fin_cases t <;> decide
            simp
        have hQ: Con V W' {0,1}=V {0,1}*W' ∅+V ∅*W' {0,1}+ 2* V {0}* W' {0}:=by
             unfold Con; rw [show ({0,1}:Finset Ask).powerset={{0},{1},∅,{0,1}} from by decide, sum_insert (by decide : ({0}: Finset Ask)∉ ({{1},∅,{0,1}}:Finset _)),sum_insert (by decide : ({1}:Finset Ask)∉({∅,{0,1}}:Finset _)),sum_insert (by decide : (∅:Finset Ask)∉ ({{0,1}}:Finset _)),sum_singleton,show ({0,1}:Finset Ask)\{0}={1} from by decide,show ({0,1}:Finset Ask)\{1}={0} from by decide]; simp only [Finset.sdiff_self, Finset.sdiff_empty]; rw [← hv,← hw]; ring
        rw [show (fun i=>coin (f i)*coin (g i))=fun i=>coin ((f*g) i) from funext fun i=>by apply eta<;>simp,rootC μ L p hp hs (f*g) (hf.mul hg),rootC μ L p hp hs f hf,rootC μ L p hp hs g hg]; change rich U-rich V * rich W'= rich D; apply eta
        · change U ∅- _ = D ∅; rw [ht _ (by decide)]; simp [Con];rfl
        · change U {0}-(V ∅* W' {0}+V {0}* W' ∅)= _; rw [show (rich D).l=D {0} from rfl,ht _ (by decide), hB]
        change _= D {2}+D {3}+D {0,1}/2; rw [ht {2} (by decide),ht {3} (by decide),ht {0,1} (by decide),hQ,hB,hB]; change (U {2}+U {3}+U {0,1}/2)-(V ∅*(W' {2}+W' {3}+ W' {0,1}/2)+V {0}* W' {0}+ (V {2}+V {3}+ V {0,1}/2)* W' ∅)=_;ring
omit hp hs
omit μ L
abbrev lumps (g:E→Token)(i:Fin 3)(x:E):ℝ:= (g x).seq i.val -- get def name
omit [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][BorelSpace E] [MeasurableSpace E] in lemma lumpSum (p:E→Token): p=∑ i:Fin 3, fun j=>Ū^i.val* coin (lumps p i j):=by
    rw [Fin.sum_univ_three]; ext1 x; apply eta <;>norm_num [Pi.add_apply,lumps,JetS.seq,Ū,pow_two]
end YM.OPE.Libra.Shell
