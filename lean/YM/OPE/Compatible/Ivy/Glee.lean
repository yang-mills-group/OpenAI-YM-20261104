import YM.OPE.Compatible.Ivy.Flits
/-!
# rank convolution bookkeeping. Fin frontier
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E: Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {k m d e n:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S:Story I}{P:Curtain I}{t:Side}{x:deck I t}{j:Site t}{Z:E→L[ℝ] deck I t}
-- transfer elements. spinHex transport indices.
omit [Fintype I] in lemma shiftH (f:Token)(i j: Phase) : (Ū^j.val*f).seq i.val= ∑ k∈ Finset.univ.filter (fun k:Phase=> k.val+j.val=i.val), f.seq k.val :=by
     simp only [Finset.sum_filter]; fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_three, JetS.seq, Ū,pow_two]
lemma shiftP (f:Token)(i j k:Phase): (Ū^(j.val+k.val)*f).seq i.val= ∑ t∈ Finset.univ.filter (fun t:Phase=> t.val+j.val+k.val=i.val),f.seq t.val :=by
     simp only [Finset.sum_filter]; fin_cases i<;> fin_cases j<;>fin_cases k<;> norm_num [Ū,JetS.seq,Fin.sum_univ_three,pow_succ]
omit [Fintype I] in lemma seqSum (s:Finset I)(f:I→Token)(i:Phase): (∑ i∈s,f i).seq i.val=∑ j∈s, (f j).seq i.val:=by
      induction s using Finset.induction_on with
      | empty=> simp only [sum_empty]; fin_cases i<;>rfl
      | insert k s hi ih=>rw [sum_insert hi,sum_insert hi,← ih]; fin_cases i <;>rfl --] -- seq_add
-- polynomial pack
abbrev Spring (I: Type):= Phase→Curtain I
def Tide (S:Spring I)(d m:ℕ)(b:ℝ):Prop:=∀ i:Phase,Volume (S i) (d+i.val) m b
def go (p:Spring I)(d:ℕ)(a:deck I t)(x:Site t):Token:=let f(i:Phase):= Flair (p i) (d+i.val) a x; ⟨f 0,f 1,f 2⟩
def cups (p:Spring I)(d:ℕ)(x:Site t)(b:deck I t)(Z:E→L[ℝ] deck I t): ScriptJ E:=fun i:E=> go p d (b+Z i) x
omit [Fintype I] [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma cups_entry (p:Spring I)(i:Phase): lumps (cups p d j x Z) i= Char.Ωx (d+i.val) (p i) Z x j:=by fin_cases i<;>rfl
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma cupsB {c:ℝ}(P:Spring I)(h:Tide P d m c): ScriptJ.B (cups P d j x Z):= Xbond (chips (hp:=h 0)) (chips (hp:=h 1)) (chips (hp:=h 2))
end YM.OPE.Libra.Char
