import YM.OPE.Compatible.Ivy.Four
/-!
# small p rank sum. Field input laws after ports. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E:Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {k m d e n:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S:Story I}{P:Curtain I}{t:Side}{x:deck I t}{j:Site t}{Z:E→L[ℝ] deck I t}
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma sketchV (p:Story I)(b:ℝ): Char.Sketch p b x Z 0=Char.Sketch p b x Z 1:=rfl -- might need Fintype
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma sketchB (p:Story I)(b:ℝ): ∀ i,Bond (Char.Sketch p b x Z i):=fun _=>cueBond ..  -- ∀
omit [Fintype I] in lemma leaps (P:Spring I)(k:Phase): (go P d x j).seq k.val=Flair (P k) (d+k.val) x j:=by fin_cases k <;>rfl
-- END single tx k p with cost. cumulative
lemma iris (p:Phase)(d m n:ℕ)(s K:ℝ)(C:ℕ→ℝ)(hs:0<s)(ht:0≤K)(hr:0≤ C)(hp:n+44≤m):∃ A:ℝ,0 ≤ A∧ ∀ (t:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I),Ω.strip s K→∀ (S:Story I)(c:ℝ)(x:deck I t)(Z:E→L[ℝ] deck I t)(b:Site t),Ribbon S Ω Z L x b m C c→∀ w:ℝ, 1 ≤ w → weightsB S m (fun _=> w)→∀ P:Spring I,∀ f:ℝ,Tide P d m f→ let Y:= Mouth Ω S P d; Volume (Y p) (d+p.val) m (A*w^5*f) ∧ Mold ((fair μ L (Stell (Char.Sketch S c x Z)) (cups P d b x Z)).seq p.val) ((go Y d x b).seq p.val) (A*w^5*f*(1+‖x‖)^glideZ d) t n:=by
        classical
        choose! D hD H using fun i j hj=> mountK (I:=I) p i j hj d n m s K C hs ht hr hp
        let f(i):= ∑ j∈Strut p i,D i j; refine ⟨∑ i:Phase,f i,sum_nonneg (fun i _=> Finset.sum_nonneg (fun j hi=> hD i j hi)),?_⟩; intro t E _ _ _ _ _ μ _ L Ω hΩ S c x Z b hB w hw hW P v hT Y
        let K':= Char.Sketch S c x Z; let q:= cups P d b x Z; let U(i j:Phase):= stretchH Ω S (P i) d i j; have he(i j)(hj:j∈Strut p i):= H i j hj t _ μ L Ω hΩ S c x Z b hB w hw hW (P i) v (hT i); let A:= (1+‖x‖)^glideZ d
        let d' := d+p.val;let X(i):=∑ j∈Strut p i,U i j; have hx(i j)(hj:j∈Strut p i): Volume (U i j) d' m (D i j*w^5*v):=(he i j hj).1; have hh(i): Volume (X i) d' m (f i*w^5*v):=by unfold X f; rw [sum_mul,sum_mul]; exact Volume.sum _ _ _ (hx i)
        have hr(i): Mold ((Conf μ L K' q i).seq p.val) (Flair (X i) d' x b) (f i*w^5*v*A) t n:=by
            unfold Conf q; rw [shiftH, cups_entry,show Flair (X i) d' x b= _ from flairS _ _ _ _ (fun j hj=>Volume.bound _ (hx i j hj)), show (f i*w^5*v*A)=∑ j∈ Strut p i,D i j*w^5*v*A from ?_]; exact moldSum (fun j hj=> (he i j hj).2)
            unfold f; rw [sum_mul,sum_mul,sum_mul]
        refine ⟨?_,?_⟩
        · rw [sum_mul,sum_mul]; exact Volume.sum X _ _ (fun i _=> hh i)
        erw [bumper _ _ K' (sketchV _ _) (sketchB _ c) q (cupsB _ hT), seqSum,leaps, show Flair (Y p) _ _ _=_ from flairS d' x b _ (fun i _=>Volume.bound _ (hh i)),sum_mul,sum_mul,sum_mul]; exact moldSum fun i _=> hr i
end YM.OPE.Libra.Char
