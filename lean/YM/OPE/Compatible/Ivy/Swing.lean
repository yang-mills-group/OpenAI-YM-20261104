import YM.OPE.Compatible.Ivy.Kite
/-!
# script spectator off-site gets heat alignment never moving inputs to update S. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable [Fintype I]{k m d n e:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S: Story I} {P:Curtain I}{t:Side}{x:deck I t}{j:Site t}
variable {Z:E→L[ℝ] deck I t}
def sizN (d:ℕ) (i:Ask) := if i=4 then d else sizes i
private lemma rune (d:ℕ)(i:Ask)(h:i≠ 4): sizN d i=sizes i:= if_neg h
private lemma runeD (d:ℕ):sizN d 4=d:= if_pos rfl
def Quip (a:Script I d)(S:Story I)(i:Ask) : Script I (0+sizN d i):= if h:i=4 then Shell.slice (finCongr (by rw [h, runeD,Nat.zero_add])) a else Shell.slice (finCongr (by rw [rune d i h])) (Paloma S i)
private def dustX {N:Side}(t:Site N)(j:Ask):Option (Site N):= if j=4 then some t else none -- n implicit wrong
-- use fi_eq; budget j before Q. construct
variable {C:ℕ→ℝ}{c v:ℝ}
lemma comet (i:Phase)(s:Meeting)(h:s∈Plans i)(d e:ℕ)(m n:ℕ)(a σ:ℝ)(C:ℕ→ℝ)(hp:n+HueS (insert 4 s)≤m)(hx:0<σ)(ha:0≤a)(hC:0≤C):
    ∃ D:ℝ, 0 ≤ D∧ ∀ (t:Side)(E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (L: Law E)(Ω:Row I I), Ω.strip σ a→∀ (S: Story I)(x:deck I t)(c:ℝ)(Z:E→L[ℝ] deck I t)(b s':Site t), Ribbon S Ω Z L x b m C c → Cold b s' (Oriel L Z) (C m) m → (∀ i≤m,Cold b s' (Oriel L Z) (C i) i) →∀ w, weightsB S m w → forall f:Script I d,forall q:Script I e,∀ u v, soot m f u→soot m q v→ Mold (πc μ L s (Char.Sketch S c x Z) (flash f Z x b) (flash q Z x s') 4) 0 (D*u*v*Visit w s*(1+‖x‖)^(extendK d i+e)) t n:=by
         have h4:= rows i s h; let E':= insert 4 s; obtain ⟨D,hD,H⟩:= lux (s:=E') (v:=sizN e) (w:=fun _=>0) (I:=I) (d:=d) (e:=0) hx ha hC hp
         refine ⟨D,hD,?_⟩; intro t E _ _ _ _ _ μ _ L Ω hΩ S x c Z b s' hR ht hK w hw f q u v hu hv; let F:= Quip q S; let B:= dustX s'; let T:= B
         let W(j:Ask):= if j=4 then v else w j; have hv' :0 ≤ Visit w s:= Visit0 (covers hw); let X:= Fig (sizN e) (fun _=>0) F B c x Z; let f':=Char.Sketch S c x Z;let p:= flash f Z x b; let P:=flash q Z x s'; have hh : coversB (sizN e) (fun _=>0) F m W E':=by
             intro j hj; unfold F Quip W; split
             next h=> exact slice_fee _ _ hv
             next h=> exact slice_fee _ _ (hw _)
         have he : okP X E':= branches _ _ _ _ _ _ _; have hY:Buds Ω L x C Z (w:=fun (_:Ask)=>0) (v:=sizN e) F b E' B m c :=by
             refine ⟨hR.amp,hR.fee,fun j hj=> ?_⟩; rcases Finset.mem_insert.mp hj with h|h'
             · subst j; exact hK
             have hk:j≠4:=fun e=>h4 (e ▸ h'); fin_cases j <;> first| exact hR.xL 0| exact hR.xL 1| exact hR.xL 2| exact hR.xL 3 | simp at hk
         have hp' : Tap μ L X p E'=πc μ L s f' p P 4:=by
             apply fi_eq; intro j hj
             rcases Finset.mem_insert.mp hj with h|hr
             · subst j; unfold Cosis;rw [Function.update_self]; ext i; change SX x x Z _ i (d:=sizN e 4) (e:=0)=_; -- cast issue
               exact senses q i (sootS (slice_fee _ _ hv))
             have hk:j≠4:=fun e=>h4 (e ▸ hr); unfold Cosis; rw [Function.update_of_ne hk]; fin_cases j <;>first | (rfl) | (simp at hk)
         let k:=Rollup (sizN e) (fun _=>0) E' d 0; have hk:k≤extendK d i+e:=by
             have hl:=enoughK d s i h; unfold Rollup at *; unfold k Rollup; rw [Finset.sum_insert h4, runeD, show (∑ j∈s,(sizN e j+0))=(∑ j∈s,(sizes j+0)) from sum_congr rfl (fun i hi=>by rw [rune e i (fun e=>h4 (e ▸ hi))])]; simp only [add_zero] at hl ⊢; omega
         have hP:= H _ μ L Ω hΩ t _ Z b _ c x hY W hh (wrapPlus f) u (slice_fee _ _ hu) k le_rfl
         have hz : Shell.Hall Ω (sizN e) (fun _=>0) F (LightX∘ B) E' d 0 (wrapPlus f)=0 := unfit (i:= (4:Ask)) (mem_insert_self ..) (by unfold B dustX; simp [LightX]) _
         have hU := Sack.coins hu; have hv := Sack.coins hv
         change Mold (Tap μ L X (SX x x Z _ (e:=0) (d:=d)) E') _ _ _ _ at hP; rw [← hp']; rw [hz,flair0, show SX x x Z (orchestra (wrapPlus f) b) (e:=0) (d:=d)=p from funext fun i=> senses f i (sootS (slice_fee _ _ hu)), show Visit W E' = v*Visit w s from ?_] at hP; apply hP.trans; rw [←mul_assoc (D*u)]; apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) hk); positivity
         unfold Visit E'; rw [prod_insert h4]; apply congr_arg₂; · exact if_pos rfl
         exact Finset.prod_congr rfl fun i hi=> if_neg (fun (e:i=4)=> h4 (e ▸ hi))
end YM.OPE.Libra.Char
