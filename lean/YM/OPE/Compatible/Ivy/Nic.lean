import YM.OPE.Compatible.Ivy.Silts
/-!
# cross! product lens after all horizons still same. not Fourier
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E:Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {k m d e n:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S:Story I}{P:Curtain I}{t:Side}{x:deck I t}{j:Site t}{Z:E→L[ℝ] deck I t}
lemma sniff (p i j t:Phase)(h:t∈shout p i j) (d e k n:ℕ)(a σ:ℝ)(C:ℕ→ℝ)(hs:n+44≤k)(hp:0<σ)(hx:0≤a)(hc:0 ≤ C):∃ D:ℝ,0 ≤ D∧ ∀ (u:Side)(E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I), Ω.strip σ a→∀ (S:Story I)(x:deck I u)(b:ℝ)(Z:E→L[ℝ] deck I u)(z y:Site u), Ribbon S Ω Z L x z k C b→(∀ j ≤ k, Cold z y (Oriel L Z) (C j) j)→∀ w:ℝ,1 ≤ w→weightsB S k (fun _=>w)→∀ f g:Curtain I,∀ v v':ℝ,Volume f (d+i.val) k v→Volume g (e+j.val) k v'→
    Mold ((rich fun s=> πc μ L s (Char.Sketch S b x Z) (Char.Ωx (d+i.val) f Z x z) (Char.Ωx (e+j.val) g Z x y) 4).seq t.val) 0 (D*w^5*v*v' *(1+‖x‖)^glideZ (d+e)) u n :=by
       choose! D hd H using fun s h=> conox (I:=I) t s h (d+i.val) (e+j.val) k n a σ C ((whorl n (insert 4 s)).trans hs) hp hx hc
       let R(i):= ‖meter i‖ * D i; refine ⟨∑ i∈ Plans t, R i,sum_nonneg (fun i hi=>mul_nonneg (norm_nonneg _) (hd i hi)),?_⟩; intro u E _ _ _ _ _ μ _ L Ω hΩ S x b Z z y hB hA w hw hW f g v v' hf hg
       let C':=(1+‖x‖)^glideZ (d+e); let K(i):=R i*w^5*v*v'*C'; let s:= Plans t; let U(S'):=(πc μ L S' (Char.Sketch S b x Z) (Char.Ωx (d+i.val) f Z x z) (Char.Ωx (e+j.val) g Z x y) 4); let X(i):=meter i*U i
       have he(a)(ha:a∈s):Mold (X a) 0 (K a) u n:=by
            have he:= sculpt (H a ha u E μ L Ω hΩ S _ _ _ _ _ hB hA _ hW f g v v' hf hg) (meter a); rw [mul_zero] at he; let V:=Visit (fun (_:Ask)=>w) a; have hv:= Sack.coins (hf.2 0); have hv':= Sack.coins (hg.2 0); have hd:= hd a ha; have hP: extendK (d+ i.val) t+(e+j.val) ≤ glideZ (d+e):=by
                  have he := Finset.mem_filter.mp h; unfold extendK glideZ; have hp:p.val<3:= p.isLt; omega
            refine he.trans ((mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left (π_bd w a hw) (by positivity : 0 ≤ D a*v*v')) (pow_le_pow_right₀ (by simp : (1:ℝ)≤1+‖x‖) hP) (by positivity) (by positivity)) (norm_nonneg _)).trans_eq ?_); unfold K R C'; ring -- C order
       rw [role]; have hf:=moldSum he; rw [sum_const_zero] at hf; apply hf.trans_eq
       unfold K; rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
lemma marvel (p:Phase)(d e k n:ℕ)(a σ:ℝ)(C:ℕ→ℝ)(hs:n+44≤k)(hp:0<σ)(hx:0≤a)(hc:0 ≤ C):∃ D:ℝ,0 ≤ D∧∀ (t:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] (μ: Measure E)[μ.IsAddHaarMeasure](L:Law E)(Ω:Row I I),Ω.strip σ a→∀ (S: Story I)(x:deck I t)(c:ℝ)(Z:E→L[ℝ] deck I t)(i j:Site t),Ribbon S Ω Z L x i k C c→(∀ a≤ k,Cold i j (Oriel L Z) (C a) a)→∀ w:ℝ,1 ≤ w→weightsB S k (fun _=>w)→∀ A B:Spring I,∀ c' d':ℝ,Tide A d k c'→Tide B e k d'→
     let F:=fair μ L (Stell (Char.Sketch S c x Z)); let f:=cups A d i x Z; let g:=cups B e j x Z
     Mold ((F (f*g)-F f *F g).seq p.val) 0 (D*w^5*c'*d'*(1+‖x‖)^glideZ (d+e)) t n:=by
          choose! K hK H using fun i j t h=>sniff (I:=I) p i j t h d e k n a σ C hs hp hx hc; let B(i j):=∑ t∈shout p i j,K i j t; let Y(i):=∑ j:Phase,B i j; refine ⟨∑ i:Phase,Y i, sum_nonneg (fun i _=>sum_nonneg fun j _=>sum_nonneg fun t ht=> hK i j t ht),?_⟩; intro t E _ _ _ _ _ μ _ L Ω hΩ S x c Z i j h hA w hw hW A B' c' d' hp₀ hp₁ F f g; rw [show F (f*g)-F f *F g=_ from centered μ L _ (sketchV ..) (sketchB _ _) _ _ (cupsB _ hp₀) (cupsB _ hp₁),seqSum]; let W:= (1+‖x‖)^glideZ (d+e)
          let hP:=Char.Sketch S c x Z
          have he(u v:Phase): Mold ((Cox μ L hP f g u v).seq p.val) 0 (B u v*w^5*c'*d'*W) t n:=by
               unfold Cox; rw [shiftP]
               rw [show lumps f u= _ from cups_entry .., show lumps g v=_ from cups_entry ..]; unfold B; rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
               have hh:= moldSum fun t ht=> H u v t ht _ _ μ L Ω hΩ S x c Z i j h hA w hw hW (A u) (B' v) c' d' (hp₀ u) (hp₁ v); rw [sum_const_zero] at hh; exact hh
          have hh(u):= moldSum (s:=Finset.univ) (fun v _=>he u v); have ht:= moldSum (s:=Finset.univ) (fun u _=> hh u); simp_rw [sum_const_zero] at ht; simp_rw [seqSum]; apply ht.trans_eq; unfold Y; simp_rw [sum_mul];rfl
end YM.OPE.Libra.Char
