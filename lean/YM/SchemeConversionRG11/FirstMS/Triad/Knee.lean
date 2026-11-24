import YM.SchemeConversionRG11.FirstMS.Triad.Solstice

/-! Sum a single helicity contraction to trident. Uniform soft limits across finite set. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {x:Nodes}{R ρ:ℝ}(h:Box x R ρ)(l:P→Stem)(hl:∀ i,(l i).loc=i)(j:P)(p:Bool)(m:Fin 3)

-- set D axis only

def incline (j:P)(l:P→Stem)(b:Axis) := update l j {l j with axis:=b}
private lemma primed (b:Axis)(i:P){x:Nodes} {v:E4}{t:ℝ} (hi:i∈Finset.univ.erase j): leg x (incline j l b) t i v = leg x l t i v:= by simp only [leg,incline,update_of_ne (Finset.ne_of_mem_erase hi)]
lemma incline_ignores (x:Nodes)(b:Axis)(t:ℝ): bypass x (incline j l b) j t=bypass x l j t:= by
   ext v; exact Finset.prod_congr rfl fun i hi=> primed l j b i hi

lemma live_signal (t:ℝ)(w:E4):
   clasp (l j).dual (l j).i p m t (w-x j)*bypass x l j t w=∑ a:Axis,∑ b:Axis,fan p m a b*softsphere x (incline j l b) j a t w:= by
   simp_rw [clasp,Finset.sum_mul,mul_assoc,softsphere, incline_ignores l j x, surface, incline,update_self]; -- softsphere needs unfold

def shot (t:ℝ)(w:E4):ℝ:=clasp (l j).dual (l j).i p m t (w-x j)*bypass x l j t w

include h
lemma shot_pays {t:ℝ}(ht:0<t): Integrable (shot (x:=x) l j p m t):= by
   change Integrable (fun v:E4=> shot (x:=x) l j p m t v); simp_rw [shot,live_signal]; exact integrable_finsetSum _ fun a _=> integrable_finsetSum _ fun b _=> (soft_integral h (incline j l b) a j ht).const_mul _

def spark_at (x:Nodes)(R ρ:ℝ):ℂ:=∑ a:Axis,∑ b:Axis,(fan p m a b:ℂ)*multiplies (incline j l b) j a x R ρ 0

include hl
lemma shotLimit : Tendsto (fun t=> (↑(∫ w, shot (x:=x) l j p m t w):ℂ)) (𝓝[>] 0) (𝓝 (spark_at l j p m x R ρ)):= by
   have hh(b k) : (incline j l b k).loc=k:= by by_cases hx:k=j<;> simp [incline,hx,hl]
   have hb:= tendsto_finsetSum (Finset.univ (α:=Axis)) (fun a _=> tendsto_finsetSum (Finset.univ (α:=Axis)) (fun b _=> (result h (incline j l b) j a (hh b) h.confirms).const_mul (↑(fan p m a b):ℂ)))
   refine hb.congr' ?_
   filter_upwards [self_mem_nhdsWithin] with t ht
   simp_rw [shot,live_signal]; rw [integral_finsetSum]; swap
   · exact fun i _=>integrable_finsetSum _ fun b _=> (soft_integral h _ _ _ ht).const_mul _
   simp_rw [integral_finsetSum _ (fun i _=> (soft_integral h _ _ _ ht).const_mul _),integral_const_mul, ofReal_sum,ofReal_mul]

end YM.SchemeConversionRG11.FirstMS.Triad
