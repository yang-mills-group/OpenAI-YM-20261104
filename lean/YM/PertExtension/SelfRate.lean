import YM.PertExtension.PacketFourier

/-! Recovering the infinite-volume covariance top Wick entry from a bare
Wilson even-torus rule, including flatness of the period difference relative to
any fixed spacing factor (fixed bare test slots). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection Normal Converter
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal RealInnerProductSpace FourierTransform
variable {G : Gauge} (q : ℕ+)

abbrev Atom (G : Gauge):= RG.Slot × G.ColorIndex
def atAddress (k:Atom G):Address G := ⟨k.1.offset,k.1.plaq,k.2⟩
private def constantD (t:Atom G):Degree G:=basic G t.1.plaq t.2

def selfFull (p s:Atom G) (t:ℕ):= direct G (side q t) 0 0 (atAddress p) (atAddress s)
local notation "reg" => (atTop:Filter ℕ)
variable (p s:Atom G)
variable {q} (hq:1<q.val)
lemma selfExact (q:ℕ+) t:selfFull q p s t=(if p.2=s.2 then incline p.1 s.1 (side q t) else 0).re:= by
   unfold selfFull direct stem incline Converter.position atAddress; simp
include hq
lemma builtin0 : Tendsto (fun t=>(selfFull (G:=G) q p s t:ℂ)) reg (nhds ((covarianceSymbol G).cov p s)):=by
  have hf:= (show ContinuousAt Complex.ofReal ((kernelEntry p.1 s.1:ℝ)) from Complex.ofRealCLM.continuous.continuousAt).tendsto.comp (incline_limit p.1 s.1 hq)
  by_cases h:p.2=s.2
  · rw [show (covarianceSymbol G).cov p s=(kernelEntry p.1 s.1:ℝ) from if_pos h]
    exact hf.congr (fun t=>by change (↑((incline p.1 s.1 (side q t)).re):ℂ)=_;rw [selfExact p s q t];rw [if_pos h])
  rw [show (fun t:ℕ=> (↑(selfFull (G:=G) q p s t):ℂ))=(fun _=>0) from funext fun t=>by rw [selfExact p s q t,if_neg h];rfl]
  exact (show Tendsto _ reg (nhds (0:ℂ)) from tendsto_const_nhds).mono_right (le_of_eq (congr_arg nhds (if_neg h).symm))

lemma shell_lip (a b:Degree G) (n:ℕ):∃ C>0, Lip (shell a b) 2 C ∧ Integrable (shell a b):= by
   obtain ⟨c,h⟩:=profile (G:=G) a b (max 1 n)
   have he:= h.cast.lips h.event (le_max_left 1 _) h.coast; exact ⟨max 1 c,lt_of_lt_of_le zero_lt_one (le_max_left ..),h.cast.coin (le_max_right ..)|>.lips h.event (le_max_left ..) (h.coast.trans (le_max_right ..)),Lip.int h.meas he⟩

lemma therm (a:ℕ) :
   Tendsto (fun t=>(magnify q t)^a • (selfFull q p s t-(covarianceSymbol G).cov p s :ℂ)) reg (𝓝 0):=by
    obtain ⟨D,hD,h⟩:=powder 2
    let f₀ (x y:Atom G):=shell (constantD x) (constantD y)
    obtain ⟨c,hc,hF,hS⟩:=show ∃ c>0,Lip (f₀ p s) 2 c∧ Integrable (f₀ p s) from shell_lip (G:=G) hq (constantD p) (constantD s) 1
    let z:=mapZ (p.1.offset-s.1.offset)
    let T:ℝ:= (harmon (f₀ p s) z).re
    let W(t):ℝ:=(side q t).val
    have hf t:selfFull q p s t=(stepsP (f₀ p s) (side q t) 2 z).re:=by
       have hh : captured 0 0 p.1.offset s.1.offset=z:= by unfold captured; rw [zero_add,zero_add]
       rw [← hh]; unfold selfFull f₀;exact direct_price (constantD p) (constantD s) (side q t) 0 0 _ _
    have he (b:ℕ)(k): ‖(magnify q k)^b • (T-selfFull q p s k)‖ ≤ magnify q k^b/W k*(D*c*(1+‖z‖)):= by
        rw [hf, norm_smul,Real.norm_of_nonneg (pow_nonneg (pow_nonneg (by positivity : (0:ℝ)≤(q:ℕ)) _) _), ←Complex.sub_re]
        have ht:=h (f₀ p s) c hc.le hS hF (side q k) z
        exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ht) (by positivity)).trans_eq (by ring)
    have hE (b:ℕ): Tendsto (fun k=>magnify q k^b*(T-selfFull q p s k)) reg (𝓝 0) := squeeze_zero_norm' (Eventually.of_forall (he b)) (by convert! (side_rate hq b).mul_const (D*c*(1+‖z‖)) using 1 <;> simp)
    have hT₀: Tendsto (fun t:ℕ=> selfFull q p s t) reg (nhds ((covarianceSymbol G).cov p s).re):= (show Tendsto (fun t:ℕ=> (↑(selfFull q p s t):ℂ).re) reg (nhds ((covarianceSymbol G).cov p s).re) from Complex.continuous_re.continuousAt.tendsto.comp (builtin0 p s hq))
    have hT' : Tendsto (fun t=> selfFull q p s t) reg (𝓝 T):= by
         convert! (hE 0).neg.add_const T using 2
         · simp [zero_smul, neg_sub]
         · simp
    have hT:=tendsto_nhds_unique hT' hT₀
    have hy : Tendsto (fun t=> (↑(-(magnify q t^a*(T-selfFull q p s t))):ℂ)) reg (𝓝 0):= by exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (hE a).neg)|>.mono_right (le_of_eq (by rw [neg_zero,Complex.ofReal_zero]))
    apply hy.congr
    intro t; dsimp; simp only [neg_mul_eq_mul_neg,neg_sub,Complex.ofReal_mul,Complex.ofReal_sub];rw [hT]
    refine congr_arg (fun x:ℂ => (magnify q t ^ a:ℝ)* (selfFull q p s t-x)) ?_
    change _= if p.2=s.2 then _ else 0
    split_ifs with h; simp [covarianceSymbol,h];simp [covarianceSymbol,h]
end YM.PertExtension.LatticePT
