import YM.SchemeConversionRG11.FirstMS.Triad.Hinge
import YM.Pert.Triangle.Estimate

/-! Single basis choices, distinct V branch. Fold in C_b/C_U for top ext slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {x:Nodes}{R ρ:ℝ}(h:Box x R ρ) (w:P→Fin 3)

-- contraction in cyclic color order. nonlinear mark j over a b full antisymmetric sum;
-- two pairings already combined (cancel 1/2).
def atMarkQ (x:Nodes)(j:P)(z:ℂ):ℂ:= ∑ c:Axis,∑ d:Axis,(fan (glow j) (w j) c d:ℂ)*
   lane z (glow (slide j)) (w (slide j)) c (x j-x (slide j)) 0 *
   lane z (glow (lag j)) (w (lag j)) d (x j-x (lag j)) 0

def paths (x:Nodes)(R ρ:ℝ)(z:ℂ):ℂ:=∑ j:P,(atMarkQ w x j z-pass w x R ρ j mainPair z)

lemma parts (k:P)(b c d:Axis)(x:Nodes)(v:E4): bypass x (stove w (orderP k b c d)) k 0 v=
     soff (glow (slide k)) (w (slide k)) c 0 (v-x (slide k))*soff (glow (lag k)) (w (lag k)) d 0 (v-x (lag k)) := by
   unfold bypass; rw [flood_load,Finset.prod_pair (Ne.symm (neg3 k))]; simp only [leg,stove,stern,abaft]
lemma launch (m:Fin 3)(a:Axis)(v:E4): soff false m a 0 v=mLine m a v:= by simp [soff,mLine,sol,flow,soften_zero]

include h
lemma cancelled (j:P)(he:j≠0): atMarkQ w x j 0= 2*pass w x R ρ j (stemTensor false) 0:= by
   rw [collect]
   have hb : ∀ c d:Axis,(stove w (orderP j 0 c d) j).dual=false:= fun _ _=>by simp [stove,glow,he]
   have hp(c d:Axis)(m:Fin 3):spark_at (stove w (orderP j 0 c d)) j false m x R ρ=(if w j=m then 2⁻¹ else 0:ℂ)*(↑(bypass x (stove w (orderP j 0 c d)) j 0 (x j)):ℂ):= by
      have he':= pierce h (stove w (orderP j 0 c d)) j m (fun _=>rfl); rw [hb] at he'; exact he'
   unfold fair; simp_rw [hp]; rw [Finset.sum_eq_single_of_mem (w j) (Finset.mem_univ _) (fun m hm hi=> ?_)]
   · unfold atMarkQ; simp only [parts, glow,he,decide_false, ↓reduceIte, Finset.mul_sum]
     apply Finset.sum_congr rfl; intro c _; refine Finset.sum_congr rfl fun d _=> ?_
     rw [kernel_real _ _ _ (sub_ne_zero.mpr (h.confirms.ne (Ne.symm (neg1 j)))),kernel_real _ _ _ (sub_ne_zero.mpr (h.confirms.ne (Ne.symm (neg2 j)))),ofReal_mul]; ring
   simp [Ne.symm hi]
lemma terminalQ : atMarkQ w x 0 0=↑(terminal (x 1) (x 2) (x 0) (w 0) (w 1) (w 2)) := by
   unfold atMarkQ; simp only [show slide 0=1 from (by decide), show lag 0=2 from (by decide),show glow 0=true from (by decide),show glow 1=false from (by decide),show glow 2=false from (by decide)]
   unfold terminal; rw [ofReal_sum]; refine Finset.sum_congr rfl fun c _=>?_
   rw [ofReal_sum]; refine Finset.sum_congr rfl fun d _=> ?_
   rw [kernel_real _ _ _ (sub_ne_zero.mpr (h.confirms.ne (by decide : (0:P)≠1))),kernel_real _ _ _ (sub_ne_zero.mpr (h.confirms.ne (by decide : (0:P)≠2))),launch,launch, ofReal_mul,ofReal_mul]; ring

local notation "zoneQ" => zone (x 0) (x 1) (x 2)
lemma circuit (m:Fin 3) : fair w x R ρ 0 m= ↑(against (w 0) m (w 1) (w 2) (x 0) (x 1) (x 2)):= by
   let l(c d:Axis):= stove w (orderP 0 0 c d); let A(c d:Axis):= tread x (l c d) m; let B(c d:Axis) := frolic x (l c d) m
   let I(c d: Axis):ℝ:= (∫ v in zoneQ, A c d v)+(∫ v in zoneQᶜ,B c d v)
   have he(c d:Axis):spark_at (stove w (orderP 0 0 c d)) 0 false m x R ρ=(↑(I c d):ℂ):= opponent x (l c d) m h.confirms (by simp [l,stove,glow]) h (fun i=>rfl)
   unfold fair; simp_rw [he,← ofReal_mul,← ofReal_sum]; congr 1
   have hp(c d:Axis)(v): bypass x (l c d) 0 0 v = mLine (w 1) c (v-x 1)*mLine (w 2) d (v-x 2):= by
      unfold l; rw [parts,show slide 0=1 from (by decide), show lag 0=2 from (by decide), show glow 1=false from (by decide),show glow 2=false from (by decide), launch, launch]
   let M(c d:Axis)(v:E4):= fan false m c d*A c d v
   let N(c d:Axis)(v:E4):= fan false m c d*B c d v
   have ha(c d):IntegrableOn (M c d) zoneQ:= ((inside_zero x _ m h.confirms (show (l c d 0).dual=true from by simp [l,stove,glow])).1).const_mul _
   have hb(c d):IntegrableOn (N c d) zoneQᶜ:= ((outside_zero x _ m h.confirms (show (l c d 0).dual=true from by simp [l,stove,glow]) h).1).const_mul _
   let f(v:E4):= mixed (w 0) m (x 0-v); let g:=integralInput m (w 1) (w 2) (x 1) (x 2)
   have hm(w): (∑ a:Axis,∑ b:Axis,M a b w)= f w*(g w-g (x 0)):= by
      unfold M A tread; simp_rw [hp]; change ∑ a:Axis,∑ b:Axis,fan false m a b*(f w*(_-_))=_
      unfold g integralInput; simp only [← Finset.sum_sub_distrib,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun b _=> by ring
   have hn(w): (∑ a:Axis,∑ b:Axis,N a b w)= f w*g w:= by
      unfold N B frolic; simp_rw [hp]; change ∑ a:Axis,∑ b:Axis,fan false m a b*(f w*(_*_))=_
      unfold g integralInput; simp_rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun b _=>by ring
   have hi(c d:Axis): fan false m c d * I c d=(∫ v in zoneQ, M c d v)+(∫ v in zoneQᶜ,N c d v):=by unfold I M N;rw [mul_add,integral_const_mul,integral_const_mul]
   simp_rw [hi,Finset.sum_add_distrib,← integral_finsetSum _ (fun c _=> ha _ c),← integral_finsetSum _ (fun c _=> hb _ c),←integral_finsetSum _ (fun c _=> integrable_finsetSum _ (fun d _=>ha c d)),←integral_finsetSum _ (fun c _=> integrable_finsetSum _ (fun d _=>hb c d)),hm,hn]
   unfold against; congr 1
   · exact (integral_indicator (f:=fun v=> f v*(g v - g (x 0))) (s:=zoneQ) (isClosed_closedBall.measurableSet)).symm
   refine Eq.trans ((integral_indicator (μ:=volume) (f:=fun v=>f v*g v) (s:=zoneQᶜ) (isClosed_closedBall.measurableSet.compl)).symm) (integral_congr_ae (Eventually.of_forall fun v=> ?_)); by_cases he:v∈zoneQ <;> simp [f,g,outerZone,he]

lemma gets : paths w x R ρ 0 = (impact (x 1) (x 2) (x 0) (w 0) (w 1) (w 2) :ℂ):= by
   unfold paths; rw [Finset.sum_sub_distrib,port_anti h w, ← Finset.sum_sub_distrib,Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _) (fun i _ hi=>sub_eq_zero.mpr (cancelled h w i hi)),collect, terminalQ h w]; unfold impact; push_cast; simp_rw [circuit h]

lemma pass_bill (j:P): AnalyticAt ℂ (atMarkQ w x j) 0:= by
   let he (k:P)(b:Axis)(hp:k≠j): AnalyticAt ℂ (fun z:ℂ=> lane z (glow k) (w k) b (x j-x k) 0) 0:= by
      let v:= x j-x k; have hh:(v,(0:ℝ))∈region:= by change 0<‖v‖^2+0; have h':0<‖v‖:=norm_pos_iff.mpr (sub_ne_zero.mpr (h.confirms.ne (Ne.symm hp))); exact lt_of_lt_of_le (sq_pos_of_pos h') (le_add_of_nonneg_right (by norm_num))
      exact DifferentiableOn.analyticAt (fun z hz=> ((off_lane (glow k) (w k) b).colors _ hz _ hh).differentiableWithinAt) (opened.mem_nhds occurs)
   apply Finset.analyticAt_fun_sum; intro c _; apply Finset.analyticAt_fun_sum; intro d _
   exact (analyticAt_const.mul (he _ c (neg1 _))).mul (he _ d (neg2 _))

lemma responsive : aim (paths w x R ρ) (↑(impact (x 1) (x 2) (x 0) (w 0) (w 1) (w 2))) := by
   rw [← gets h w]; apply aim.bag; intro j _
   have hg : aim (pass w x R ρ j mainPair) (pass w x R ρ j mainPair 0):= by
      unfold pass; apply aim.bag; intro a _; apply aim.bag; intro b _; apply aim.bag; intro c _; apply aim.bag; intro d _
      exact (atMark (analyticAt_const (v:=mainPair a b c d))).prod_goal (distinct_zero h _ _ _ (fun i=>show (stove w (orderP j b c d) i).loc=i from rfl))
   obtain ⟨g,hh,hE,hv⟩:= hg.arc
   exact ⟨atMarkQ w x j-g, (pass_bill h w j).sub hh, EventuallyEq.rfl.sub hE, by rw [Pi.sub_apply,hv]⟩
end YM.SchemeConversionRG11.FirstMS.Triad
