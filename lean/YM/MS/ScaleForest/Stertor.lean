import YM.MS.ScaleForest.Backing
/-!
# Scalar estimate on the far side. IR limit of the continuum cumulant.

Even at rank zero, time integration acts only with a remainder small on the
long side. Prove for every m (parameter-uniform); include positive-rank decay too
(for that statement keep co-moving momentum units).
This drives the ordering of regulator removal for all histories with at least
two pins. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J E:Type} [TopologicalSpace I] {F:Curtain G I} {a b u R : ℝ} {p : ℤ}
   (w : ℕ)

omit [TopologicalSpace I] in
theorem backing_nil (t:ℝ) (z:ℂ)(x:I) : backing 0 F z t x w [] = F z t x w [] := by simp [backing,plow,mass,fieldDim,sr,amount]

omit [TopologicalSpace I] in
theorem levy_economy (ha : 0<a) (hb : 0<b) : Integrable (levy a b) := by
   apply integrableOn_univ.mp; rw [← Iic_union_Ioi (a:= (0:ℝ))]; refine IntegrableOn.union ?_ ?_
   · exact (integrableOn_exp_mul_Iic ha 0).congr_fun (fun i (hi:i≤0) => (ulev a b hi).symm ) measurableSet_Iic
   exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hb) 0).congr_fun (fun i (hi: 0 < i )=> (ilev a b hi.le).symm) measurableSet_Ioi

/-- Limit evaluation: only [] at rank zero can survive. -/
def bottomLine (F:Curtain G I) (w:ℕ) (z:ℂ)(x:I) : ℂ:= ∫ t, F z t x w []

variable (h : Waves R p F) (he: Envelope R a b F)
include he
omit [TopologicalSpace I] in
theorem priceScalar : ∃ C:ℝ,0<C∧∀ z:disc R,∀ (x:I) t, ‖F z t x w []‖ ≤ C*levy a b t := by
   obtain ⟨C,hC,k,hP⟩:= Arc.ride (he (Atlas I R) Prod.fst τtest ( Prod.snd ∘ Prod.snd) w ℝ []) 0; refine ⟨ C,hC,fun z x s=>?_⟩;
   simpa only [ norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,norm_zero,one_mul,one_pow,mul_one,fieldVal,Wire.sail,List.map_nil,τtest, Function.comp_apply ] using hP (z,s,x) (0:ℝ)

variable (ha : 0 < a) (hb : 0 < b) (x : I) (z : disc R)
include h ha hb

theorem eatScalar : Integrable (fun t=> F z t x w []) := by
   obtain ⟨C,hC,hP⟩:= priceScalar w he;
   exact ((levy_economy ha hb).const_mul C).mono' (((h.sway w []).comp (show Continuous (fun t:ℝ=> (show Atlas I R from (z,t,x))) by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun t=> hP z x t)

omit [TopologicalSpace I] h he ha hb in
private theorem nil_stat (t:ℝ) : vertical F z t x w []=∫ s in Iic t, F z s x w []:= by
   rw [← backing_nil (F:=vertical F),backingVert]; simp only [mend, backing_nil]
omit h [TopologicalSpace I] in

theorem zero_income : ∃ C:ℝ,0<C∧∀ z:disc R,∀ (i:I) t, ‖vertical F z t i w []‖ ≤ C := by
   obtain ⟨C,hC,hP⟩:= priceScalar w he; let D:= ∫ t,C*levy a b t; have ht: Integrable (fun t:ℝ=>C*levy a b t):= (levy_economy ha hb).const_mul C
   refine ⟨ max D 1,lt_max_of_lt_right zero_lt_one,fun z i s=>?_ ⟩; rw [nil_stat w]; refine (norm_integral_le_of_norm_le (ht.restrict) (Eventually.of_forall fun t=> hP z i t)).trans (le_max_of_le_left ((setIntegral_le_integral ht) ?_))
   exact Eventually.of_forall fun i:ℝ=> mul_nonneg hC.le (posLevy _ _ i).le

theorem breath : ∃ C:ℝ,0<C∧∀ i:I,∀ z:disc R,∀ t,0 ≤ t → ‖bottomLine F w z i-vertical F z t i w []‖ ≤ C*exp (-b*t):= by
   obtain ⟨C,hC,hP⟩:= priceScalar w he;
   refine ⟨ C/b,by positivity,fun i z t ht=>?_⟩; let V (s:ℝ):= F z s i w []
   have hV:= eatScalar w h he ha hb i z; unfold bottomLine; rw [nil_stat w];
   rw [ ← intervalIntegral.integral_Iic_add_Ioi (μ:=MeasureTheory.volume) (b:=t) (f:=V) hV.integrableOn hV.integrableOn,add_sub_cancel_left ];
   refine (norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (a:=-b) (by linarith) t).const_mul C) ((ae_restrict_mem measurableSet_Ioi).mono fun s hs=>?_)).trans ?_
   · obtain hp:= hP z i s; rw [ilev a b (ht.trans (mem_Ioi.mp hs).le)] at hp; exact hp
   rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]; apply le_of_eq; ring

theorem choke : Tendsto (fun t:ℝ=> vertical F z t x w []) atTop (𝓝 (bottomLine F w z x)) := by
   obtain ⟨C,hC,hP⟩:= breath w h he ha hb; have hx : Tendsto (fun t:ℝ=>C*exp (-b*t)) atTop (𝓝 0):= by
      have ht:= tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hb) tendsto_id )
      simpa only [mul_zero, comp_apply,id] using ht.const_mul C
   apply tendsto_iff_dist_tendsto_zero.mpr; apply squeeze_zero' (Eventually.of_forall fun i=> dist_nonneg) ?_ hx
   filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht; rw [dist_comm, dist_eq_norm]; exact hP x z t ht

def vcost (p : ℤ)(b : ℝ) := if p=0 then 0 else b

-- zero rank inside integration only sees output scalar []
theorem reserveVert (hp : b<1) : Envelope R a (vcost p b) (vertical F) := by
   obtain hB : 0≤a+b:= by linarith
   refine Envelope.paste (fun _ z s q _=> verticalU he h ha hB z s q) ?_
   intro J z s q hs; rcases eq_or_ne p 0 with hp'|hp'
   · simp [vcost,hp'];
     intro m E _ _ _ w
     by_cases hw:w=[]
     · subst w; obtain ⟨C,hC,hZ⟩:= zero_income m he ha hb; refine Costs.scalar (T:=(Arc.path 0).full) (S:=Arc.path 0) (g:=fun (_:J) (_:E)=>1) (p:=fun i=>vertical F (z i) (s i) (q i) m []) (?_)
       exact ⟨ C,hC,0,fun i _ _=>by simpa only [pow_zero,mul_one] using hZ (z i) (q i) (s i) ⟩
     obtain ⟨i,w',rfl⟩:= List.exists_cons_of_ne_nil hw
     unfold fieldVal; simp only [show ∀ j t, vertical F (z j) (s j) (q j) m (sail (i::w') t)=0 from fun j t=> ranks_off (VertRank _ _ h he ha hB (z j).property) _ (by simp [sail, hp']; omega ) ]; exact Costs.zero fun _ _ _=> zero_le_one
   unfold vcost; rw [if_neg hp']; exact verticalI he h ha hB hp hp' z s q

-- analytic and continuous in remaining parameters for IR limit before specializing

theorem breathes : Forest (disc R) (fun z=> bottomLine F w z x) := by
   intro z hZ
   obtain ⟨T,hT,hL⟩:= radius_pay isOpen_ball hZ; obtain ⟨C,hC,hP⟩:= priceScalar w he;
   exact (middle (μ:=MeasureTheory.volume) isOpen_ball (Eventually.of_forall fun t=> (h.hol t x).top w [])
      (fun i hi=> (eatScalar w h he ha hb x ⟨i,hi⟩).1) hT hL ((levy_economy ha hb).const_mul C) (Eventually.of_forall fun t j hj=> hP (⟨j,hL hj⟩:disc R) x t)).differentiableAt

theorem line_cont [FirstCountableTopology I] : Continuous (fun i:disc R × I=> bottomLine F w i.1 i.2) := by
   obtain ⟨C,hC,hP⟩:= priceScalar w he
   refine continuous_of_dominated (F:=fun (i:disc R × I) t=> F i.1 t i.2 w []) ?_ ?_ ((levy_economy ha hb).const_mul C) ?_
   · exact fun i=> (eatScalar w h he ha hb _ i.1).1
   · exact fun i=> Eventually.of_forall fun t=> hP i.1 i.2 t
   exact Eventually.of_forall fun t=> (h.sway w []).comp (show Continuous (fun i:disc R × I=> (show Atlas I R from (i.1,t,i.2))) by fun_prop)
end YM.MS.ScaleForest
