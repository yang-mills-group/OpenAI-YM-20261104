import YM.MS.Rake.Deliver
/-!
# Uniform compact-time/window estimates on cylinder symbols
No assumption in y when point sampled other parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open scoped Topology ContDiff Interval
variable {G:Gauge} {I E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 {S:Scale I}{K:Belt I}{C T r:ℝ}{z:I→ℂ}{b c:Bool}{t n:ℕ}{a y w:I→ℝ}
-- take compact displacement.Both lines & lenses.
def Villa (F:ℝ→E→ℂ) (T:ℝ) (j:ℕ)(H:Set E): Prop:= ∃ C:ℝ,0<C∧∀ t:ℝ,‖t‖≤T→∀ p∈H, ‖iteratedFDeriv ℝ j (F t) p‖≤C
variable {U:ℝ→E→ℂ}
lemma Villa.compact (h:ContDiff ℝ ∞ ( uncurry U )) (T:ℝ)(j:ℕ){p:Set E}(hp:IsCompact p): Villa U T j p:= by
   let P:= Metric.closedBall (0:ℝ) T; let F:= fun v=>‖iteratedFDeriv ℝ j (uncurry U) v‖; have hF : Continuous F:= ( h.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast le_top)).norm; obtain ⟨v,h⟩:= (( ( isCompact_closedBall 0 T ).prod hp).image hF).bddAbove; exact ⟨ max v 1, lt_max_of_lt_right zero_lt_one, fun i hi p hp=> le_max_of_le_left (( norm_extDer (f:=uncurry U) (by assumption) i p j ).trans ( h ( Set.mem_image_of_mem _ ( show (i,p)∈ P ×ˢ _ from ⟨ Metric.mem_closedBall.mpr (by simpa using hi), hp⟩)))) ⟩
lemma Villa.moves (h:ContDiff ℝ ∞ ( uncurry U )) [ProperSpace E]{C:ℝ}(hp:∀ t v,∃ x:E,‖x‖≤C∧∃ k:ℂ,‖k‖=1∧ (fun y=> U t (y+(v-x)))=k • U t) (z:ℝ)(j:ℕ): Villa U z j Set.univ := by
    obtain ⟨T,hT,hx⟩:= Villa.compact h z j ( isCompact_closedBall 0 C ); refine ⟨ _,hT,?_⟩; intro t ht v _; obtain ⟨x,hP,k,hk,hr⟩:=hp t v; have hv: ContDiff ℝ ∞ (U t):= h.comp (f:=fun p:E=>(t,p)) (contDiff_const.prodMk contDiff_id)
    have he: iteratedFDeriv ℝ j (U t) v=k•iteratedFDeriv ℝ j (U t) x:= by rw (occs:=.pos [1]) [show v=x+( v-x ) from (by abel)]; rw [ ← iteratedFDeriv_comp_add_right, hr]; exact iteratedFDeriv_const_smul_apply ( hv.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [he,norm_smul,hk,one_mul]; exact hx _ ht x (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hP))
lemma season (h:ContDiff ℝ ∞ ( uncurry U ))(hs: ∀ i,1 ≤ S.length i)(hx:∀ i,‖a i‖≤T)(he:∀ j,Villa U T j Set.univ): Bound S (fun i => U (a i)) 1:= by
    refine ⟨fun i=> h.comp (f:=fun p:E=> (a i,p)) (contDiff_const.prodMk contDiff_id),fun j=>?_⟩; obtain ⟨C,hC,hp⟩:= he j; refine ⟨C,hC,0,fun i p _=> ( hp _ (hx i) p (Set.mem_univ _)).trans ?_⟩; simp only [pow_zero,Pi.one_apply,mul_one,one_mul]; exact le_mul_of_one_le_right hC.le (one_le_pow₀ (hs i))
-- Lattice log lines and derivatives. continuity plus quasi. also damped late-time restriction later.
abbrev LowP (G:Gauge)(t:ℝ): Edge G:= ( High.spaceL G ).meter t
def spread (K:Edge G) : Edge G:= fun i j p=> ( aisle p:ℂ)* K i j p
def PlanetL (G:Gauge)(t:ℝ): Edge G := spread (LowP G t)
lemma scaleL (G:Gauge)(t:ℝ): LowP G t=( exp t:ℂ ) • Cpu G (exp t) := Wind.weight_day t
lemma nearL (G:Gauge)(t:ℝ): City.Near (LowP G t):= by rw [scaleL]; intro q i j p; simp_rw [Pi.smul_apply, L_stamp (exp t) q i j p, smul_eq_mul]; ring
lemma continuousLb (G:Gauge)(i j:BH G)(p:QP): Continuous (fun t=> LowP G t i j p) := by simp_rw [scaleL, Pi.smul_apply]; exact (Complex.continuous_ofReal.comp Real.continuous_exp).smul (( main_f G i j ).continuous.comp (f:=fun t=> (exp t,p)) ( by fun_prop ) )
lemma vary_up (i j:BH G)(T:ℝ): ∃ C:ℝ,0<C ∧ ∀ k, Villa (fun t:ℝ=>Cpu G t i j) T k Set.univ:= by
    let F(t:ℝ):=Cpu G t i j; refine ⟨1,zero_lt_one,fun k=>?_⟩; letI: ProperSpace QP:= FiniteDimensional.proper ℝ _; refine Villa.moves ( C:= 4*π ) (E:=QP) ( U:=F ) (main_f G i j) ?_ _ _; intro s p;
    obtain ⟨u,v,h,h'⟩:= Wind.realm (fun _:Unit=>p); let y:=u (); refine ⟨ y,( norm_le_pi_norm u () ).trans h,?_⟩; let c:=v (); have he : p-y= Tone.rep (c+c):= sub_eq_iff_eq_add.mpr (by obtain hx:= congr_fun h' (); simp only [map_add]; exact hx.trans (add_comm y (amt v ()))); rw [he]; exact cityLine ( L_stamp s ) i j ( c+c )
variable (hA: ∀ i,exp (a i) ≤ T)(hT:∀ i,S.length i=1)
include hA hT
lemma burn_core (i j: BH G): Bound S (fun s=> Cpu G (exp ( a s )) i j) 1:= by obtain ⟨C,hC,h⟩:=vary_up i j T; exact season ( main_f G i j ) (fun i=> (hT i).ge) (fun i=> by rw [Real.norm_of_nonneg (exp_pos _).le]; exact hA i) h
lemma cost_L0 : CourseK S (fun i=> exp ( a i )) (fun i=> LowP G ( a i )):= by
    intro i j; simp_rw [ hT,one_zpow,one_mul, scaleL, Pi.smul_apply ]; have he : Bound S (fun i (_:QP)=>exp (a i)) (fun i=> exp (a i)):= Costs.scalar ( Cost.of_le fun i p hp=> (norm_of_nonneg (exp_pos (a i)).le).le ); convert! ( he.ofReal.mul ( burn_core hA hT i j )) using 1; ext i; simp
lemma crown : Sheet S (fun i=>exp (a i)) (fun i=>PlanetL G (a i)):= by
   intro i j; refine folding ?_ (fun k=>cityLine (nearL G (a k)) i j) (fun i=>(hT i).ge); simp_rw [hT,one_zpow,one_mul]; intro b; have h:=cost_L0 hA hT ( G:=G ) i j; simp_rw [hT,one_zpow,one_mul] at h
   refine ⟨h.smooth,fun k=>?_⟩; obtain ⟨C,hC,k',hk⟩:=h.quoted k; let B:=1+π; have hB:B>0:= by unfold B; positivity
   refine ⟨ C*(B^( k'+b )),mul_pos hC (pow_pos hB _),k',fun i p hp=>(hk i p trivial).trans ?_⟩; have hv : S.weight i p ≤ B:= by unfold Scale.weight; rw [hT i, one_mul]; refine add_le_add_right ?_ 1; simpa [Scale.strict,firstZone] using hp -- cost display
   have hz:= S.weight_pos i p; have ht:=S.basic_pos i; have hw:= S.pos i
   simp only [hT,Scale.strict,Scale.full,one_pow,mul_one]; -- hp also
   rw [ ← mul_div_assoc, le_div_iff₀ (pow_pos hz _),pow_add ]; calc
          _ ≤ C * (S.basic i * B)^k' * exp (a i) * B^b := by gcongr
          _ = _ := by rw [mul_pow]; ring
end YM.MS.Rake
