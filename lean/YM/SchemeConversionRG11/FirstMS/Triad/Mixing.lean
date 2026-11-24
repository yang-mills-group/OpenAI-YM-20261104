import YM.SchemeConversionRG11.FirstMS.Triad.Regular
import YM.SchemeConversionRG11.FirstMS.DR.Crown

/-!
# Order-one pole of the double line to the same insertion

All primitive kernels here have only PHYSICAL open indices. Hats variable at the integrated
vertex is scalar radial *in the kernel*, but counterterms have open derivative indices, tested
on polynomials degree 2 or 3. Keep the two tickets, second at one auxiliary hat-plane.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

-- Laurent sign conventional: ours variable s=-eps, subtract v/s.
-- reserve stop =4R absorbs full support (coordinates measured from coincidence).

def centry (T:sheet)(z:ℂ)(v:E4):ℂ:= T (z,v,0)
def ladd (p:E4→ℂ)(n:ℕ)(v:E4):= layer n (fun r:ℝ=> p (r • v)) 0
def phys (F:ℂ→E4→ℝ→ℂ)(n:ℕ)(f:E4→ℂ):=
   -(∫ v:E4,vert 0*shape F 0 (v,0) * ladd f n v)/2

variable {F:ℂ→E4→ℝ→ℂ} {R : ℝ} {T : sheet}
variable (hF:Off F) (hT:Touch R T)

lemma peel_hits {U:ℂ × ℝ × Patch → ℂ}(z:ℂ)(p:Patch)(t:ℝ)(n:ℕ) :
   peel^[n] U (z,t,p)=layer n (fun t=> U (z,t,p)) t := by
   induction n generalizing t with | zero=> rfl | succ j ih=> simp_rw [iterate_succ_apply',peel,ih,layer_next]

-- quick
private lemma layer_scalar {f:ℝ→ℂ} (hv:f.HasTemperateGrowth)(n:ℕ)(c:ℂ): layer n (fun t=> c*f t)= fun t=> c*layer n f t:= by
   induction n with
   | zero=> rfl
   | succ i ih=>
     have hp := (layer_tame_ray i hv).1
     rw [layer_next, ih,layer_next]
     ext1 t; rcases eq_or_ne t 0 with rfl|ht
     · unfold strip; rw [dslope_same,dslope_same,deriv_const_mul]; exact hp.differentiable (by simp) _
     rw [strip,dslope_of_ne _ ht,strip, dslope_of_ne _ ht]; simp only [slope_def_module,real_smul]; ring

include hT

lemma Touch.entrance : AH neighborhood (fun p:ℂ×Patch=> T (p.1,swell p.2)) := by
   refine upon_packed opened (isCompact_closedBall (0:Patch) R) (fun z hz x hx=> hT.ends _ hz _ (sq_nonneg _) ?_) ?_ ?_
   · exact show R^2<Q x from (pow_lt_pow_left₀ (lt_of_not_ge (fun he=> hx (mem_closedBall.mpr (by simpa using he)))) hT.inside.le (by decide : (2:ℕ)≠0)).trans_le (q_square _)
   · rintro x hx; exact (hT.smooth (x.1,swell x.2) hx (sq_nonneg _)).comp (f:=fun x:ℂ×Patch=> (x.1,swell x.2)) x (by unfold swell; fun_prop)
   intro z x hz; exact hT.hol _ hz (swell x) (sq_nonneg _)

lemma Touch.makes : AH neighborhood (uncurry (centry T)):=
   (hT.entrance.arguments (w:=fun v:E4=> (v,(0:ℝ))) (by fun_prop)).congr opened (fun z hz x=> by simp [swell,centry])

omit hT in
theorem analytic_ray {F:ℂ× E4 → ℂ} (h : AH neighborhood F)(i:ℕ):
   AH neighborhood (fun p:ℂ × E4=> ladd (fun v=> F (p.1,v)) i p.2) := by
   let t := fun x:E4 × ℝ=> x.2 • x.1
   have hm : HasTemperateGrowth t:= by unfold t; fun_prop
   exact ((h.arguments hm).rad_tail i opened).arguments (w:=fun v:E4=> (v,(0:ℝ))) (by fun_prop)

include hF
lemma entry_deriv (n:ℕ){z:ℂ}(hz:z∈neighborhood): AnalyticAt ℂ (fun z=> phys F n (centry T z)) z:= by
   let G(p:ℂ × E4):= vert 0*shape F 0 (p.2,0)*ladd (centry T p.1) n p.2
   have hG:AH neighborhood G:=
      ((AH.param_tame (g:=fun v:E4=>vert 0*shape F 0 (v,0)) ((HasTemperateGrowth.const _).mul ((shape_bill hF|>.slice occurs).comp (show HasTemperateGrowth (fun v:E4=>(v,(0:ℝ))) by fun_prop)))).mul (analytic_ray (hT.makes) n))
   let K:=closedBall (0:E4) 1; have hc : IsCompact K := isCompact_closedBall ..; let μ := volume.restrict K; haveI : IsFiniteMeasure μ:= ⟨by simp only [μ,Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
   have hw := ((hG.arguments (w:=fun p:ℝ×E4=>p.2) tame_projR).after_average (μ:=μ) (p:=id) (integrable_const 1) aestronglyMeasurable_id (ae_restrict_mem (s:=K) hc.measurableSet) hc).analytic opened hz 0
   have hs : AnalyticAt ℂ (fun s=> ∫ v : E4,G (s,v)) z:= hw.congr (Eventually.of_forall fun w=> by
       simp only [one_mul,id]; exact setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) fun x hx=>by
         have hx':1<‖x‖:=lt_of_not_ge fun he=> hx (mem_closedBall_zero_iff.mpr he)
         exact show _ from (by unfold G; simp only [shape_ends F (hx'.trans_le (norm_fst_le (x,(0:ℝ)))),mul_zero,zero_mul]))
   exact hs.neg.div analyticAt_const (by norm_num)

lemma entry_pole (n:ℕ) :
    let W(p:ℂ × ℝ):= billAt p.1 (fun v=> servo F T (p.1,p.2,v))
    Unfolds (due n W (4*R)) (phys F n (centry T 0)) := by
   intro W; let H:= servo_ok hF hT
   have hb := due_open (F:=W) (H.integral opened) (mul_pos (by norm_num : (0:ℝ)<4) hT.inside) n
   have hh : layer n (fun t=> W (0,t)) 0 = billAt 0 (fun v=> peel^[n] (servo F T) (0,0,v)) := (integral_layer H opened occurs 0 n).symm
   rw [hh,(later H opened n).zero _ occurs] at hb
   unfold phys
   have he (v:E4) : peel^[n] (servo F T) (0,0,v,0)=vert 0*shape F 0 (v,0) *ladd (centry T 0) n v:=by
      have hv : HasTemperateGrowth (fun t:ℝ=>centry T 0 (t • v)) := (hT.makes.slice occurs).comp (by fun_prop : HasTemperateGrowth (fun t:ℝ=>t • v))
      rw [peel_hits]; unfold servo; simp only [swell,Prod.smul_fst, Prod.smul_snd, smul_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact congr_fun (layer_scalar hv n _) _
   simp_rw [he] at hb; exact hb

-- hat entrance coefficient from radial ext per single hat index η²,
-- sets other hats zero; tensor contraction at Λ needs multiplicity 2s.

def slit (T:sheet)(p:ℂ × E4):= layer 2 (fun t:ℝ=> T (p.1,swell (p.2,t))) 0

omit hF in
lemma Touch.spare : AH neighborhood (slit T):=
   (hT.entrance.rad_tail 2 opened).arguments (w:=fun v:E4=> (v,(0:ℝ))) (by fun_prop)

end YM.SchemeConversionRG11.FirstMS.Triad
