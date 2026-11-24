import YM.GapsContact.Tube.Scale
import Mathlib.Analysis.Complex.Liouville

/-!
# Relative convention adapter, actual testing on all Schwartz at any finite arity

A relative test means in independent displacements FROM FIRST. Costs
thus on ALL scaled relative positions. Exact tuboid from testing `fields` in that embedding,
i.e. orders still demand consecutive relative imaginary timelike! Price extends to native
absolute as well so can also apply without any adapt. Lebesgue on these relative variables.
No Jacobian multiplier lost when taking out the physical translation variable. Limit in
entire cone of relative imaginary shifts, independent of translation test. Can use any test
of mass 1 to generate fixed-price lifts of the Schwartz tests (here not claiming an n-uniform
loss, see `taxes`, any n). Scaling to W proven.
-/ -- revise
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Tunnel
open Function Set Filter
open Boundary Surface Analysis Distribution MeasureTheory Trace Trace.Pilot TraceExtension
open Ascent Ascent.Survey EveryPhase Next.BOUNDARY Spec Bornology Probe
open scoped Topology BigOperators InnerProductSpace Classical
universe u
variable {n:ℕ}
def caravan (n:ℕ)(x:E4) : Points n:= points fun _=> x
@[simp] lemma caravan_at (n:ℕ)(x:E4)(i):caravan n x i=x:=rfl
@[fun_prop] lemma caravan_cont (n:ℕ):Continuous (caravan n):=by unfold caravan points; fun_prop

private def shear : (E4 × Points n) ≃L[ℝ] (E4 × Points n) where
     toFun := fun p=>(p.1,p.2-caravan n p.1)
     invFun := fun p=>(p.1,p.2+caravan n p.1)
     left_inv := fun p=> Prod.ext rfl (sub_add_cancel ..)
     right_inv := fun p=> Prod.ext rfl (add_sub_cancel_right ..)
     map_add' := by rintro ⟨x,t⟩ ⟨y,b⟩; refine Prod.ext rfl ?_; ext1 i; change t i + b i-(x+y)= (t i-x)+(b i-y); abel
     map_smul' := by rintro r ⟨x,t⟩; refine Prod.ext rfl ?_; change r • t - r • caravan n x=r • (t-caravan n x); rw [smul_sub]
     continuous_toFun:=by fun_prop
     continuous_invFun:=by fun_prop

def sides (n:ℕ) : Points (n+1) ≃L[ℝ] (E4 × Points n) := Joint.breakAt.trans (shear (n:=n))
lemma side_pp (x:Points (n+1)): sides n x = (x 0,Points.tail x-caravan n (x 0)):=rfl
lemma side_basis (x:E4)(y:Points n): (sides n).symm (x,y)=Points.cons x (y+caravan n x):=rfl
lemma side_measure (n:ℕ): MeasurePreserving (sides n):=by
  have hb : MeasurePreserving (Joint.breakAt (n:=n)):= (WithLp.volume_preserving_ofLp _ _).comp ((Points.peel (n:=n)).measurePreserving)
  have hh : MeasurePreserving (shear (n:=n)):= (MeasurePreserving.id (volume:Measure E4)).skew_product (g:=fun p (x:Points n)=>x-caravan n p)
        (show Measurable fun p:E4 × Points n=>p.2-caravan n p.1 from by fun_prop) (ae_of_all (volume:Measure E4) fun x=>by simp_rw [sub_eq_add_neg]; exact map_add_right_eq_self (volume: Measure (Points n)) _)
  exact hh.comp hb

def foundation (n:ℕ): Points n →L[ℝ] Points (n+1):= (sides n).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E4 _)
lemma found_name (x:Points n): foundation n x=Points.cons 0 x:=by unfold foundation; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]; change (sides n).symm _=_; rw [side_basis,show caravan n 0=0 from rfl,add_zero]
lemma found_basis (t:Points (n+1)) : t = foundation n (sides n t).2 + caravan (n+1) (Points.head t) :=by
  rw [found_name, side_pp]; ext1 i
  induction i using Fin.cases with
  | zero => simp [Points.cons,Points.head]
  | succ i => simp [Points.cons,Points.tail,Points.head]
-- NB (Points.head t) syntax alias

def shelter (n:ℕ) := foundation n ⁻¹' (fields (n+1))
lemma suffixes {y:Points (n+1)}(hy:y∈fields (n+1)) : (sides n y).2 ∈ shelter n:=by
   change foundation _ _∈fields _; rw [side_pp]
   simp only [fields,mem_iInter,mem_setOf_eq] at hy ⊢
   intro i j hij
   rw [show foundation n (Points.tail y-caravan n (y 0))= y-caravan (n+1) (y 0) from ?_]; swap
   · exact eq_sub_of_add_eq (found_basis y).symm
   simpa using (hy i j hij)
lemma shelter_ne (n:ℕ): (𝓝[shelter n] 0).NeBot:=by
   let H:= (sides n); haveI: (𝓝[fields (n+1)] 0).NeBot:= towards_shore (flat _)
   apply Tendsto.neBot (f:=fun x:Points (n+1)=>(H x).2) (x:=(𝓝[fields (n+1)] 0)) ?_
   rw [tendsto_nhdsWithin_iff]; refine ⟨?_, Eventually.mono self_mem_nhdsWithin fun _ hy=>suffixes hy⟩
   simpa [Function.comp_def] using (((continuous_snd.comp H.continuous).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=fields _)))
lemma rise_shelter (n:ℕ): Tendsto (foundation n) (𝓝[shelter n] 0) (𝓝[fields (n+1)] 0):=by
   rw [tendsto_nhdsWithin_iff]; exact ⟨(by simpa using (((foundation n).continuous.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=shelter n)))), self_mem_nhdsWithin⟩

def supportTest (g: Probe E4)(n:ℕ) : Joint n →L[ℂ] Joint (n+1) :=
   (Probe.along (sides n)).comp
     (show Joint n →L[ℂ] Probe (E4 × Points n) from
     { toFun := fun h=> Probe.combine g h
       map_add' := by intro x y; ext1 t; simp [mul_add]
       map_smul' := by intro a x; ext1 t; simp [mul_left_comm]
       cont:= Probe.normCont.comp (continuous_const.prodMk continuous_id) })
lemma arrangement (g:Probe E4)(n:ℕ)(v:Joint n) (x:Points (n+1)) : supportTest g n v x=g (sides n x).1 * v (sides n x).2:=rfl

lemma head_nice : ∃ g:Probe E4,(∫ x,g x)=1 := by
   use Photons.petal E4
   change (∫ x,↑((Photons.bump E4).normed volume x))=(1:ℂ); rw [integral_complex_ofReal,ContDiffBump.integral_normed]; rfl

section price
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {F:Final C f S}{hG:G.Simple}(L:Almanac F)
variable (i:Survey F){D:∀ n, Blanket n}(X:(Survey.reads L i).world.Aurora D)
lemma fixed_price (v: Fin n→S.Union){δ:ℝ}(h:δ∈Ioc (0:ℝ) 1):∃ C:ℝ,∀ z:Full n, Room (shade z) δ → ‖X.emit v z‖≤C:=by
    obtain ⟨Y,hY,hT⟩:= observed L i
    obtain ⟨m,A,-,ha⟩:= Y.power.1 n v
    let y:=δ • rate n; have hx:y∈east n:=by simpa [y] using dawns (light n) h.1
    obtain ⟨hc,hq⟩:= neon_any hT X
    have he (x: Points n): ‖X.emit v (glow x (dawn y))‖≤A*δ⁻¹^m:= by rw [hq.pure n v x y hx]; exact ha y δ h (by simpa [y] using begins (light n) δ h.1.le) x
    refine ⟨A*δ⁻¹^m,fun z hz=>?_⟩; rw [← valley z]; exact upper_tube X v (spectra hT n v) (hq.hol n v) (etched hx) hz.shore he _

def Gig (x: Full n):Prop:=∀ a b:Fin n,∀ j:Axis,x (a,j)=x (b,j)
lemma caravan_full (x y:E4): Gig (glow (caravan n x) (caravan n y)):= fun _ _ _=> rfl
lemma Room.gig {δ:ℝ}{p t:Full n}(hp:Room (shade p) δ)(h:Gig t) (z:ℂ):Room (shade (p+z • t)) δ :=by
   intro i j hij; have he:shade (p+z • t) j - shade (p+z • t) i=shade p j - shade p i:=by
      ext1 b; change (p (j,b)+z*t (j,b)).im - (p (i,b)+z*t (i,b)).im= _; rw [h j i b,Complex.add_im,Complex.add_im,add_sub_add_right_eq_sub]
      rfl
   rw [he]; exact hp i j hij
lemma emit_common (v:Fin n→ S.Union)(z:Full n)(t:Full n)(h:z∈tube n)(ht:Gig t):X.emit v (z+t)=X.emit v z:=by
   let g(c:ℂ):= X.emit v (z + c • t)
   obtain ⟨δ,a,hp,hq⟩:= ((Room.of_fields (show shade z∈fields n from h)).and ((show ∀ᶠ δ in trail,0<δ from self_mem_nhdsWithin).and ((ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds))).exists
   have he (w:ℂ):z+w • t∈tube n:= (a.gig ht w).mem hp
   have hd:Differentiable ℂ g:= fun x=> (((observe L i X).2.hol n v _ (he x)).differentiableAt.comp x (f:=fun y:ℂ=>z+y • t) (show DifferentiableAt ℂ (fun y:ℂ=>z+y • t) _ by fun_prop))
   obtain ⟨A,hB⟩:= fixed_price L i X v (show δ∈Ioc 0 1 from ⟨hp,hq⟩)
   have hG:IsBounded (Set.range g):= isBounded_iff_forall_norm_le.mpr ⟨A,Set.forall_mem_range.mpr fun x=> hB _ (a.gig ht x)⟩
   simpa only [g,one_smul,zero_smul,add_zero] using hd.apply_eq_apply_of_bounded hG (1:ℂ) 0
lemma weather_common (v:Fin n→ S.Union)(z:Full n)(t:Full n)(h:z∈tube n)(ht:Gig t){r:ℝ}(hr:0<r):weather X v r (z+t)=weather X v r z:= by
   unfold weather; rw [smul_add]; apply emit_common
   · change shade _ ∈ fields n; rw [← valley z, ← glow_scales, im_glow]; exact swell h hr
   intro a b j; simp [ht a b j]
lemma aura_sides (v:Fin (n+1)→S.Union)(x y:Points (n+1))(hy:y∈ fields _){r:ℝ}(hr:0<r): weather X v r (glow x y)= weather X v r (glow (foundation n (sides n x).2) (foundation n (sides n y).2)):=by
   rw [show (glow x y)=_+ (glow (caravan (n+1) (Points.head x)) (caravan (n+1) (Points.head y))) from ?_,weather_common L i X v _ _ ?_ (caravan_full _ _) hr]; rotate_left
   · have hn (a b c d:Points (n+1)): glow a c+glow b d=glow (a+b) (c+d):=by ext1 k; simp [glow]; ring
     exact ((hn (foundation n _) _ (foundation n _) _).trans (congr_arg₂ glow (found_basis x).symm (found_basis y).symm)).symm
   change shade _∈ fields _; rw [im_glow]; exact suffixes hy

def aurora_sides (v:Fin (n+1)→S.Union)(r:ℝ)(y x:Points n):=weather X v r (glow (foundation n x) (foundation n y))
lemma supporter (v:Fin (n+1)→ S.Union)(y:Points n)(hy:y∈shelter n){r:ℝ}(hr:0<r)(x:Points (n+1)): weather X v r (glow x (foundation n y))=aurora_sides L i X v r y (sides n x).2:=by
    -- `foundation` constructor fixed
    unfold aurora_sides; rw [aura_sides L i X v x _ hy hr]; congr 2; rw [foundation]; simp
lemma supports_int (g:Joint n)(v:Fin (n+1)→S.Union)(y:Points n)(hy:y∈shelter n){r:ℝ}(hr:0<r): Integrable (fun x=>aurora_sides L i X v r y x*g x):=by
    -- `emit` height fixed z, all x, combine.
    let u:= r • foundation n y
    obtain ⟨δ,a,hp,hq⟩:= ((Room.of_fields (swell (show foundation n y∈fields _ from hy) hr)).and ((show ∀ᶠ δ in trail,0<δ from self_mem_nhdsWithin).and ((ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds))).exists
    obtain ⟨A,hB⟩:= fixed_price L i X v (show δ∈Ioc 0 1 from ⟨hp,hq⟩)
    unfold aurora_sides weather; simp_rw [← glow_scales]; let U:= fun x=>glow (r • foundation n x) u
    have hf: ∀ x,U x∈ tube (n+1):= fun x=>show shade _∈ fields _ from (by rw [im_glow]; exact a.mem hp)
    have hh:Continuous fun x=> X.emit v (U x):=((observe L i X).2.hol _ _).continuousOn.comp_continuous (show Continuous U from by unfold U glow; fun_prop) hf
    refine (g.integrable.norm.const_mul A).mono' (hh.mul g.continuous).aestronglyMeasurable (ae_of_all _ fun x=>?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB (U x) (by unfold U; rw [im_glow]; exact a)) (norm_nonneg _)

lemma owned (g:Joint n)(b: Probe E4)(v:Fin (n+1)→ S.Union)(y:Points n)(hy:y∈shelter n){r:ℝ}(hr:0<r) : (∫ x, weather X v r (glow x (foundation n y))* supportTest b n g x) = (∫ z,b z) * ∫ x,aurora_sides L i X v r y x*g x:=by
    let U (w:E4 × Points n):= b w.1*(aurora_sides L i X v r y w.2*g w.2)
    simp_rw [supporter L i X v y hy hr,arrangement];
    rw [show (∫ x, aurora_sides L i X v r y (sides n x).2 * (b (sides n x).1*g (sides n x).2)) =∫ x,U (sides n x) from integral_congr_ae (ae_of_all _ fun x=> mul_left_comm ..)]
    rw [(side_measure n).integral_comp (sides n).toHomeomorph.toMeasurableEquiv.measurableEmbedding U]; exact integral_prod_mul b (fun x=> aurora_sides L i X v r y x*g x)

lemma owned_limit {r:ℝ}(hr:0<r) (g:Joint n)(b:Probe E4)(hb:(∫ z,b z)=1)(v:Fin (n+1)→S.Union): Tendsto (fun y=> ∫ x,aurora_sides L i X v r y x*g x) (𝓝[shelter n] 0) (𝓝 ((Survey.reads L i).world.W (n+1) v (condense r⁻¹ (supportTest b n g)))):=by
    obtain ⟨H,Y⟩:= observe L i X
    apply ((cascade _ v X H Y (supportTest b n g) hr).comp (rise_shelter n)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx; simpa only [hb,one_mul,Function.comp_apply,weather] using owned L i X g b v x hx hr

def readingsTest (b:Probe E4)(r:ℝ)(v:Fin (n+1)→S.Union): Distn (Points n):= ((Survey.reads L i).world.W (n+1) v).comp ((shower r).comp (supportTest b n))
lemma reading_eq {r:ℝ}(hr:0<r) (g: Joint n)(b:Probe E4)(v:Fin (n+1)→S.Union):readingsTest L i b r v g = (Survey.reads L i).world.W (n+1) v (condense r⁻¹ (supportTest b n g)):=by rw [← shower_at hr]; rfl
include X in
lemma same_translation_test {r:ℝ}(hr:0<r) (v:Fin (n+1)→S.Union) (a b:Probe E4)(ha:(∫ z,a z)=1) (hb:(∫ z,b z)=1): readingsTest L i a r v=readingsTest L i b r v:=by
    ext1 x; rw [reading_eq L i hr, reading_eq L i hr]; haveI:=shelter_ne n; exact tendsto_nhds_unique (owned_limit L i X hr x a ha v) (owned_limit L i X hr x b hb v)
lemma enough_cell (n k:ℕ)(b: Probe E4) : ∃ (s:Finset (ℕ × ℕ))(C:ℝ),0≤C ∧ ∀ x:Joint n,taxes (n+1) k (supportTest b n x) ≤ C* s.sup (schwartzSeminormFamily ℂ _ _) x:=by
    obtain ⟨s,c,-,h⟩:= Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Points n) ℂ) ((taxes (n+1) k).comp (supportTest b n).toLinearMap) ((taxes_cont ..).comp (supportTest b n).continuous)
    exact ⟨s,c,c.coe_nonneg,h⟩
end price
end YM.GapsContact.Tunnel
