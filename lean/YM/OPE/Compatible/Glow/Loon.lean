import YM.OPE.Compatible.Glow.Pitch
/-!
# Normal factors price and curvature
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{b:ℝ}
namespace Script
open Page
-- tale functional on matrices. Use real linear-affine name.
structure Beam (G:Gauge) where
   leg : Walk
   f : G.Mat →L[ℝ] ℝ
abbrev Beam.account (p:Beam G) (U:CoverConfig G):= p.f (G.mat (travel U 0 p.leg)-1)
abbrev Beam.shot (p:Beam G)(t:ℝ)(x:fieldX (Shade G)):= p.account (lotU (t • x))
-- order0 use norm, else linear
lemma beam_bounds (G:Gauge)(U s:ℝ)(hs:0<s)(hp:0≤U)(j:ℕ):∃ C:ℝ,0 ≤ C∧ ∀ (p:Beam G)(x:fieldX (Shade G)) (d:ℝ),0≤ d→(∀ x:G.Mat, ‖p.f x‖ ≤ d*‖x‖)→ (∀ i∈dirt 0 p.leg, ‖indexS i x‖≤ U)→∀ t:ℝ,‖iteratedDeriv j (fun v=> p.shot v x) t‖ ≤ C*d*Real.exp (s*p.leg.length):=by
    obtain ⟨g,hg,H⟩:=linear_bill G j s U hs hp; let v:G.Mat:=1; refine ⟨g+‖v‖,add_nonneg hg (norm_nonneg _),fun p x D hD hv h t=>?_⟩; let f(t:ℝ):= G.mat (travel (lotU (t • x)) 0 p.leg); let S:=Real.exp (s*p.leg.length); have hx:1 ≤ S:=by apply Real.one_le_exp; positivity
    have ht(t): ‖iteratedDeriv j f t‖ ≤ g*S:=H _ _ _ h t; have he:ContDiff ℝ ⊤ f:=fluted ..; let Y:ℝ→G.Mat:=fun _=>1
    change ‖iteratedDeriv j (p.f ∘ (f-Y)) t‖≤_
    have hr:iteratedDeriv j (p.f ∘ (f-Y)) t= p.f (iteratedDeriv j (f-Y) t):=by unfold iteratedDeriv; erw [p.f.iteratedFDeriv_comp_left ((show ContDiff ℝ ⊤ (f-Y) from he.sub contDiff_const).contDiffAt) le_top];rfl
    rw [hr]; apply (hv _).trans; rw [iteratedDeriv_sub _ _]; swap; · exact he.contDiffAt.of_le le_top
    swap; · exact contDiffAt_const
    have hv9: ‖iteratedDeriv j Y t‖ ≤ ‖v‖:=by
        by_cases hh:j=0; · subst j; rw [iteratedDeriv_zero]
        have he : iteratedDeriv j Y t=0:=by unfold Y iteratedDeriv; rw [iteratedFDeriv_const_of_ne hh];rfl
        rw [he,norm_zero]; positivity
    have hz:= (norm_sub_le (iteratedDeriv j f t) (iteratedDeriv j Y t)).trans (add_le_add (ht t) (hv9.trans (le_mul_of_one_le_right (norm_nonneg _) hx)))
    exact (mul_le_mul_of_nonneg_left hz hD).trans_eq (by unfold S; ring)
-- curve functional
noncomputable def pleatsF (i:G.ColorIndex) : G.Mat→ₗ[ℝ] ℝ where
    toFun x := (chin i) (G.projectColor ((1/2:ℝ) • (x - star x)))
    map_add' x y:=by rw [star_add,add_sub_add_comm,smul_add,map_add,map_add]
    map_smul' t v:=by simp [star_smul, ← smul_sub];ring
lemma pleatsEq (g:G.El)(j:G.ColorIndex):pleatsF j (G.mat g-1)=chin j (G.curvature g):=by
    unfold pleatsF; change chin j (G.projectColor ((1/2:ℝ) • _)) = _; rw [star_sub,star_one,sub_sub_sub_cancel_right]; simp [Gauge.curvature]
-- price trace
noncomputable def traceF (G:Gauge):G.Mat→ₗ[ℝ]ℝ where
   toFun x:= -(x.trace.re/G.repDim)
   map_add' a b:=by simp [add_div]; ring
   map_smul' c v:=by simp;ring
lemma traceEq (G:Gauge)(v:G.El):traceF G (G.mat v - 1)=G.price v:=by
    unfold traceF Gauge.price; simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sub,Matrix.trace_one, Fintype.card_fin,Complex.sub_re, Complex.natCast_re]; have he:(G.repDim:ℝ)≠0:=by positivity
    field_simp; ring
-- square & loop slot Signed
abbrev plaqBeam (G:Gauge)(p:PlaqAxes)(s:Signed):Beam G:=⟨(square p.val.1 p.val.2).map (·.rotate s),(traceF G).toContinuousLinearMap⟩
abbrev slotBeam (k:RG.Slot)(s:Signed)(j:G.ColorIndex): Beam G:=⟨(k.walk ++ square k.plaq.val.1 k.plaq.val.2 ++ Lattice.reverse k.walk).map (·.rotate s),(pleatsF j).toContinuousLinearMap⟩
lemma plaqBeamEq (p:PlaqAxes)(s:Signed)(v:CoverConfig G): Beam.account (plaqBeam G p s) v=G.price (faceValue (pull s 0 v) (0,p)):=by rw [Beam.account]; erw [traceEq]; simp only [faceValue, travel_pull, affine, add_zero, Signed.act_zero]
lemma slotBeamEq (p: RG.Slot)(s:Signed)(j:G.ColorIndex)(v:CoverConfig G): Beam.account (slotBeam p s j) v= (p.eval (pull s 0 v)) j:=by
    let U:=pull s 0 v; let z:=square p.plaq.val.1 p.plaq.val.2; let A:=p.walk++ z ++ Lattice.reverse p.walk; unfold Beam.account; erw [pleatsEq]; change chin j (G.curvature (travel _ _ (A.map _)))=_; rw [← (show travel U 0 A= travel v (0:Cover) (A.map (·.rotate s)) from (travel_pull A v s 0 0) |>.trans (by simp [affine]))]; unfold A; rw [travel_append,travel_append,stop_append, square_stop _ _ _ (R:=ℤ), travel_reverse,G.curvature_conjugate]; rfl
end Script
end YM.OPE.Flume
