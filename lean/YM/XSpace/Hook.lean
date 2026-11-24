import YM.XSpace.Hoists

/-!
# Local invariant stencil uses one holonomy panel even off-shell

No assumptions about reflection cutoff of the ren rows. Reality.
-/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Hoops
open Filter Set Function Lattice CubicMatch Chart2 Mu Outline Wilson Labels Source Source.Drops RG Bid Work.G05
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {d:ℕ}{H:Hol G}
lemma fits_diff {f:ℝ→ G.El}{v:Drift G}(h:Chart2.Fits f v): ContDiffAt ℝ ω (fun t=> G.curvature (f t)) 0:=by
  let S: G.Mat →L[ℝ] G.Mat:= (starL ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap
  let L:= G.projectColor.toContinuousLinearMap.comp ((1/2:ℝ) • (ContinuousLinearMap.id ℝ G.Mat-S)); apply L.contDiff.contDiffAt.comp 0 h.smooth
variable (S:Survey G H d) (A:LogLinks ℤ G)
def circles (t:ℝ): Links ℤ G.El:= fun e=> G.lieExp (t • A e)
def patch (u:Slot) (t:ℝ):= roundTrip u 0 (circles A t)
lemma patch_fits (u:Slot): Chart2.Fits (patch A u) (roundTrip u 0 (native A)):= carries_round _ _ _ (fun e=>Chart2.Fits.along_a _) _
def see (t:ℝ): GaugePanel G S.size:= fun i=> G.curvature (patch A (S.looks i) t)
lemma see_view (t:ℝ): see S A t=Bid.mapped S.looks (circles A t):=by funext i; unfold see patch roundTrip; rw [G.curvature_conjugate]; rfl
lemma see_diff : ContDiffAt ℝ ω (see S A) 0:= contDiffAt_pi.mpr fun i=> fits_diff (patch_fits ..)
lemma see_zero : see S A 0=0:=by funext i; unfold see; rw [(patch_fits ..).val]; simp [Gauge.curvature]
lemma see_first : HasDerivAt (see S A) (spectra S 0 A) 0:=by
  apply hasDerivAt_pi.mpr; intro i; have he:= patch_fits A (S.looks i); have hh := (he.smooth.differentiableAt (by simp)).hasDerivAt; rw [he.slope, native,round_a] at hh; exact Work.F03.curvature_of_hasDerivAt hh
lemma see_second : term 2 (see S A)= accent S 0 A:=by
  funext i; change (ContinuousLinearMap.proj i : GaugePanel G S.size →L[ℝ] G.Color) (term 2 (see S A))=_; rw [← term_linear _ ((see_diff S A).of_le le_top)]; exact (patch_fits A (S.looks i)).curvature
lemma sea_first : HasDerivAt (fun t=> S.recover (see S A t)) (primary S 0 A) 0:=by
  have h:= (S.recover_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 (see_first S A); rw [see_zero] at h; exact h
lemma sea_second : term 2 (S.recover ∘ see S A)= secondary S 0 A:= by rw [term_vcomp_two S.recover_smooth.contDiffAt (see_diff ..),see_zero,(see_first ..).deriv,see_second]; rfl
variable (s:Signed)
lemma sea_sym (t:ℝ): S.recover (see S (incline s A) t)= snapTurn s.ortho⁻¹ (S.recover (see S A t)):=by
  rw [see_view,see_view,show circles (incline s A) t=_ from hoist s A t,S.takes,S.recover_roll]; rfl
lemma productions : primary S 0 (incline s A)= snapTurn s.ortho⁻¹ (primary S 0 A) ∧ secondary S 0 (incline s A)=snapTurn s.ortho⁻¹ (secondary S 0 A):=by
  let L:=snapTurn (G:=G) (d:=d) s.ortho⁻¹; have he : S.recover ∘ see S (incline s A) = fun t=> L ((S.recover ∘ see S A) t):= funext fun t=> sea_sym S A s t
  constructor
  · exact (sea_first S _).unique (((L.hasFDerivAt.comp_hasDerivAt 0 (sea_first S A))).congr_of_eventuallyEq (Eventually.of_forall fun t=> congr_fun he t))
  rw [← sea_second, he,term_linear _ ((S.recover_smooth.contDiffAt.comp 0 (see_diff ..)).of_le le_top),sea_second]
lemma look_product (p:Labels.Pol G)(x:Snap G d): awaken d (rotated s.ortho p) x=awaken d p (snapTurn s.ortho⁻¹ x):=by rw [awaken,rotated,eval_changed, awaken,snap_expand]
lemma hymn (p:Labels.Pol G): weave s (p0 S 0 p)=p0 S 0 (Labels.rotated s.ortho p) ∧ weave s (p1 S 0 p)=p1 S 0 (Labels.rotated s.ortho p):=by
  let L:=snapTurn (G:=G) (d:=d) s.ortho⁻¹; constructor <;> (apply same; intro A; rw [weave_pit])
  · rw [awake0,awake0,look_product, (productions S A s).1]
  rw [awake1, awake1, show awaken d (rotated s.ortho p)= awaken d p ∘ L from funext (look_product s p)]; let y:= primary S 0 A
  have hp : DifferentiableAt ℝ (awaken d p) (L y):= (snap_read_smooth d p ω).differentiable (by simp) _; rw [(productions S A s).1,(productions S A s).2, fderiv_comp y hp L.differentiableAt,L.fderiv]; rfl
lemma text_angle (p:Stamp G)(x:Cover):weave s (Trace.volume x p)=Trace.volume (s.act x) (weave s p):=by
  refine same fun A=>?_ ; rw [weave_pit,Trace.ting,Trace.ting,weave_pit]; apply congr_arg (pit · p); funext i; simp only [Trace.zone_ap]; unfold incline swing Step.used Step.rotate posDir; split_ifs <;> simp [Trace.zone_ap]; rw [add_sub_assoc]
lemma hymn_text (p:Labels.Pol G)(x:Cover): weave s (p0 S x p)=p0 S (s.act x) (Labels.rotated s.ortho p) ∧ weave s (p1 S x p)=p1 S (s.act x) (Labels.rotated s.ortho p):=by
  have he(p:Labels.Pol G)(x:Cover): Trace.volume x (p0 S 0 p)=p0 S x p:= by rw [Trace.stained,Chart.pull0]; simp [Chart.lug]
  have hh(p:Labels.Pol G)(x:Cover): Trace.volume x (p1 S 0 p)=p1 S x p:= by rw [Trace.stained,Chart.pull1]; simp [Chart.lug]
  rw [← he p x,← hh p x,text_angle,text_angle,(hymn S s p).1,(hymn S s p).2,he,hh]; trivial
-- reality
abbrev shore (G:Gauge): Stamp G →+* Stamp G:= XSpace.Taylor.conjPol _
lemma coastal (F:Stamp G): pit A (shore G F)= star (pit A F):=by
  unfold shore; induction F using MvPolynomial.induction_on with | C=>simp [XSpace.Taylor.conjPol,pit] | add p q hp hq=> simp only [map_add,hp,hq,star_add] | mul_X p i hp=> simp only [map_mul,star_mul']; rw [hp]; simp [XSpace.Taylor.conjPol,pit,numbers]
lemma salt_root (i j:Bone G ℤ): (Mu.root G).cov i j= ↑(((Mu.root G).cov i j).re):=by change coal _ _ _=↑((coal Sail.cover i j).re); unfold coal; split_ifs <;> simp
lemma vex (p:Stamp G): JetGauge.E (Mu.root G) (shore G p)= star (JetGauge.E (Mu.root G) p):= XSpace.Taylor.blend_real _ _ (fun i=> funext fun j=> salt_root i j) _
lemma vex_V (u:Face ℤ): shore G (V3 G u)= V3 G u:=same fun i=>by rw [coastal,price_at]; simp
lemma salutations (p:Labels.Pol G)(x:Cover): shore G (p0 S x p)=p0 S x (Labels.conjPol p) ∧ shore G (p1 S x p)=p1 S x (Labels.conjPol p):=by
  let M:= (Complex.conjCLE:ℂ→L[ℝ]ℂ); have hh : awaken d (Labels.conjPol p)= M ∘ awaken d p:= funext fun _=> Labels.conj_value ..; constructor <;> (apply same; intro A; rw [coastal]
  )
  rw [awake0,awake0,hh]; rfl
  rw [awake1,awake1,hh,fderiv_comp (primary S x A) M.differentiableAt (show DifferentiableAt ℝ (awaken d p) _ from (snap_read_smooth d p ω).differentiable (by simp) _),M.fderiv]; rfl
end YM.XSpace.Hoops
