import YM.RG02.Flat.Projection

/-!
# Agreement with the absolute log-link Taylor rules, even before tag sum

`formal` uses the relative chart of the real construction. For the
first identification we used the same relative convention in the formal
calculation. Absolute log-link coordinates on that tree gauge (the
A/B convention) give the same coefficients. This is NOT just translation
of polynomials by bare replicas -- the change of variables inside the
higher-order calculation must include the derivative of *all* chart-dependent
weights and use the Haar density in the appropriate log chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk.Draw
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories Exterior
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η : ChartRatio G} {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)
    (hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)
variable {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ)(ht : Ink m W)(hh : Ambient A)(hs : S.patch.Branches S.kernel G)(hη : LocalRatio η)(x : Dir G c)
variable {Q : Bed}(hc : Attached Q R){e D : ℝ} (hD : Floor Q p f e D)(hK : Sworn Q f G)

/-- The correction in MEAN coordinates. -/
def statue (x : Dir G c) : AxisChart G T:= fun i => linearCopy S.ratio (collect G x) i

-- Hessian arguments only! no claim on replacing full lifted fields.
lemma ascent (y : Dir G c)(a : ℝ) (v : AxisChart G T) :
    Bid.stretch (S:=S) T (a • y,v)= Bid.stretch (S:=S) T (a • x,v+a • statue T y-a • statue T x) := by
   have he (z : Dir G c) i : linearCopy S.ratio (collect G (a • z)) i=a • linearCopy S.ratio (collect G z) i := by
      unfold linearCopy; split; exact (smul_zero a).symm
      rfl
   funext b; unfold Bid.stretch
   dsimp only; split
   next hi => unfold linearCopy; rw [if_pos (T.trunk_internal hi),if_pos (T.trunk_internal hi)]
   next hi => simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,statue,he]; abel

private def aisle (x y : Dir G c) (v : ℝ×AxisChart G T): Dir G c×Dir G f:=
   ((Tangent.shift T x v).1,(Work.F03.inclusion T (Tangent.shift T y v)).2)

lemma from_open (y : Dir G c) : arcRay T i p R x y =ᶠ[𝓝 0] (Work.F03.flat S i p R) ∘ aisle T x y := by
   have H : Tendsto (Tangent.shift T y) (𝓝 0) (𝓝 0) := by simpa only [map_zero] using (Tangent.shift T y).continuous.tendsto 0
   filter_upwards [H.eventually (Work.F03.inclusion_works T)] with z hz
   change represent (Work.F03.axisLog T _) = _ at hz
   change mainTerm p R (Work.F03.live T (Tangent.shift T y z)) + noiseTaylor S (represent (z.1 • x)) (Work.F03.live T _) i =
     mainTerm p R (represent (Work.F03.axisLog T _)) + noiseTaylor S _ (represent (Work.F03.axisLog T _)) _
   rw [hz]; rfl

include hs hW hc hD hK
private lemma from_led (y : Dir G c) :
   Radial.Stationary (arcRay T i p R x y) ∧ ∀ a v,
    Radial.jet (arcRay T i p R x y) 2 (a,v)=Radial.jet (Work.F03.flat S i p R) 2 (a • x, Bid.stretch (S:=S) T (a • y,v)) := by
   let F:=Work.F03.flat S i p R
   let Y:=aisle T x y
   have Hu : ContDiffAt ℝ ω F 0 := Work.F03.flat_smooth hs i (Work.F02.answer G p R σ v Λ hW)
   obtain ⟨hx,hy,_⟩:= Work.F03.flat_jets hs i hW hc hD hK (Work.F02.answer G p R _ _ _ hW)
   have hg := from_open (R:=R) (p:=p) T i x y
   have hb : Y 0=0 := by unfold Y aisle; rw [map_zero,map_zero, Work.F03.inclusion_zero]; rfl
   let Z:= Tangent.shift T y
   have hZ : ContDiffAt ℝ ω (Work.F03.inclusion T) (Z 0) := Z.map_zero.symm ▸ Work.F03.inclusion_smooth T
   have hv : ContDiffAt ℝ ω Y 0 := ((Tangent.shift T x).contDiff.contDiffAt).fst.prodMk (hZ.comp 0 Z.contDiff.contDiffAt).snd
   have he : fderiv ℝ (F ∘ Y) 0=0 := by rw [fderiv_comp _ (show DifferentiableAt ℝ F (Y 0) by rw [hb]; exact Hu.differentiableAt (by simp)) (hv.differentiableAt (by simp)),hb]; change fderiv ℝ (Work.F03.flat S i p R) 0 ∘L _=_; rw [hy]; rfl
   have Hj (b) : fderiv ℝ Y 0 b=(b.1 • x, Bid.stretch (S:=S) T (b.1 • y,b.2)) := by
      let L:=Tangent.shift T x
      let t:= ContinuousLinearMap.snd ℝ (Dir G c) (Dir G f)
      have hr : HasFDerivAt (fun z : ℝ × AxisChart G T=> (Tangent.shift T x z).1) (ContinuousLinearMap.fst ℝ _ _ ∘L Tangent.shift T x) 0 := L.hasFDerivAt.fst
      have H := (t.hasFDerivAt.comp 0 ((hZ.differentiableAt (by simp)).hasFDerivAt.comp _ Z.hasFDerivAt))
      rw [show fderiv ℝ Y 0=_ from (hr.prodMk H).fderiv]
      apply Prod.ext; rfl
      change (fderiv ℝ (Work.F03.inclusion T) (Z 0) (Z b)).2=_
      rw [map_zero,Work.F03.inclusion_deriv]; rfl
   refine ⟨⟨((hb.symm ▸ Hu : ContDiffAt ℝ ω F (Y 0)).comp 0 hv|>.congr_of_eventuallyEq hg).of_le le_top,hg.eq_of_nhds.trans (by change F (Y 0)=0; rw [hb]; exact hx), fun u=>?_⟩, fun a v=>?_⟩
   · unfold Radial.jet; rw [iteratedFDeriv_one_apply, hg.fderiv_eq, he]; simp
   unfold Radial.jet; rw [(hg.iteratedFDeriv ℝ _).self_of_nhds]
   congr 1
   rw [show (fun _ : Fin 2=> _) = ![(a,v),(a,v)] from ?_]
   change iteratedFDeriv ℝ 2 (F ∘ Y) 0 _= _
   rw [(Work.F03.hessian_comp hb (Hu.of_le le_top) (hv.of_le le_top) hy).2,Hj]
   · apply congr_arg; funext i; fin_cases i <;> rfl
   funext i; fin_cases i <;> rfl

include h hp hr

lemma moved (y : Dir G c) : Steer (Γ i hp hr h) (arcRay T i p R x y)
      (due T i p R x (crest T ρ x)) (crest T ρ x + statue T x - statue T y) := by
   have ht := from_led T i hW hs x hc hD hK
   refine ⟨(ht y).1,fun a v=>?_⟩
   let w := v+a • statue T y-a • statue T x
   calc
     _ = Radial.jet (arcRay T i p R x x) 2 (a,w) := by rw [(ht y).2,(ht x).2,ascent (x:=x) T]
     _ = _ := by
       let H := Orientation.recovers Q T hs hW hc hD hK
       change Radial.jet (ray T i p R x) 2 (a,w)=_
       rw [(launch i hp hr h H x).2]
       rw [show w-a • crest T ρ x=v-a • (crest T ρ x+statue T x-statue T y) by unfold w; rw [smul_sub,smul_add]; abel]

include ht hh hη
/-- Thus radial perturbation extraction does not rely on which group
translation shift is made even to define the link variables in the PT rule. -/
theorem flexed (y : Dir G c) : formal T i hp hr h η x A m W =
     flexion T i (Γ i hp hr h) η p R x y A m W (crest T ρ x+statue T x-statue T y) := by
   have hv := moved T i hp hr h hW hs x hc hD hK y
   have hg := Orientation.recovers Q T hs hW hc hD hK
   obtain ⟨r,hu,hs',HH⟩:= uncut_target T i hW ht hh hs hη x y (flightFrom T i x y hv hW hη hh)
   obtain ⟨V,hV,Hv,H⟩ := Volume.coverage T η (motion_tends T y) hη hu hs'.le
   obtain ⟨U,hU,Ht,Hu⟩ := target T i hp hr h hW ht hh hs hη x hg
   let L:= U ∩ V
   have hx := Hu L (inter_mem hU hV) (Ht.inter Hv) inter_subset_left
   have hy := HH r hu le_rfl (fun _=>L) (H L (inter_mem hU hV) (Ht.inter Hv) inter_subset_right)
   let c:=multiplier T i hp hr h η x
   have he := multiplier_pos T i hp hr h η x hη
   exact smul_right_injective _ (Complex.ofReal_ne_zero.mpr he.ne') (hx.2.uniquely hy.2)

omit hW ht hh hs hη x hc hD hK in
/-- Unshifted absolute A/B rules. Normalize exactly as `Fk.formal`. -/
def absolute (η)(x)(A : Space G f→ℝ)(m : ℕ)(W : Space G f→Poly B) :=
   flexion T i (Γ i hp hr h) η p R x 0 A m W (crest T ρ x+statue T x)
lemma absolute_same : formal T i hp hr h η x A m W = absolute T i hp hr h η x A m W := by
  unfold absolute
  have he : statue T (0:Dir G c)=0 := by funext i; unfold statue linearCopy; split <;> rfl
  simpa only [he,sub_zero] using flexed T i hp hr h hW ht hh hs hη x hc hD hK (0:Dir G c)

omit i hp hr h hW ht hh hs hη x hc hD hK in
lemma absolute_link (u : AxisChart G T) (t : ℝ) : (Pins.visits T 0 (t,t • u)).2 =
    T.drape fun i : T.Free => G.lieExp (t • u i) := by
   change lifting _ (represent (t • (0:Dir G c))) (t • u) = _
   rw [smul_zero,link_one]; unfold lifting
   simp only [replica_one,Pi.one_apply,mul_one,Pi.smul_apply]
end YM.RG02.Fk.Draw
