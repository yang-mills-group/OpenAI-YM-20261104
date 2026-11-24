import YM.RG02.Degree.Paged
import YM.RG02.Flat.Syntax

/-!
One-step canonical conditional transmission. Degree counts on projected
field kernels (in this finite torus algorithm -> no unique lifted-path
presentation). The log factors contract all vacuum lines; the quadratic
which has no explicit coupling power is recovered separately from the price
of the affine mean. Keep exact coordinates held as in the full dictionary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk.Draw
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Bid Marker Extra.Trajectories Multi Marks
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η : ChartRatio G} {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)(hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)

abbrev SpaceVar (T : Forest S.ratio)(G : Gauge) := Dir G c × AxisChart G T

def fixture (z : ℝ × SpaceVar T G) := (z.1, Work.F03.live T z.2)
def graphPrice (i : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(A : Space G f→ℝ)(z : ℝ × SpaceVar T G) :=
   tested T i p R z.2.1 z.2.2 + A (fixture T z) + z.1^2*(Precision.loop R (fixture T z).2-Real.log (axisJ T η z.2.2))

lemma stretch_graph (x : Dir G c)(u : ℝ× AxisChart G T) : track T i η p R x A u=graphPrice T i η p R A (u.1,u.1 • x,u.2) := by
   rw [enact]; rfl
omit [Fintype I] in
lemma set_graph (x : Dir G c)(u : ℝ× AxisChart G T) : Pins.ink T x W u=W (fixture T (u.1,u.1 • x,u.2)) := rfl

lemma scenery {Y: Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](F : Space G f→Y)(H : ContDiffAt ℝ ∞ (F ∘ fills) 0) : ContDiffAt ℝ ∞ (F ∘ fixture T) 0 := by
   let f' := fun x : ℝ× SpaceVar T G=> (x.1, (Work.F03.inclusion T x.2).2)
   have he : f' 0=0 := by simp [f',Work.F03.inclusion_zero]
   have hu : ContDiffAt ℝ ∞ f' 0:= contDiffAt_fst.prodMk (((Work.F03.inclusion_smooth T (G:=G)).of_le le_top).comp (f:=Prod.snd) (0:ℝ×SpaceVar T G) contDiffAt_snd).snd
   have hx : Tendsto (Prod.snd : ℝ × SpaceVar T G → _) (𝓝 0) (𝓝 0) := continuous_snd.tendsto _
   apply ((he.symm ▸ H : ContDiffAt ℝ ∞ _ (f' 0)).comp _ hu).congr_of_eventuallyEq
   filter_upwards [hx.eventually (Work.F03.inclusion_works T)] with z hz; exact congr_arg F (Prod.ext rfl hz.symm)

lemma scene_born {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ) (ht : Ambient A)(hη : LocalRatio η)(h : Critical T p R ρ) : ContDiffAt ℝ ∞ (graphPrice T i η p R A) 0 := by
   unfold graphPrice
   refine (((h.2.2 i).1.of_le le_top |>.comp (f:=Prod.snd) 0 contDiffAt_snd).add (scenery T A ht.smooth)).add ((contDiffAt_fst.pow ..).mul ?_)
   have hs : ContDiffAt ℝ ω (fun z=> Precision.loop R (Work.F03.live T z)) 0 := Progress.StationaryScenes.loop_smooth hW (Work.F03.live_smooth T)
   have hb : ContDiffAt ℝ ω (axisJ T η) 0 := contDiffAt_prod fun i _=>
      (hη.germ 0 (Metric.mem_ball_self hη.patch)).comp (f:=fun v : AxisChart G T=>v i) _ (contDiffAt_apply ..)
   have hr : axisJ T η 0 ≠ 0 := by simp [axisJ,hη.anchored]
   refine (((hs.comp (f:=Prod.snd) 0 contDiffAt_snd).sub ((hb.log hr).comp (f:=fun x : ℝ×SpaceVar T G=>x.2.2) 0 (contDiffAt_snd.comp 0 contDiffAt_snd))).of_le le_top)

def toGraph (ρ : Dir G c→AxisChart G T) : SpaceVar T G →ₗ[ℝ] ℝ × SpaceVar T G := {
    toFun x := (0,x.1,x.2+ crest T ρ x.1)
    map_add' x y := by simp [crest]; abel
    map_smul' a x := by ext <;> simp [crest, smul_add] }

lemma tilted (x : SpaceVar T G)(ρ : Dir G c→AxisChart G T) : toGraph T ρ x+(1,0)= (1,x.1,x.2+crest T ρ x.1) := by simp [toGraph]

variable {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ)(ht : Ink m W)(hh : Ambient A)(hη : LocalRatio η)

include hW hh hη h
lemma vacuum_stage (r : ℕ) : Shear.Rolls (r+2) fun k : SpaceVar T G =>
    coeff r (Asym.driven (track T i η p R k.1 A) (bend (crest T ρ k.1) k.2)) := by
   by_cases hv:r=0
   · simpa only [hv,Asym.driver_vac] using Shear.Rolls.const (X:=Dir G c) (E:=AxisChart G T) (k:=2) 0
   let F:= graphPrice T i η p R A
   have hf : ContDiffAt ℝ ∞ F 0 := scene_born T i hW hh hη h
   convert! ((Shear.Rolls.jets F (r+2) (toGraph T ρ) ((1:ℝ),0)).scale (-1)) using 1
   funext k; simp only [Pi.smul_apply,smul_eq_mul, neg_one_mul, driven, coeff_mk, Radial.layers,hv,if_false,add_zero, Complex.ofReal_neg,tilted]
   let u := bend (crest T ρ k.1) k.2
   congr 2
   let L : ℝ×AxisChart G T →L[ℝ] ℝ×SpaceVar T G := (ContinuousLinearMap.fst ℝ _ _).prod (Tangent.shift T k.1)
   have he : track T i η p R k.1 A = F ∘ L := funext (stretch_graph T i k.1)
   have hg : ContDiffAt ℝ ∞ (track T i η p R k.1 A) 0 := he.symm ▸ ((L.map_zero.symm ▸ hf : ContDiffAt ℝ ∞ F (L 0)).comp 0 L.contDiff.contDiffAt)
   have hy : Asym.layer (track T i η p R k.1 A) u = Asym.layer F (L u) := by
      apply Asym.Near.unique' (layer_ray hg u); convert layer_ray hf (L u) using 1; funext t; rw [he, Function.comp_apply,map_smul]
   have ht := congr_arg (fun x : PowerSeries ℂ=> coeff (r+2) x) hy
   have hU : L u=(1,k.1,k.2+crest T ρ k.1) := Prod.ext rfl (Prod.ext (one_smul ℝ k.1) rfl)
   simp only [layer,coeff_mk,hU,Complex.ofReal_inj] at ht; exact ht

include ht
omit i hp hr h hW hh hη [Fintype I] in
lemma source_stage (r : ℕ)(ρ : Dir G c→AxisChart G T)(s : B.Mode) : Shear.Rolls (m+r) fun x : SpaceVar T G=>
       (coeff r (Therm.rises m (Pins.ink T x.1 W) (x.2+crest T ρ x.1))).part s := by
   let F: ℝ×SpaceVar T G→ ℂ:=fun z=> (W (fixture T z)).part s
   have hf : ContDiffAt ℝ ∞ F 0:= scenery T (fun z=> (W z).part s) (ht.smooth s)
   have he k : ribbon (fun z=> (Pins.ink T (Prod.fst (α:=Dir G c) (β:=AxisChart G T) k) W z).part s) (bend (crest T ρ k.1) k.2) = ribbon F (toGraph T ρ k+(1,0)) := by
      let L : ℝ × AxisChart G T →L[ℝ] ℝ × SpaceVar T G := (ContinuousLinearMap.fst ℝ _ _).prod (Tangent.shift T k.1)
      let u:= bend (crest T ρ k.1) k.2
      rw [tilted, ← show L u=(1,k.1,k.2+crest T ρ k.1) from Prod.ext rfl (Prod.ext (one_smul ℝ k.1) rfl)]
      have ht : (fun z => (Pins.ink T k.1 W z).part s)= F ∘ L := rfl
      apply Near.unique' (ribbon_test (x:=u) ?_) -- edit
      rotate_left
      · rw [ht]; exact (L.map_zero.symm ▸ hf : ContDiffAt ℝ ∞ F (L 0)).comp (f:=L) 0 L.contDiff.contDiffAt
      convert ribbon_test hf (L u) using 1; funext t; rw [← map_smul L]; rfl
   simp only [rise_coeff, add_comm r m];
   change Shear.Rolls _ fun t:SpaceVar T G=> coeff (m+r) (ribbon _ (bend (crest T ρ t.1) t.2))
   simp only [he,ribbon_coeff]
   exact (Shear.Rolls.jets (fun i => (F i).re) _ _ _).add ((Shear.Rolls.jets (fun i => (F i).im) _ _ _).scale _)

omit [Fintype I] in
theorem vertex_ready (r : ℕ)(t : Multi.Hot (mixed r B)) :
    Shear.Rolls (Shear.vertexRate r m t) fun x : SpaceVar T G=> (encode r (pre T i η p R x.1 A m W ρ x.2)).part t.val := by
   let k := (Pair.fst t.val).val.card
   simp only [Grade.encode_part, pre, Therm.board,map_add,Poly.part_plus];
   apply Shear.Rolls.scale (k:=Shear.vertexRate r m t) _ (k.factorial:ℂ)
   apply Shear.Rolls.add
   · unfold Shear.vertexRate; split
     next hv =>
       simp_rw [Therm.rise_coeff];
       have hg (x : SpaceVar T G) : (fun z=> ((Pins.ink T x.1 W) z).part B.quiet) = fun _ => 0 := funext fun _=> ht.silent _
       change Shear.Rolls _ fun x:SpaceVar T G=> coeff (k+m) (ribbon _ _)
       -- prove zero
       convert Shear.Rolls.const (X:=Dir G c) (E:=AxisChart G T) (k:=k+2) 0 using 1; funext x
       rw [hv,hg x, show ribbon (fun _ : ℝ × AxisChart G T=>0) _= (0: PowerSeries ℂ) from ?_,map_zero]
       ext1 n; simp [ribbon_coeff,Radial.jet]
     have hh := source_stage T ht k ρ
     rw [add_comm _ m]; apply hh
   by_cases h : Pair.snd t.val=B.quiet
   · simp only [Grade.scalar,h, Poly.bead,PowerSeries.coeff_map, RingHom.coe_mk,MonoidHom.coe_mk, OneHom.coe_mk,Poly.part_send, if_true]
     simpa [Shear.vertexRate,h] using! (vacuum_stage T i ‹Critical T p R ρ› hW hh hη ((Pair.fst t.val).val.card))
   simp only [Grade.scalar,PowerSeries.coeff_map, Poly.bead, RingHom.coe_mk,MonoidHom.coe_mk, OneHom.coe_mk,Poly.part_send, if_neg h]; exact Shear.Rolls.const 0

theorem spans (s : B.Mode)(r : ℕ) :
   Shear.Payment (r + if s=B.quiet then 2 else m*s.val.card) fun x =>
       (PowerSeries.coeff r (Grade.logarithm (formal T i hp hr h η x A m W))).part s := by
   apply Shear.budgets (f:=fun x=> pre T i η p R x A m W ρ) (Chart.tangent G T.Free) _ (fun x=> (ready T i x _ ht).1) (fun x=> (ready T i x _ ht).2) r m
   intro j; exact vertex_ready T i h hW ht hh hη r j
end YM.RG02.Fk.Draw
