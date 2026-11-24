import YM.RG02.Flat.Projection

/-!
Invariant reading on different lifts, tags, even locally equivalent chart ratios.
Each through any finite order. NO claim on same bounds uniformly in the periods
or on a restriction of RG calendars. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk.Draw
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries Profiles
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}
variable (T F : Forest S.ratio)

lemma lane : dim T G = dim F G := by
    unfold dim; exact (Work.F05.index (Work.F05.freeEquiv T F)).toLinearEquiv.finrank_eq
lemma reroutes (x : Config G f) : reroute T F G (wick T x)=wick F x := by
    change wick F (T.drape _)=_
    rw [wears]; exact wick_gauge F x (T.foldAt x) (fun _ => T.fold_root ..)
private lemma wreath : reroute T F G (1 : T.Slice G)=1 := by
   rw [← Work.F05.exposure_zero]; exact Work.F05.reroute_exposure_zero ..

variable {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η O : ChartRatio G} {w y : ℝ}{ρ : Dir G c → AxisChart G T}{u : Dir G c→AxisChart G F}(i t : S.Choices)
    (hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)(hw : 0<y)(hz : PriceGap F p R y)(hg : Critical F p R u)
variable {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ)(ht : Ink m W)(hh : Ambient A)(hs : S.patch.Branches S.kernel G)(hη : LocalRatio η)(hO : LocalRatio O)(x : Dir G c)
variable {Y : Bed}(hY : ∀ T:Forest S.ratio, Comptroller T Y p R)
include hp hr h hw hz hg hW ht hh hs hη hO hY

theorem independence :
      multiplier T i hp hr h η x=multiplier F t hw hz hg O x ∧
      formal T i hp hr h η x A m W=formal F t hw hz hg O x A m W := by
    rw [multiplier_constant F i hw hz hg t hs,formal_constant F i hw hz hg t O x hs]
    let U:=formal T i hp hr h η x A m W; let V := formal F i hw hz hg O x A m W
    let a:=multiplier T i hp hr h η x; let b:= multiplier F i hw hz hg O x
    have ha : basepoint U=1 := configured T i hp hr h η x ht
    have hB : basepoint V=1 := configured F i hw hz hg O x ht
    obtain ⟨M,hM,Hm,hm⟩:= target T i hp hr h hW ht hh hs hη x (hY T)
    obtain ⟨Q,hQ,Hq,HQ⟩:= target F i hw hz hg hW ht hh hs hO x (hY F)
    let E := reroute F T G
    let P := Q ∩ E ⁻¹' M
    have htE : Tendsto E (𝓝 1) (𝓝 1) := by
       refine (show E 1=1 from wreath ..) ▸ E.continuous.tendsto _
    have he : P∈𝓝 1:= inter_mem hQ (htE hM)
    have hv : MeasurableSet P := Hq.inter (E.measurable Hm)
    have hp' := (HQ P he hv inter_subset_left).2
    have HD : E.symm ⁻¹' P ∈𝓝 (1:T.Slice G) := by
       exact (show Tendsto E.symm (𝓝 1) (𝓝 1) from ((show E.symm 1=1 from wreath ..) ▸ E.symm.continuous.tendsto _)) he
    have HH : E.symm ⁻¹' P ⊆ M:= fun i hi=> by have hv : E (E.symm i)∈ M:= hi.2; simpa using hv
    have hx := (hm _ HD (E.symm.measurable hv) HH).2
    have hy : ∀ (t:ℝ), cut T i p R x A m W t (wick T ⁻¹' (E.symm ⁻¹' P)) = cut F i p R x A m W t (wick F ⁻¹' P) := by
       have hu : E.symm ∘ wick T=wick F := funext fun x=> reroutes T F x
       unfold cut; rw [lane T F,← preimage_comp]; simp only [hu, forall_const]
    simp_rw [hy] at hx
    have heq : (a:ℂ) • U=(b:ℂ) • V:= hx.uniquely hp'
    have he := congr_arg (fun v:Script B=>basepoint v) heq
    simp only [basepoint_read, coeff_smul, Poly.part_smul] at he ha hB
    rw [ha,hB,mul_one,mul_one] at he
    refine ⟨Complex.ofReal_injective he,?_⟩
    rw [he] at heq
    exact smul_right_injective _ (Complex.ofReal_ne_zero.mpr (multiplier_pos F i hw hz hg O x hO).ne') heq

end YM.RG02.Fk.Draw
