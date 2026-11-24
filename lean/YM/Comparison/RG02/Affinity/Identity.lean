import YM.Comparison.RG02.Affinity.Door
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Affinity
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Gaussian PertExtension.Series PertExtension.Series.Tested Laplace.Prism Laplace
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {f : House X I→ℝ} {F : Hot R→House X I→ℂ} {l: Hot R→ℕ} [Fintype V]
local notation "E"=>House X I
namespace Door
variable (x : X)

-- smooth on the aperture interior; use finite marker horizon as given. no gauge-invariance
-- of `F` needed for this (would be handled in reading). No global envelope assumed either.
omit [FiniteDimensional ℝ X] in
lemma inside (hf : GradeAt 2 f) (hF : ∀ i, GradeAt (l i) (F i)) :
    ∃ δ:ℝ, 0 < δ ∧ ∀ ε g, ε≤δ → 0<g → ∀ Q : Gaussian.Table I,
      Good (cloud Q) ((circle x g ε).indicator (Assembly.numeric l F f g ∘ season x)) := by
   obtain ⟨d,hd,hD⟩ := Metric.eventually_nhds_iff.mp ((hf.smooth.eventually (by simp)).and (eventually_all.mpr (fun i=> (hF i).smooth.eventually (by simp))))
   refine ⟨d/2,half_pos hd,fun ε g he hg Q i=> ?_⟩
   let A:=circle x g ε (I:=I)
   rw [mark_cut, integrable_indicator_iff (closed_circle ..|>.measurableSet)]
   apply ContinuousOn.integrableOn_compact (compact_circle x g ε hg)
   intro v hv
   suffices H : ContinuousAt (atMark i (Assembly.numeric l F f g ∘ season x)) v from H.continuousWithinAt
   let p := fun v:I→ℝ=> g • season x v
   have h:‖p v‖<d:= lt_of_le_of_lt (((circle_spec ..).1 hv).trans he) (half_lt_self hd)
   obtain ⟨h₀,hs⟩ := hD (by rwa [dist_zero_right]:dist (p v) 0<d)
   have hp : Continuous p := (season_cont x).const_smul g
   have hz := season_cont (I:=I) x
   letI : MeasurableSpace E := borel _
   have hr : ContinuousAt (fun y:I→ℝ=> Radial.higher f g (season x y)) v :=
      --
      (((h₀.continuousAt.comp hp.continuousAt).neg.div_const (g^2))).add (((Radial.Smooth.continuousJet f 2).comp hz).continuousAt)
   have hh (i: Hot R) : ContinuousAt (fun y=> (smoothMark l F g (season x y)).part i.val) v := by
      simp_rw [mark_read]; exact ((hs i).continuousAt.comp hp.continuousAt).const_smul ((g ^ l i)⁻¹)
   have hm (y:I→ℝ): (Poly.pass (smoothMark l F g (season x y))).part i=∑ s∈shards R i,∏ j∈s.val,(smoothMark l F g (season x y)).part j.val:= Cumulants.pass_partition _ (part_lit_quiet _) i
   unfold atMark; simp_rw [Function.comp_apply,Assembly.numeric,Poly.product_bead, Poly.part_smul,hm]
   exact (Complex.continuous_ofReal.continuousAt.comp hr.rexp).mul (tendsto_finsetSum _  (fun i _=> tendsto_finsetProd _  (fun j _=> hh j)))

variable (Q : Gaussian.Table I) (hQ : Q.PosDef) (S : Vibe X I) (s : R.Mode)
local notation "♩" => ((1,x,0):House X I)
local notation "L"=> reach (I:=I) X

variable (h : Ray Q f) (hF : ∀ i, GradeAt (l i) (F i))
include h hQ hF
lemma pulled (r : ℕ) (hq : Q.IsSymm) (i : ℕ) (he : i≤r):
    detail (Assembly.prescription ♩ L (R:=R) l F f Q hq r) s i = detail (Assembly.prescription ♩ L l (fun j=> F j ∘ S.effect) (S.price f) Q hq r) s i:= by
   have hp:=funded h.root hF
   have hs:=S.prices h
   let C'(j:Hot R) := F j ∘ S.effect
   let f' := S.price f
   obtain ⟨a,ha,A⟩:= Laplace.Prism.squeeze ♩ L r s hQ hq hp
   obtain ⟨b,hb,B⟩:= Laplace.Prism.squeeze ♩ L r s hQ hq (f:=f') (funded hs.root (F:=C') (l:=l) fun i=> (hF i).coarse S.no_jets.2 S.base)
   obtain ⟨d,hd,h⟩:=pull_cap x S hb -- shadow h!
   obtain ⟨e,hr,H⟩:=inside x (f:=f) (l:=l) ‹Ray Q f›.root hF
   let m:= min (a/2) (min d e)
   have hm:0 < m := lt_min (half_pos ha) (lt_min hd hr)
   have hd:m≤d := le_trans (min_le_right ..) (min_le_left ..)
   let p g:= (circle (I:=I) x g m).indicator (Assembly.numeric l F f g ∘ season x)
   let q g:= (pull x S m g).indicator (Assembly.numeric l C' f' g ∘ season x)
   have hz:= h _ hd
   have hu:=root_circle x m (I:=I) hm
   have hP : ∀ᶠ g in along, Good (cloud Q) (p g) := eventually_pos.mono (fun g hg=> H m g (le_trans (min_le_right ..) (min_le_right ..)) hg Q)
   have hK : ∀ᶠ g in along, Good (cloud Q) (q g) ∧ charge (cloud Q) (p g)=charge (cloud Q) (q g) := by
       filter_upwards [hP,eventually_pos,qualifies x S] with g hP hv he
       have hh:= Vibe.within R (l:=l) (F:=F) x S hv.ne' he ‹Ray Q f› hQ (circle x g m); exact ⟨hh.1.mp hP,hh.2⟩
   let f1:=fun g=> (charge (cloud Q) (p g)).part s
   let f2:=fun g=> (charge (cloud Q) (q g)).part s
   have ht : f1=ᶠ[along] f2:= hK.mono fun g he=> congrArg (fun r=> Poly.part r s) he.2
   have hB:= B (pull x S m) hz (pays x S m hm) (hK.mono fun g hg => ⟨(Vibe.continuous_outreach x S g).measurable (closed_circle ..|>.measurableSet), hg.1⟩)
   have hA:= A (fun g=>circle x g m) (cap_circle x m a ((min_le_left ..).trans_lt (half_lt_self ha))) hu (hP.mono fun g hg=> ⟨(closed_circle ..).measurableSet,hg⟩)
   exact trial_gap (trial_congr ht hA) hB i he

lemma agree (r : ℕ) (hq : Q.IsSymm) : Assembly.prescription ♩ L (R:=R) l F f Q hq r= Assembly.prescription ♩ L l (fun i=> F i ∘ S.effect) (S.price f) Q hq r := by
   refine (sym_coeff _ _ (prescription_sym _ _ _ _ _ _ _ hQ) (prescription_sym _ _ _ _ _ _ _ hQ)).2 (fun i hi=> ?_)
   ext s; exact pulled x Q hQ S s h hF r hq i hi
end Door
end YM.Comparison.RG02.Affinity
