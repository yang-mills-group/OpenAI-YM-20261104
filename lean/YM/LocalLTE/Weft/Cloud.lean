import YM.LocalLTE.Weft.Packet
/-! Arp kernel prices. Verging openings. Walk chart costs from Ep Occurrence. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
variable {v z r W s y η γ B : ℝ} {j n m : ℕ}
lemma cloudCard {P:Teller G}(L:Side)(D:Patch)(hd:D.Branches P.bind G){d p :ℝ→ℝ}{N : ℝ→ℕ}(Q:YM.ConnectedActivityE6.Target G P){W:ℝ} (o:Target.Order G W)(j:ℕ)(h₁:1≤j){v κ k:ℝ}(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hR:Reliable G κ k)(hk:Rate G L 0 d)(hN:Rate G L 0 fun t=>(N t:ℝ)):∃ V :ℝ→ℝ, Rate G L 0 V ∧ ∀ᶠ t in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖<p t → ∀ (y:Site f)(i:ℕ)(Y':LocalLTE.FrameBox.Grove y), i≤N t→1 ≤ V t∧ Brush j (V t) 1 (Y'.crook i Chi.canonical κ ∘ inputΛ X z) x:=by
  obtain ⟨A,C₀,R,hA,hC,hQ,H⟩:= thistles L D hd Q W o j h₁ hW h hp hk hp'
  obtain ⟨M,r,hM,hr,hL⟩:= chord_chart_cost G
  obtain ⟨Y,R',hP'⟩:=Frond.cleanly G j 1 zero_lt_one
  -- hP': Suitable G j Y R' 1
  have hq':0 ≤ Y:= (hP'.sound (1:G.El) (by rw [G.mat_one,sub_self,norm_zero]; exact hP'.pos.le)).nonneg -- edit
  let z t:=M*|A t| + M*|A t|; let P t:= (8*(N t:ℝ)+1)*z t; let v' (t:ℝ):=(1+royalty G)*(LocalLTE.Frame.expense G (N t) (|R t|))
  have hq:= hA.compare (v:=fun x=>|A x|) (Eventually.of_forall fun x=> (abs_abs _).le); have hv:Rate G L v P:= by unfold P; simpa only [zero_add] using! (((hN.mul_left 8).add (Rate.const 1)).mul ((hq.mul_left M).add (hq.mul_left M)))
  let V₀:ℝ:=1+j.factorial*Y; let Θ t:= (Pressure.fiery G t L)⁻¹; let V t:= 1+V₀*(1+v' t)^j
  have he':=(hQ.compare (v:=fun x=> |R x|) (Eventually.of_forall fun _=> (abs_abs _).le)); have hu : Rate G L 0 v':= by
    let B x:=4*(N x:ℝ)*(|R x| *royalty G); have hg:Rate G L 0 B:= by simpa only [add_zero] using! ((hN.mul_left 4).mul (he'.mul_right _))
    unfold v' LocalLTE.Frame.expense; exact ((hg.mul_right _).add ((he'.mul_right _).add hg)).mul_left _
  refine ⟨V,?_,?_⟩
  · exact (Rate.const 1).add (((((Rate.const 1).add hu).pow j).weaken (by simp)).mul_left _)
  filter_upwards [H,hA.below h _ hr,hv.below h _ hR.down,(hv.mul_left G.colorScale).below h _ hP'.pos] with t ht hv' hk' hK c f S T hS μ α H F X ht' hX z' hz x hx y i Y' he
  let U:=inputΛ X z'; let s:= p t; have hp:=ht c f S T hS _ _ H F X ht' hX z' hz
  have hh x (hx:‖x‖≤p t) (i:Bond f): G.chord (U x i)≤ z t:= by
    let v:= twig X z' x; let V:=increment 1 v.1
    have hT:‖v.1‖≤ |A t| ∧ ‖v.2‖≤|A t|:=max_le_iff.mp ((hp x hx).1:‖v‖≤_)
    have hv (i:Bond f): G.chord (replica S.ratio (V:Config G c) i) ≤ M*|A t| := by
      unfold replica; split; next => rw [G.chord_one]; positivity
      next =>
        let j:=S.ratio.parent i.1; let k:Bond c:=(j,i.2)
        change G.chord (increment (1:Config G c) v.1 k) ≤ _; rw [increment,Pi.one_apply,mul_one]; exact (hL _ (((norm_le_pi_norm ..).trans hT.1).trans hv')).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans hT.1) hM.le) -- parent? neg case
    exact (G.chord_triangle (G.lieExp (v.2 i)) (replica S.ratio V i)).trans (add_le_add ((hL _ (((norm_le_pi_norm ..).trans hT.2).trans hv')).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans hT.2) hM.le)) (hv _))
  let r:= |R t|; have hp:(8*i+1:ℝ)* z t ≤ P t:= by unfold P; gcongr
  have hΨ : Brush j V₀ (v' t) (LocalLTE.FrameBox.Grove.crook Y' i Chi.canonical κ ∘ U) x:=
    (LocalLTE.FrameBox.climbs Y' hR i (ht c f S T hS _ _ H F X ht' hX z' hz x hx.le|>.2.2) hP'
       (by filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with v hv; exact hh v hv.le) hq' (show 0≤ z t from by unfold z; positivity) (hp.trans ((le_abs_self _).trans hk')) ((mul_le_mul_of_nonneg_left hp G.colorScale_pos.le).trans ((le_abs_self _).trans hK))).climb (le_add_of_nonneg_left zero_le_one) (by unfold v' LocalLTE.Frame.expense; have hg:=royalty_ge G; gcongr)
  exact ⟨le_add_of_nonneg_right hΨ.trim.nonneg,hΨ.trim.climb (le_add_of_nonneg_left zero_le_one) le_rfl⟩
end YM.ConnectedActivityE6.Blaze.Vine
