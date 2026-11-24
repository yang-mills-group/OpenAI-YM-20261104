import YM.LocalTaylorR2.Marker.Light

set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Census Animals Push.AbsoluteSums.Paths
open Itinerary Reserves PhysicalNext PhysicalNext.Repeat
namespace Marker
open PhysicalNext.Repeat.Daisy
lemma scripts (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ (t0 ζ : ℝ),-(1/2:ℝ)<t0 → t0<Q.rate → 0≤ζ →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q D' p' bm K: ℝ→ℝ) (k l:ℕ), Rate G L 0 B ∧ Rate G L 0 r ∧ Rate G L t0 bm ∧ Rate G L 0 D' ∧ Rate G L 0 p' ∧ Rate G L 0 K ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N : Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) (l+i) χ, LocalBookingsR2 ζ (bm x) N.conduit ∧ StoresR2 H i (v x) (d x) A (D' x) k (p' x) l χ ∧ Herd H N.conduit A (B x) (l+i) ∧ Tinted G x (K x) (d x) o.a L χ i := by
  obtain ⟨n,h⟩:= pearls P Q; refine ⟨n, fun L hL t0 ζ ht ht' hζ D hD i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,b,u,p,k,l,hd,hr,hbm,hu,he',hF⟩:= h L hL t0 ζ ht ht' hζ D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  obtain ⟨K,hK,hU⟩:= tinted (j:=i) (χ:=χ) d hd o.a
  let B' x := p x*(1+u x+2*(r x+K x))^i
  have hB:Rate G L 0 B':=by
    unfold B'; simpa only [zero_mul,zero_add] using! (he'.mul ((((Rate.const (G:=G) (L:=L) 1).add hu).add ((hr.add hK).mul_left 2)).pow i))
  have hu':= Glass.portal P D L hD i χ hh (hp.mono (fun x hh=> by unfold v; positivity)) o.K o.γ W o.indexPay o.f
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,u,p,b,K,k,l,hB,hr,hbm,hu,he',hK,?_⟩
  filter_upwards [hp,hF,hu',hU] with x hx hm' huP hU' c f S T hS hT R C' H
  obtain ⟨ht1,Ξ,hQ,hΞ⟩:= hm' c f S T hS hT R C' H
  have hy:= herded H (Ξ:=Ξ) hU' hΞ (show _≤B' x from le_rfl)
  have hw:0≤ B' x:= by unfold B'; have h₁:=Ξ.active; have h₂:=hΞ.fuel; have h₃:=hΞ.sure; have h:=hU'.salt; positivity
  have hv := H.laws.data
  have hΘ: Oboe H i (v x) (B' x) (l+i) A a Ξ:= ⟨hA,ht1,hy.unmarked,fun F X hX hF hh hh'=> huP c f S T hS hv.funds hv.access F X hh hF hX (hv.localP F X hX hh hh')⟩
  exact ⟨⟨Ξ,hΘ,mul_nonneg hZ.le hx.le,hx.le,(by have he:= hv.room.temperatures; rw [hv.funds.length_eq] at he; exact he),
    (by unfold v; positivity),hw, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hQ,hΞ,hy,hU'⟩

end Marker
end YM.LocalTaylorR2
