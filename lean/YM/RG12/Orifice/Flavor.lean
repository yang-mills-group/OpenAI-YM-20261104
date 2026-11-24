import YM.RG12.Orifice.Almond
import YM.RG12.Burst.Wardrobe
import YM.RG12.Burst.Axes
import YM.RG12.Burst.Birch
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy.Charity.RG12
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters Blaze.March
open Mallow
open Push.SectorMeasure
open PhysicalNext.Repeat.Height Blush.Burst10
-- all losses for our criterion eligible. post.To make precise table in receipts
-- `κ_to-consume`, due per occurrence independent of radius, except exact Gas coefficient. Only U=1 with repeated normalized direction, determinant part only. Colour.Poly.Higher. Any ℓ beyond test.P.S.Ship. Approx issue <1 exponent.
def price12 (H:Cash W x μ L Q o C T R)(p:H.fragrances):ℝ:=max 1 (|coefficient H.seam p.2| / ↑(p.1+1).factorial)
def Cool (Q:ConnectedActivityE6.Target G P)(L:Side) (W μ:ℝ) (o:Target.Order G W) (D:RG.Stage) (_i:ℕ) (x:ℝ) (ε:ℝ):Prop:=
    let d:=D.order
    let q:=2*fiery G x L
    2≤d→G.Simple → ∀ (c f:Side)(S:StepData c f)(T:Tube G S), Stamp T→ ∀ R C (H:Cash W x μ L Q o C T R) (Z: Directions G c), ‖Z‖ ≤q → ∀ (J:Bond f)(K': Leaf R)(p:H.fragrances), twin12 H J K' p →
      ‖leftDerivs (matin K' H p Chi.canonical) [Z,Z] 1‖ ≤ price12 H p*K'.weight*(betaF G x L ^ ε)

lemma manager12 (H:Cash W x μ L Q o C T R) (j m:ℕ) (q t v Y A b r B g:ℝ)(N:Captain H j q t v Y A b r B g m Chi.canonical)(hN:Herd H N.conduit A B m) (Z:Directions G c)
    (J:Bond f)(K':Leaf R)(p:H.fragrances)(hp:twin12 H J K' p) (h : 2≤j) (hs:0<Pressure.temp x){w:ℝ}(he:0<w)(h0:Spritz H (fun t:ℝ=>increment (1:Config G c) (t • Z)) J j w)
    (hu:Mode (fun t:ℝ=>increment (1:Config G c) (t • Z)) 0 j v):
    ‖leftDerivs (matin K' H p Chi.canonical) [Z,Z] 1‖ ≤ 4* price12 H p*K'.weight*w :=by
  let f:= matin K' H p Chi.canonical; let L(t:ℝ):=increment (1:Config G c) (t • Z); let W:= L 0
  have hW:W=(1:Config G c):=by unfold W L; simp
  have he:= Hess12 H N J hW hu hN he h h0 hs K' p hp -- order
  have ht:= Next.Foundations.leftDerivs_diag (1:Config G c) Z f 2 0; rw [zero_smul,Work.G07.at_zero_increment] at ht
  change ‖leftDerivs f _ _‖ ≤_; rw [show [Z,Z]=List.replicate 2 Z from rfl, ht]; unfold price12; apply he.trans_eq; ring

lemma tethers (Q: YM.ConnectedActivityE6.Target G P){ε:ℝ} (hr:(-1:ℝ)<ε) : ∃ n:ℕ,∀ L:Side,n≤L.val→∀ (W μ:ℝ) (o:ConnectedActivityE6.Target.Order G W) (D:RG.Stage)(k:ℕ),0<W→0<μ→∀ᶠ x in atTop,Cool Q L W μ o D k x ε:=by
  obtain ⟨n,h⟩:= Daisy.timing P Q
  refine ⟨n,fun L hL W μ o B k hW hm=>?_⟩
  set v := B.order; by_cases hv:2 ≤ v ∧ G.Simple
  swap; · exact Eventually.of_forall fun x hp hq=>(hv ⟨hp,hq⟩).elim
  obtain ⟨hv,hG⟩:=hv
  by_cases he:∃ D: RG.Patch,D.Branches P.bind G∧D.L=L∧D.J=P.j
  swap; · exact Eventually.of_forall fun x _ _ c f S T _ R C H=> let h:=H.laws.data.funds; False.elim (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩)
  obtain ⟨D,he,Hh,hJ⟩:= he; obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G v
  obtain ⟨u,hu,h'⟩:=exists_between hr
  let t x:=2*Pressure.fiery G x L
  have ht : Rate G L (-(1/2)) t:=Rate.flame.mul_left _; have hp:∀ᶠ x in atTop,0<t x:= ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x hx=> mul_pos zero_lt_two (Work.E09.temp_pos hx)
  let v0 x:= ((v:ℝ)+1)*Z*t x; have hT : Rate G L (-(1/2)) v0:= ht.mul_left _; have hV:∀ᶠ x : ℝ in atTop,0≤v0 x:= hp.mono fun x h=>by unfold v0; positivity
  obtain ⟨C,d,r,X,i,Hep,hB,hX⟩:= h L hL D he v Chi.canonical W hW μ hm o A a hA v0 hT hV
  have hg:= Glass.portal P D L he v Chi.canonical hT hV o.K o.γ W o.indexPay o.f
  filter_upwards [Blush.Burst10.grabbed hG P L D he v hv W o v0 hT u hu,hX,hp,hg,eventually_gt_atTop (0:ℝ),Delay.shift_pos G L, ((Rate.power (G:=G) (L:=L) (a:=u)).mul_left 4 ε h')] with x hu h hh hP hx hk h0 _ _ c f S T hC R C' H F hF j K' p hp
  have hs:= (H.laws.data.funds).patch Hh hJ; obtain ⟨hZ',N',hN⟩:= h c f S T hs hC R C' H
  have hO: Oboe H v (v0 x) (|X x|) i A a N':= ⟨hA,hZ',hN.unmarked,fun F X hX hF hv hm=> hP c f S T hs H.laws.data.funds H.laws.data.access F X hv hF hX (H.laws.data.localP F X hX hv hm)⟩
  have hT:0 ≤Z*t x:=by positivity
  let N : Captain H v C (d x) (v0 x) (t x) A a (r x) (|X x|) (Z*t x) i Chi.canonical:= ⟨N', hO, hT,hh.le,(by have he:= H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at he; exact he),(by unfold v0; positivity),abs_nonneg _, ⟨fun _=>hq _ _ hh.le⟩,(by unfold v0; nlinarith [mul_nonneg hZ.le hh.le])⟩
  let f'(q:ℝ):=increment (1:Config G c) (q • F)
  have hf: Mode f' 0 v (v0 x):=by
     have hh := hq c _ hh.le F hF ℝ (fun _:ℝ=>1) 0 0 (show Mode (fun _:ℝ=>(1:Config G c)) 0 v 0 from ⟨le_rfl,fun _=> a_oneB G _ le_rfl⟩)
     let P' := ContinuousLinearMap.inr ℝ ℝ ℝ; have hl:‖P'‖≤(1:ℝ):= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp [P',Prod.norm_def])
     refine ⟨(by unfold v0; positivity),fun i=>?_⟩
     rw [add_zero] at hh; have h':Brush v (royalty G) (Z*t x*1) (fun z=> G.mat (increment ((1:Config G c)) ((P' z).2 • F) i)) 0:= Brush.reading P' (g:=fun t:ℝ×ℝ=>G.mat (increment (1:Config G c) (t.2 • F) i)) (by rw [map_zero]; exact hh.atLink i) hl
     exact h'.climb le_rfl (by rw [mul_one]; unfold v0; nlinarith [mul_nonneg hZ.le (show 0≤ t x from (by unfold t; exact mul_nonneg zero_le_two (Work.E09.temp_pos hk).le))])
  obtain h:= manager12 H _ _ _ _ _ _ _ _ _ _ _ N hN F j K' p hp hv (Work.E09.temp_pos hx) (Real.rpow_pos_of_pos hk u) (hu c f S T hs H.laws.data.funds.length_eq Q μ C' R H f' (by unfold f'; simp) hf j) hf
  have hz:0≤price12 H p*K'.weight:=mul_nonneg (zero_le_one.trans (le_max_left ..)) K'.profit
  exact h.trans ((le_of_eq (by ring:_=(price12 H p*K'.weight)*(4* betaF G x L^u))).trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h0) hz))

def sticker12 (G:Gauge)(ε:ℝ)(ht:-1<ε):Decal G where
     rub _ Q _ L W μ o D p x:=Cool Q L W μ o D p x ε
     good _ Q _:= by obtain ⟨n,h⟩:=tethers Q ht; exact ⟨n,fun L hl W μ o D i _=>h L hl W μ o D i⟩
end YM.PhysicalNext.Repeat.Daisy.Charity.RG12
