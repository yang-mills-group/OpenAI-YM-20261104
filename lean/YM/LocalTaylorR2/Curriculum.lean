import YM.LocalTaylorR2.Tolls
/-!
 Component estimates on the tail as Utopia + recoil Taylor power
 system. March launch plan with F inserted through all leases. -/
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
lemma pearls (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ (t ζ : ℝ),-(1/2:ℝ)<t→ t<Q.rate → 0≤ζ →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r b d p : ℝ→ℝ) (k l:ℕ), Rate G L (-(1/2)) q ∧ Rate G L 0 r ∧ Rate G L t b ∧ Rate G L 0 d ∧ Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), 8*o.a* Pressure.fiery G x L ≤ A/2 ∧
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, LocalBookingsR2 ζ (b x) Ξ ∧ StoresR2 H i (V x) (q x) A (d x) k (p x) l χ := by
  obtain ⟨n,hN⟩:= Utopia.leasedUtopiaR2 P Q
  refine ⟨n,fun L hL t ζ ht ht' hζ D hD i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,b,hC,hr,hb',hχ⟩:= hN L hL t ζ ht ht' hζ D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  let e x:= 1+|F x|
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨C,(fun x=>|B x|), r,b,(fun x=>|U x|),e,k,K,hb,hr,hb',hh hU,(Rate.const 1).add (hh hF),?_⟩
  filter_upwards [hχ,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx h hx hp c f S T hS hT R C' H
  obtain ⟨Ξ,hΞ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  refine ⟨hp,Ξ,hΞ,le_add_of_nonneg_right (abs_nonneg _),abs_nonneg _,?_,?_⟩
  · intro F' X ht hζ hK hM z E _ _ _ Y y hy' hf
    obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
    have hZ:= hθ.localP F' X ht hK hM
    have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [ht,hh.length_eq]; exact hp)
    exact ⟨hp,fun p=> h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw _⟩
  intro F' X ht hζ hK hM p'
  let I:= edgesM S (H.unionP p') (radiusB x); let S':=1+H.shapeW p'; have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  let hm:=globes I (hθ.localP F' X ht hK hM).sails (k*i*2)
  let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
  have hI: i'≤ S'*ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
    have h:= crewsC H p'; rw [hh.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
  have he: 1≤e x:= le_add_of_nonneg_right (abs_nonneg _)
  have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
  have hp := hm.2.trans (hΨ x i' V S' hx' (Nat.cast_nonneg _) hI hV')
  apply hp.trans
  exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
      (le_self_pow₀ (one_le_mul_of_one_le_of_one_le he (one_le_pow₀ hx')) (by omega))
lemma curriculum (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ (t0 ζ : ℝ),-(1/2:ℝ)<t0 → t0<Q.rate → 0≤ζ →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q D' p' bm: ℝ→ℝ) (k l:ℕ), Rate G L 0 B ∧ Rate G L 0 r ∧ Rate G L t0 bm ∧ Rate G L 0 D' ∧ Rate G L 0 p' ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N : Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) (l+i) χ, LocalBookingsR2 ζ (bm x) N.conduit ∧ StoresR2 H i (v x) (d x) A (D' x) k (p' x) l χ := by
  obtain ⟨n,h⟩:= pearls P Q; refine ⟨n, fun L hL t0 ζ ht ht' hζ D hD i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,b,u,p,k,l,_,hr,hbm,hu,he',hF⟩:= h L hL t0 ζ ht ht' hζ D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x := p x*(1+u x+2*r x)^i
  have hB:Rate G L 0 B':=by
    unfold B'; simpa only [zero_mul,zero_add] using! (he'.mul ((((Rate.const (G:=G) (L:=L) 1).add hu).add (hr.mul_left 2)).pow i))
  have hu':= Glass.portal P D L hD i χ hh (hp.mono (fun x hh=> by unfold v; positivity)) o.K o.γ W o.indexPay o.f
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,u,p,b,k,l,hB,hr,hbm,hu,he',?_⟩
  filter_upwards [hp,hF,hu'] with x hx hm' hu c f S T hS hT R C' H
  obtain ⟨ht1,Ξ,hQ,hΞ⟩:= hm' c f S T hS hT R C' H
  have hw:0≤ B' x:= by unfold B'; have h₁:=Ξ.active; have h₂:=hΞ.fuel; have h₃:=hΞ.sure; positivity
  have hv := H.laws.data
  have hΘ: Oboe H i (v x) (B' x) (l+i) A a Ξ:= ⟨hA,ht1,hΞ.earnings Ξ,fun F X hX hF hh hh'=> hu c f S T hS hv.funds hv.access F X hh hF hX (hv.localP F X hX hh hh')⟩
  exact ⟨⟨Ξ,hΘ,mul_nonneg hZ.le hx.le,hx.le,(by have he:= hv.room.temperatures; rw [hv.funds.length_eq] at he; exact he),
    (by unfold v; positivity),hw, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hQ,hΞ⟩

end YM.LocalTaylorR2
