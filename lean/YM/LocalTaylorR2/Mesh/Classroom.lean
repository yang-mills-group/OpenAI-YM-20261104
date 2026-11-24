import YM.LocalTaylorR2.Mesh.Ripple
/-!
 Component estimates on the tail as Utopia + recoil Taylor power
 system. March launch-augmentation plan with F inserted through all leases. -/
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
namespace Mesh
structure Regime (G:Gauge) where
  symbol : ∀ {c f L : Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}{P:Teller G}{Q:YM.ConnectedActivityE6.Target G P}{W x μ C:ℝ}{o:Target.Order G W}, Cash W x μ L Q o C T R → ℕ → LogIndex c f → Port.Test T
  enroll (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P): ∃ k:ℕ, ∀ (L:Side),k≤L.val → ∀ (D:Patch), D.Branches P.bind G→∀ (i l:ℕ)(χ:Chi)(W:ℝ), 0<W→∀ (μ:ℝ), 0<μ→∀ (o:Target.Order G W)(v d : ℝ→ℝ), Rate G L (-(1/2)) v→ (∀ᶠ x in atTop,0≤v x)→ Rate G L (-(1/2)) d→∀ (a b ζ:ℝ), a≤1/2→ -(1/2:ℝ)<b → 0≤ζ→ ∃ f : ℝ→ℝ, Rate G L b f ∧ ∀ᶠ x in atTop, ∀(c f':Side) (S : StepData c f')(T:Tube G S)(R:Rep G f')(C:ℝ)(H:Cash W x μ L Q o C T R), S.patch=D→Stamp T → ∀ r:ℝ, 1≤r → ∃ w, Meter (H:=H) (symbol H l) l ζ r (v x) (d x) (betaF G x L^a) (f x) i χ w

def clips (G:Gauge):Regime G where
  symbol H l := Mesh.part H l
  enroll P Q:=by
    refine ⟨0, fun L _ D _ i l χ W _ μ _ o v d _ _ hd a b ζ ha hb _=> ?_⟩
    obtain ⟨Y,hY,h⟩:= tempo G P Q L d v _ hd (Rate.power (a:=a)) ha o ζ l i χ
    refine ⟨Y,hY.weaken hb.le,?_⟩; filter_upwards [h,Delay.shift_pos G L] with x hp hx c f S T R C H _ _
    exact hp (Real.rpow_pos_of_pos hx _) c f S T μ C R H
lemma classroom (Ξ:Regime G) (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ (m:ℕ) (α:ℝ), α ≤ 1/2→ ∀ (t0 ζ : ℝ),-(1/2:ℝ)<t0 → t0<Q.rate → 0≤ζ →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q D' p' bm: ℝ→ℝ) (k l:ℕ), Rate G L 0 B ∧ Rate G L 0 r ∧ Rate G L t0 bm ∧ Rate G L 0 D' ∧ Rate G L 0 p' ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N : Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) (l+i) χ, LocalBookingsR2 ζ (bm x) N.conduit ∧ StoresR2 H i (v x) (d x) A (D' x) k (p' x) l χ ∧ Crib (Ξ.symbol H m) N.conduit m (betaF G x L^α) := by
  obtain ⟨n,h⟩:= pearls P Q; obtain ⟨n',hn'⟩ := Ξ.enroll P Q; refine ⟨n+n', fun L hL m α hα t0 ζ ht ht' hζ D hD i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,b,u,p,k,l,hd,hr,hbm,hu,he',hF⟩:= h L (by omega : n≤ _) t0 ζ ht ht' hζ D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x := p x*(1+u x+2*r x)^i
  have hB:Rate G L 0 B':=by
    unfold B'; simpa only [zero_mul,zero_add] using! (he'.mul ((((Rate.const (G:=G) (L:=L) 1).add hu).add (hr.mul_left 2)).pow i))
  have hu':= Glass.portal P D L hD i χ hh (hp.mono (fun x hh=> by unfold v; positivity)) o.K o.γ W o.indexPay o.f
  obtain ⟨f',hf',hg⟩:= hn' L (by omega) D hD i m χ W hW μ hm o v d hh (hp.mono fun x hh=>by unfold v; positivity) hd α t0 ζ hα ht hζ
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,u,p,(fun x=>b x+f' x),k,l,hB,hr,hbm.add hf',hu,he',?_⟩
  filter_upwards [hp,hF,hu',(hbm.add hf') Q.rate ht', hg, (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx hm' hu hb hg hG c f S T hS hT R C' H
  obtain ⟨ht1,Xq,hQr,hΞ⟩:= hm' c f S T hS hT R C' H
  obtain ⟨w0, hw⟩:= hg _ _ S T R C' H hS hT _ Xq.active
  obtain ⟨Ξ,hQ,hU⟩:= Mesh.bamboo _ Xq hQr hG hζ (Real.rpow_nonneg (zero_le_one.trans hG) _) hw ((le_abs_self _).trans hb)
  have hw:0≤ B' x:= by unfold B'; have h₁:=Ξ.active; have h₂:=hΞ.fuel; have h₃:=hΞ.sure; positivity
  have hv := H.laws.data
  have hΘ: Oboe H i (v x) (B' x) (l+i) A a Ξ:= ⟨hA,ht1,hΞ.earnings Ξ,fun F X hX hF hh hh'=> hu c f S T hS hv.funds hv.access F X hh hF hX (hv.localP F X hX hh hh')⟩
  exact ⟨⟨Ξ,hΘ,mul_nonneg hZ.le hx.le,hx.le,(by have he:= hv.room.temperatures; rw [hv.funds.length_eq] at he; exact he),
    (by unfold v; positivity),hw, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hQ,hΞ,hU⟩
open Tail Charge Candle Tender AnalyticBridge VerifiedReset Price
structure Charter (Ξ:Regime G) (l j n k : ℕ) (Q : YM.ConnectedActivityE6.Target G P) (L:Side)(μ W s δ:ℝ) (o:Target.Order G W) (χ:Chi)
    (A a C x d v t r B K q ρ b w θ:ℝ) : Prop where
  gates : GateR2 Q L μ s ρ θ K x B r b w δ (l+1:ℝ) j l n
  chooses : ∀ (c f:Side)(S:StepData c f) (T:Tube G S), Stamp T → ∀ (R:RG.Rep G f)(C':ℝ)(H:Cash W s μ L Q o C' T R),
    ∃ N:Captain H j C d v t A a r B q (n+j) χ, LocalBookingsR2 (l+1:ℝ) b N.conduit ∧ StoresR2 H j v d A K k x n χ ∧ Crib (Ξ.symbol H l) N.conduit l ρ
  carry : Carry l j θ
-- Note Gates hδ? consumer since δ from Expense. Criterion ties report-order `u` and `σ`, ζ etc.
def Mailed (Ξ:Regime G) (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(W μ s ε δ u:ℝ)(j σ l:ℕ) (o:Target.Order G W)(χ:Chi):Prop := ∃ A a C x d v t r B K q ρ b w θ n k, Charter Ξ l j n k Q L μ W s δ o χ A a C x d v t r B K q ρ b w θ ∧
    ∀ i : ℕ,i ≤ l+1 → report G j σ δ s w u ρ i ≤ betaF G s L^(requested i ε)
-- For arbitrary request P, only need the purchase in the nonvoid case
-- (the witness of Branches comes from actual H). 

theorem passes (Ξ:Regime G) (P : Teller G) (Q:YM.ConnectedActivityE6.Target G P)(Q':Target.Expense Q) : ∃ n:ℕ,∀ (L:Side), n≤L.val → ∀ W μ (o:Target.Order G W) (h k l:ℕ) (ε u:ℝ) (χ:Chi), 0<W → 0<μ → 0<ε → (∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j) →
    ∀ᶠ x in atTop, Mailed Ξ Q L W μ x ε (Q'.one/2) u h k l o χ:=by
  obtain ⟨N,H⟩:= Mesh.classroom Ξ P Q
  refine ⟨N,fun L hp W μ o j σ l ε U χ hW hμ hε he=>?_⟩
  obtain ⟨D,hd,hL,hJ⟩:= he
  obtain ⟨Θ,hθ,hΘ⟩:=carries l j
  obtain ⟨e,hp',he,h⟩:= plan l ε hε
  have hR: -(1/2:ℝ)< min Q.rate (-e) := lt_min Q.start (by linarith)
  obtain ⟨r,hr,heL⟩:= exists_between hR; obtain ⟨hS,hE⟩:= lt_min_iff.mp heL
  let ζ:= (l+1:ℝ)
  have hζ:1 ≤ ζ := by unfold ζ; linarith [Nat.cast_nonneg (α:=ℝ) l]
  obtain ⟨A,a,C,d,v,t,K,B,q,D',p,b,k,n,hB,hK,hb,hD,hP,hF⟩:= H L hp l e he.le r ζ hr hS (zero_le_one.trans hζ) D hd j χ W hW μ hμ o
  let ρ x:=betaF G x L^e
  let u:=max Q.rate (e+r); have hu:u<0:=max_lt Q.stop (by linarith)
  obtain ⟨u',hh,h'⟩:= exists_between hu; let w x:=betaF G x L^u'
  have hI:= (incline (θ:=Θ) ρ l (show Rate G L e ρ from Rate.power) hb hμ (le_max_right ..) (le_max_left Q.rate (e+r)))
  have ht:=tangent (θ:=Θ) D' B b p K ρ l n j (show Rate G L e ρ from Rate.power) hb hμ (le_max_right ..) (le_max_left Q.rate (e+r)) hD hB hP hK
  let δ:=Q'.one/2
  have hm:= meters (t:=u') w Rate.power δ
  have hv (i:Fin (l+2)):= height (L:=L) G i j σ U e δ u' (requested i ε) (lt_trans (add_lt_of_neg_right _ h') (h i (Nat.le_of_lt_succ i.isLt))) 
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,marked (L:=L) Q hμ ζ,(meters _ hI Q.δ).below hu (1/2) (by norm_num),((Rate.power (a:=e)).mul hb).below (by linarith) 1 zero_lt_one,
    ht u' hh, hm.below h' (1/2) (by norm_num),eventually_all.mpr hv, hF] with x hx hpz hx' he' hv' hw hi hXX
  have hX:1≤ρ x:= Real.one_le_rpow hx hp'.le; have hw':0<w x:= Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
  have hg : ρ x ^ (l+1) ≤ betaF G x L^ζ:= by
    rw [show ρ x ^(l+1)=_ from (Real.rpow_mul_natCast (zero_le_one.trans hx) e (l+1)).symm]; apply Real.rpow_le_rpow_of_exponent_le hx; have hh : ((l+1:ℕ):ℝ)=ζ:=by unfold ζ; push_cast; rfl 
    rw [hh]; exact mul_le_of_le_one_left (zero_le_one.trans hζ) (by linarith)
  exact ⟨A,a,C,p x,d x,v x,t x,K x,B x,D' x,q x,ρ x,b x,w x,Θ,n,k,⟨⟨hx,hX,hθ,(zero_le_one.trans hζ),hΘ.1,(le_abs_self _).trans he',hg,hpz,(le_abs_self _).trans hx',(le_abs_self _).trans hv',(le_abs_self _).trans hw,hw'⟩,fun _ _ S T hT R C H=> hXX _ _ S T ((H.laws.data.funds).patch hL hJ) hT R C H,hΘ⟩, fun i h=> (le_abs_self _).trans (hi ⟨i,Nat.lt_succ_of_le h⟩)⟩
end Mesh
end YM.LocalTaylorR2
