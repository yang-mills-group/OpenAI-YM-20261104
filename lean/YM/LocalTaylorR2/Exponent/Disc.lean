import YM.LocalTaylorR2.Exponent.Pantry
import YM.LocalTaylorR2.Copper.Mingle
import YM.LocalTaylorR2.Marker.Steno

/-!
 # Knight.Purchasing Hart. Common captain on arbitrary μ. Includes associated III crew. Up-post apartment B.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open PhysicalNext.Repeat Mesh Marker
structure Wealth (Ξ:Observatory G) (H:Cash W s μ L Q o C T R)(K:ℝ)(l:ℕ)(p:ℝ)(j' n:ℕ){i :ℕ}{v d r C':ℝ}(U:Utopia H i v d r C' χ)(m:ℕ)(ρ:ℝ): Prop where
    stuff : ∀ k:LogIndex c f, Port.Burst H (H.supportP (identityLog k)) (Ξ.upgrade H m k)
    invests : ∀ t:Reel.Strand, Lodestar H n K U (replay (weightLog H) (Ξ.upgrade H m) (Reel.Strand.dial t*ρ^m))
    bank : Bank H i j' l p m n K
    positively : 1 ≤ K
open Mesh Marker
lemma knight (Ξ:Observatory G) (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ (m:ℕ) (α:ℝ), α ≤ 1/2→ ∀ (t0 ζ : ℝ),-(1/2:ℝ)<t0 → t0<Q.rate → 0≤ζ →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q D' p' bm Y₀ X0: ℝ→ℝ) (k l j:ℕ), Rate G L 0 B ∧ Rate G L 0 r ∧ Rate G L t0 bm ∧ Rate G L 0 D' ∧ Rate G L 0 p' ∧ Rate G L 0 Y₀ ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N : Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) (l+i) χ, LocalBookingsR2 ζ (bm x) N.conduit ∧ StoresR2 H i (v x) (d x) A (D' x) k (p' x) l χ ∧ Crib (Ξ.symbol H m) N.conduit m (betaF G x L^α) ∧ Daisy.Herd H N.conduit A (B x) (l+i) ∧ Marker.Tinted G x (Y₀ x) (d x) o.a L χ i ∧ Wealth Ξ H (X0 x) l (p' x) k j N.conduit m (betaF G x L^α) := by
  obtain ⟨n,h⟩:= pearls P Q; obtain ⟨n',hn'⟩ := Ξ.enroll P Q; obtain ⟨j,hj⟩:=Ξ.evolve P Q; refine ⟨n+n'+j, fun L hL m α hα t0 ζ ht ht' hζ D hD i χ W hW μ hm o=>?_⟩
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,b,u,p,k,l,hd,hr,hbm,hu,he',hF⟩:= h L (by omega : n ≤ _) t0 ζ ht ht' hζ D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  obtain ⟨Y,hY,hτ⟩:= Marker.tinted (j:=i) (χ:=χ) d hd o.a
  have hu':= Glass.portal P D L hD i χ hh (hp.mono (fun x hh=> by unfold v; positivity)) o.K o.γ W o.indexPay o.f
  obtain ⟨f',hf',hg⟩:= hn' L (by omega) D hD i m χ W hW μ hm o v d hh (hp.mono fun x hh=>by unfold v; positivity) hd α t0 ζ hα ht hζ
  obtain ⟨Ω,Q',t',j,hΩ,hQ',hΔ⟩:= hj L (by omega) D hD m i χ W o ζ t0 ht v d hh hd (hp.mono (fun x hh=> by unfold v; positivity))
  let e := max (0:ℝ) (α * m+t')
  let Ψ x:=1+(betaF G x L^α)^m * |Ω x|
  have hv : Rate G L e Ψ:= by
    unfold Ψ; exact ((Rate.const _).weaken (le_max_left ..)).add ((((Rate.power (a:=α)).pow m).mul (hΩ.compare (Eventually.of_forall fun x=>(abs_abs _).le))).weaken (le_max_right ..))
  obtain ⟨n₀,X,hX,h₁,h₂⟩:= Debit P Q L o m i k j e Ψ hv
  let p₀ x:=p x+X x; let v₀:= l+n₀
  let B' x := p₀ x*(1+u x+2*(r x+Y x))^i
  have hB:Rate G L 0 B':=by
    unfold B'; simpa only [zero_mul,zero_add] using! ((he'.add hX).mul ((((Rate.const (G:=G) (L:=L) 1).add hu).add ((hr.add hY).mul_left 2)).pow i))
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,u,p₀,(fun x=>b x+(f' x+Q' x)),Y,Ψ,k,v₀,j,hB,hr,hbm.add (hf'.add hQ'),hu,he'.add hX,hY,?_⟩
  filter_upwards [hp,hF,hu',(hbm.add (hf'.add hQ')) Q.rate ht', hg,hτ,h₂,hΔ, (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx hm' hu hb hg hτ h₂ hΔ hG c f S T hS hT R C' H
  obtain ⟨ht1,Xq,hQr,hΞ⟩:= hm' c f S T hS hT R C' H
  obtain ⟨w0, hw⟩:= hg _ _ S T R C' H hS hT _ Xq.active
  have he:0<betaF G x L^α:=Real.rpow_pos_of_pos (zero_lt_one.trans_le hG) _
  obtain ⟨Ξ',hQ,hU,hΔ',hv₀⟩:= Exponent.negotiations Xq hQr hG hζ hw (hΔ c f S T R μ C' H hS hT hw.keptP) ((le_abs_self _).trans hb) he (abs_nonneg _)
  have hΞ:= storageUp hΞ (show l≤v₀ from Nat.le_add_right l _) (show p x≤ p₀ x from le_add_of_nonneg_right (h₁ x))
  have hl:1≤Ψ x:= le_add_of_nonneg_right (mul_nonneg (pow_nonneg he.le _) (abs_nonneg _)); have hz:= h₂ c f S T R μ C' H; rw [abs_of_nonneg (zero_le_one.trans hl)] at hz
  have hF:Bank H i k v₀ (p₀ x) m j (Ψ x):= hz.raise (Nat.le_add_left n₀ l) (by unfold p₀; linarith only [‹StoresR2 H i (v x) (d x) A (u x) k (p x) l χ›.sure]) (h₁ _)
  have hw:0≤ B' x:= by unfold B'; have h₁:=Ξ'.active; have h₂:=hΞ.fuel; have h₃:=hΞ.sure;have h₄:=hτ.salt; positivity
  have hU':= Marker.herded H (Ξ:=Ξ') hτ hΞ le_rfl
  have hv := H.laws.data
  have hΘ: Oboe H i (v x) (B' x) (v₀+i) A a Ξ':= ⟨hA,ht1,hU'.unmarked,fun F X hX hF hh hh'=> hu c f S T hS hv.funds hv.access F X hh hF hX (hv.localP F X hX hh hh')⟩
  exact ⟨⟨Ξ',hΘ,mul_nonneg hZ.le hx.le,hx.le,(by have he:= hv.room.temperatures; rw [hv.funds.length_eq] at he; exact he),
    (by unfold v; positivity),hw, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hQ,hΞ,hU,hU',hτ,hΔ',hv₀,hF,hl⟩

end YM.LocalTaylorR2.Exponent
