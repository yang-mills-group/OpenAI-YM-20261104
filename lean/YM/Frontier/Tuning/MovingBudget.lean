import YM.Frontier.Tuning.VectorTilt
/-! Launching the priced sheets before period/cutoff and unifying reference worlds.
NOT claiming the receipt closes the analytic push estimate until equality, dominated C^j
integration, regular/forced assembly, and flow smallness have been established separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.MovingBudget
open VectorTilt
open TiltTogether Footage YM.Frontier.Tuning.Voice HeldBurst DensityTilt
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Eider Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt Flux Shield Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option quotPrecheck false
set_option maxHeartbeats 2000000

variable {H: Cash W s μ L Q o H0 T R}
variable {C' : ℝ}
variable (P' : Pocket H A j v q C α d γ χ)



open Reserves
structure Motion (H : Cash W s μ L Q o H0 T R) (A:Rep G f) (j:ℕ)(v q C CE d γ : ℝ) (χ:Chi) (D K D' K' F' : ℝ) (k κ l : ℕ) extends Pocket H A j v q C CE d γ χ where
  morphism : Canary G K K'
  weight : 8*o.a*Pressure.fiery G s L ≤ K/2
  walk : WalkBound H F' l ((κ+k)*j*2)

  travels :∀ (F:Forest S.ratio)(X:Coat T F),X.x=s → X.width=o.K → X.χ=χ→X.manifest→ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→ Config G c)(y:E), U y=X.V→ Mode U y j v→
    Glass P X U y j W ∧ ∀ (z:Air f G),
    (Clutch X z o.a R.beta q y j U (fun i=> steer X K (worldZ X R.beta z) (U i)) (fun i=>course X K R.beta z (U i))) ∧
    ∀ J, Brush j 1 (|D| * facescale J z^κ) (fun y'=> Flux.scalp J X (U y') R.beta K z) y ∧ Brush j (|D'| * facescale J z^k) 1 (fun y'=> PhysicalNext.Repeat.Alabaster.draftI X J R.beta K (U y') z) y
namespace Motion
variable {CE K K' D D' F':ℝ}{κ k₁ l:ℕ}
universe u
variable {M : Motion H A j v q C CE d γ χ D K D' K' F' k₁ κ l}
-- unmultiplied held transform on the steering motion
variable (I : Finset (Bond f))
def anchoredWord (K : ℝ) (X : Coat T F) (V:E→ Config G c) (p:Molecule S)(H:Cash W s μ L Q o H0 T R)(τ:ℂ)(e h : Payload G f)(z:E)(y:F.Slice G × Air f G):=
  let X':=X.wrapY y.1; skewIntegral X' K W R V (fun i=> steer X' K (worldZ X' R.beta y.2) (V i)) (fun i=>course X' K R.beta y.2 (V i)) z y.2 I Q o.a p τ e h
omit I
lemma held_bound (M : Motion H A j v q C CE d γ χ D K D' K' F' k₁ κ l)(V:E→ Config G c)(y:E) (X:Coat T F){τ:ℂ}(e f':Payload G f)(hV:V y=X.V)(hz: Mode V y j v)(hθ:Voice.strainG G L s * Real.log (‖τ‖/τ.re) ≤ Q.ε)(hr : R.beta=τ.re)(hτ:‖τ/R.beta‖≤3)(hg:fans R A (grow G L s) e f')
  (hχ:X.χ=χ)(hx:X.x=s)(hk:X.width=o.K)(hp:X.manifest)(p:Molecule S)(he:Ac.Spark H.supportP p)(ht :troupe T R Q.halo M₀ p)(hH:Healthy (Pressure.temp s) (H.unionP p) X.V):
  let I:=edgesM S (H.unionP p) M₀; let g:=anchoredWord I K X V p H τ e f'
  let w(z : F.Slice G × Air f G):=envelope M.toPocket D' D k₁ κ τ p (X.wrapY z.1) I z.2
  let θ:=(1+coefficient M.toPocket D' D τ)^j
  let m:=(F.order G).prod X.dice
  Integrable w m ∧ (∫ t,w t ∂m) ≤ ((1+|F'|)*θ)*heated M.toPocket (l+j) p ∧ ∀ z, Brush j (w z) 1 (fun i=>g i z) y:=by
 intro I g w θ m
 obtain ⟨hhInt,hv⟩:=integrablePrice M.toPocket X hx hp hk hχ k₁ κ D' D p he ht τ M.walk
 refine ⟨hhInt,hv,?_⟩; intro z
 let Y : Coat T F:=X.wrapY z.1
 obtain ⟨clth,hZ⟩:= (M.travels F Y hx hk hχ hp E V y hV hz).2 z.2
 exact simultaneous M.toPocket _ _ _ hg hr hτ hθ Y p ht hx hk hχ hp hH K V _ _ _ y hz clth _ _ _ _ M.exp_cost (hZ I).1 (hZ I).2
end Motion

lemma launch (Q : ConnectedActivityE6.Target G P): ∃ n:ℕ,∀ (L:Side),n≤L.val→∀ (D:Patch),D.Branches P.bind G →∀ (j:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (K K':ℝ), Canary G K K' → ∀ (V:ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C γ:ℝ) (q CE d B B' F':ℝ → ℝ) (k κ l : ℕ), Rate G L (-(1/2)) q ∧ Rate G L 1 CE ∧ 0≤γ ∧ Rate G L 0 d ∧ Rate G L 0 B ∧ Rate G L 0 B' ∧ Rate G L 0 F' ∧
    ∀ᶠ x in atTop,∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → Stamp T →∀ (R A:Rep G f)(C₀:ℝ)(H:Cash W x μ L Q o C₀ T R), Facing R A→Intake P T x A →
      Nonempty (Motion H A j (V x) (q x) C (CE x) (d x) γ χ (B x) K (B' x) K' (F' x) k κ l) := by
  obtain ⟨n,hN⟩:=AngularReceipt.launch Q
  refine ⟨n,fun L hL D hD j χ W hW μ hm o K K' hK V hv hV'=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hK P L j χ hv
  let B' x:= |B x|
  have hb:= hB.compare (v:=B') (Eventually.of_forall fun x=> (abs_abs _).le)
  obtain ⟨C,Y,d,Ω, hY,hC,hd,hΩ,hP⟩:=hN L hL D hD j χ W hW μ hm o V B' hv hV' hb
  obtain ⟨k,U,hU,hΓ⟩:= Flux.rump P L D hD o.K o.γ W o.a χ j hv hB hV' hZ o.indexPay o.f K
  obtain ⟨l,U',hU',hΓ'⟩:= MarginalPrice.drafts P L D hD o.K o.γ W o.a χ j hv hB hV' o.indexPay o.f K
  obtain ⟨F',k',hF',hΨ⟩:= Flux.walksW G L (payE o.eta o.gap o.ample (tubularPrice G L)) ((k+l)*j*2)
  have he:= Glass.portal P D L hD j χ hv hV' o.K o.γ W o.indexPay o.f
  refine ⟨C,Y,B',Ω,d,U,U',F',l,k,k',hb,hΩ,zero_le_one.trans hY,hd,hU,hU',hF',?_⟩
  filter_upwards [hX,hP,hΓ,hΓ',((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hK.warm),he] with x hx hQ hΓ hΓ' hA hE c f S T hS he' R A C₀ H hM hf
  obtain ⟨N⟩:= hQ c f S T hS he' R A C₀ H hM hf
  have hg:= H.laws.data; have ht:=hg.localP; have hW:=hg.funds
  refine ⟨{ N with morphism := hK, weight := (le_abs_self _).trans hA, walk := hΨ x, travels := ?_ }⟩
  intro F X hX hJ hχ hM E _ _ _ U y hX' hY
  have hγ := hE c f S T hS hW hg.access F X hJ hχ hX (ht F X hX hJ hM) E U y hX' hY
  refine ⟨hγ,fun z=>?_⟩
  have p:= H.laws.intake
  obtain ⟨hw,hA'⟩:= hx _ _ S T F X hX hW hχ R.beta p.positive z E U y hX' hY
  have hA := hA' o.a (mul_pos o.large ((ht _ _ hX hJ hM).sails.room.fiery)) (show 8*o.a*X.t≤_ from by unfold Coat.t; rw [hX,hW.length_eq]; exact (le_abs_self _).trans hA)
  exact ⟨hA,fun I=> ⟨hΓ _ _ S T hW hS hg.access E y U F X _ _ hX hJ hχ (ht _ _ hX hJ hM) p hY hA hw I,hΓ' _ _ S T hW hS hg.access E y U F X _ _ hX hJ hχ (ht _ _ hX hJ hM) p hY hA I⟩⟩
end YM.Frontier.Tuning.MovingBudget
