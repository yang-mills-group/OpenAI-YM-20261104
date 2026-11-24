import YM.Frontier.Tuning.TwoMotion
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Horns
/-! One support-list angular receipt. Imports old invoices but hatted spreads and all Board
parameters fixed before real parts and normalized E/K direction rows. τ is an auxiliary width;
one of R,I MAY be reset at every τ for the estimate (no variation of represented addresses). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.AngularReceipt
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option maxHeartbeats 1200000
-- C' largest fixed packet bill, α plume price; v q two Mode/Clutch widths, γ coefficient for Complex exponential in earned Direction cost, B optional speed
structure Pocket (H: Cash W s μ L Q o H0 T R) (A:Rep G f) (j:ℕ)(v q C' α B γ : ℝ) (χ:Chi) where
 strong : 1 ≤ γ
 exp_cost : ∀ z, Brush j (γ * ‖Complex.exp z‖) 1 Complex.exp z
 wide : 1 ≤ B
 kCost : ℕ → ℝ
 logCost : LogIndex c f→ℝ
 rad : ℝ
 awake : 0≤rad
 stamp : Stamp T
 lives : (Q.costs L μ (b₁/2) s C').Buy S.patch.L Q.halo M₀
 accounts : Mixed.Accounts S Q.halo M₀ (Q.costs L μ (b₁/2) s C') H.birth (rates kCost logCost ((topStorm S.patch+1)*rad)) (lengths T R)
    (steamP S (Q.costs L μ (b₁/2) s C'))
 blanks : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio)(X:Coat T F)
   (U:E→ Config G c)(u:E→ Directions G f)(g:E → Air f G)(y:E)(m:Air f G),X.x=s → X.width=o.K → X.χ=χ → X.manifest → Mode U y j v → Clutch X m o.a R.beta q y j U u g → ∀ (k:Finset ℕ) (Z:Stores S), Healthy (Pressure.temp s) (Z.dome (Q.halo*M₀)) X.V → 1≤Z.shares →
    Brush j (steamP S (Q.costs L μ (b₁/2) s C') Z) 1 (fun i=>Polar.stock (vary X (U i)) o.a R W Q.table (u i) (X.input (Vine.worldZ X R.beta m)) k Z) y
 impulses: ∀ (τ:ℂ)(e k':Payload G f),R.beta=τ.re → ‖τ/R.beta‖≤3→ fans R A (grow G L s) e k' → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio)(X:Coat T F)
   (U:E→ Config G c)(u:E→ Directions G f)(g:E → Air f G)(y:E)(m:Air f G),X.x=s → X.width=o.K → X.χ=χ → X.manifest → Mode U y j v → Clutch X m o.a R.beta q y j U u g →
   (∀ i k, Brush j (rates kCost logCost (topStorm S.patch+1) i) (B*twigs R T M₀ Q.halo i) (fun z=> Held.emberC (vary X (U z)) R (X.input (Vine.worldZ X R.beta m)) (u z) (g z) Q.table o.a W k τ Q.halo e k' (.inr i)) y) ∧
   ∀ (Z : Stores S), (¬ (fun i=> X.enforce o.a (u i) (X.plaza (Z.dome (304*X.B))))=ᶠ[𝓝 y] fun _=>0) →
     Brush j (phaseCost τ X Z) (phaseSpeed τ j γ α Z) (fun z=>penGain (vary X (U z)) R (X.input (Vine.worldZ X R.beta m)) (u z) Q.table τ Z) y
 ship : ∀ (F:Forest S.ratio)(X:Coat T F), X.x=s→ X.width=o.K → X.χ=χ → X.manifest → ∀ i,
      X.dice.real (X.catastrophe (o.ξ/2) R.beta i) ≤ (rad^2)^i.card

lemma launch (Q : ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C' Y:ℝ) (r Ω:ℝ→ℝ), 1≤Y ∧ 0≤C' ∧ Rate G L 0 r ∧ Rate G L 1 Ω ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R A:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R), Facing R A→Intake P T x A→ Nonempty (Pocket H A i (v x) (w x) C' (Ω x) (r x) Y χ) := by
  obtain ⟨t,h₁,h₂⟩:= exists_between Q.start
  obtain ⟨n,hn⟩:=Clutch.strongRush P Q h₁ (h₂.trans Q.stop)
  have hp:0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  refine ⟨n,fun L hL D hd i χ W hw μ hm o v w hv hwV hW=>?_⟩
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hJ,hv',h⟩:= hn L hL D hd i χ W o v w hv hwV hW
  obtain ⟨A,hA,hy,hQ⟩:=Clutch.ash G L χ i hW hv W o.a Q.halo (by have h:=Q.buys; omega)
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (2*t-1) (half_pos o.rare)
  let g x:= betaF G x L^t; let Z x:= B x+A x; have hZ x:1≤Z x:= (hv' x).trans (le_add_of_nonneg_right (hy x))
  let u := Coat.topStorm D+1; have hu : 0 ≤ u := by unfold u; linarith [topStorm_one D]
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε t u hp g Rate.power
  obtain ⟨ε,hε,hD⟩:=ComplexBrush.exp_cost i
  let p : ℝ := 2+i.factorial*(ε*Real.exp 1+1)
  have hP:= ComplexBrush.exp_small i hD (zero_le_one.trans hε)
  obtain ⟨Ω,hΩ,hΘ⟩:=ClockShift.upload P L D hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW o.indexPay o.f
  have hr : Rate G L t (fun x=> J x+J x+(3*p*(J x+J x)+b x)) := (hJ.add hJ).add (((hJ.add hJ).mul_left (3*p)).add hb)
  refine ⟨C,ε,Z,Ω,hε,hC,hB.add hA,hΩ,?_⟩
  filter_upwards [hΨ,h,hQ,hF,hΘ,Q.pay_for L hm hC,hY (2*t) (by linarith),hr Q.rate h₂,(hJ.mul_left 6).below (h₂.trans Q.stop) 1 zero_lt_one,(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hΨ h hQ he hΘ hV hA hr hSmall hG c f S T hS hF R I C' H hM hI
  -- hS conflict: hS smallness in context reused shadows; rename.
  have hΓ:= H.laws.data; have hh:= H.laws.intake
  have hΘ': 0<betaF G x L:=by have he:=hh.height; rw [hΓ.funds.length_eq] at he; linarith
  have hg:0≤g x:= by unfold g; positivity
  have h' := (hΓ.localP)
  obtain ⟨k₁,y₁,H₁⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access R hh
  obtain ⟨k₂,y₂,H₂⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access I hI
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu hg)
  have hg':1 ≤ grow G L x:= Real.one_le_rpow hG (by norm_num)
  obtain ⟨⟨hx,hφ⟩,hφ'⟩:= ticket_prices hM H₁ H₂ p hP.1 hg' ((le_abs_self _).trans hSmall)
  let k:=ticketK (grow G L x) k₁ k₂; let y:=ticketL (grow G L x) p y₁ y₂
  let costs:=Q.costs L μ (betaF G x L/2) x C
  have hV' : costs.Buy S.patch.L Q.halo (radiusB x):=hΓ.funds.length_eq ▸ hV _ Set.left_mem_Ici
  have hr': Mixed.Accounts S Q.halo (radiusB x) costs H.birth (rates k y (u*g x)) (lengths T R) (steamP S costs) := by
     have h := (ratesCombine hφ hx hΞ).raise ((le_abs_self _).trans hr)
     exact ⟨fun i _=> ⟨mul_nonneg hV'.capture (Real.exp_pos _).le,le_rfl⟩,h.nonneg,fun _=>Nat.cast_nonneg _, h.hit⟩
  refine ⟨⟨hε,hD,hZ _,k,y,g x,hg,hF,hV',by rw [show S.patch=D from hS]; exact hr',?_,?_,?_⟩⟩
  · intro E _ _ _ F X U f' v' a' w he hK hχ hc hm hτ m' m hm' hu
    have he' :=hΨ _ _ S T hS hΓ.funds hΓ.access hΓ.grant _ a' U F X R f' w v' he hχ hK (h' F X he hK hc) hm hh hτ m _ m' Q.buys hu (by rw [he,show X.B=_ from congr_arg radiusB he];exact hm')
    have hx : X.t= Pressure.fiery G x L := by rw [Coat.t,he,hΓ.funds.length_eq]
    have hh1: betaF G x L/2≤R.beta:= hΓ.funds.length_eq ▸ hh.window.1
    apply he'.climb _ le_rfl
    change Packets.income _ _ (R.beta*(μ*X.t^2)) m.shares ≤ steamP S costs m
    unfold steamP costs Target.costs Buy.quote Packets.income
    dsimp only; unfold Grant.credit; rw [hx]; gcongr
  · intro τ e k' hτ hI' hc E _ _ _ F X U u g y m hX hK hχ hMx hm he'
    have HF kVal:=pair_cap (X:=X) (Z:=grow G L x) (s:=B x) (q:=w x) (v:=v x) hM hg' (by rw [hX,hχ]; exact H₁) (by rw [hX,hχ];exact H₂) ((le_abs_self _).trans hSmall)
      hc p hP.2 hP.1 (hv' _) hI' kVal U u g hm he' hMx hK
    -- takes k explicit; use polymorphic have HF k
    have hpos (i') (h:0 ≤ i') : B x*i' ≤ Z x*i' := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hy x)) h
    change X.x=x at hX
    rw [← congr_arg radiusB hX]
    refine ⟨?_H,fun m' h => phaseCap X _ hD (zero_le_one.trans hε) (by rw [hX,hK,hχ]; exact hΘ _ _ S T hS hΓ.funds h' hΓ.access) hτ (hτ ▸ hh.positive) U u m g _ Q.table_exists.scale hMx hm (by rw [hX]; exact hh) he' h⟩
    case _H=> rintro (i'|i'|i') k
              all_goals let z i'':= twigs R T X.B Q.halo i''; have ht i'':0 ≤ z i'' := add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              · exact ((HF k).1 i').climb le_rfl (hpos (z _) (ht _))
              · exact ((HF k).2 i').climb le_rfl (hpos (z _) (ht _))
              have hd:=hQ c f S T F X R hX hχ hΓ.funds.length_eq (by unfold Coat.t; rw [hX,hΓ.funds.length_eq]; exact mul_pos hw (show 0<Pressure.fiery G x L from Work.E09.temp_pos hΘ'))
                    E _ y U u g he' hm i' k (X.input (Vine.worldZ X R.beta m))
              change Brush i _ (Z x * _) (fun a=> (_ :ℂ)) y
              apply (ComplexBrush.cast hd).climb le_rfl _
              change _*(1+(_ : ℝ)) ≤ _ * (1+(_+ (_ :ℕ) : ℝ))
              exact mul_le_mul (le_add_of_nonneg_left (zero_le_one.trans (hv' x))) (add_le_add_right (le_add_of_nonneg_right (Nat.cast_nonneg _)) _) (add_nonneg zero_le_one (Nat.cast_nonneg _)) (zero_le_one.trans (hZ x))
  intro F X ht hK _ hp K
  have hV' : betaF G x L^(2*t)=g x^2 := by unfold g; rw [mul_comm, Real.rpow_mul hΘ'.le, Real.rpow_two]
  exact (he.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hK hp).sails R (ht.symm ▸ hh) K).trans
    (pow_le_pow_left₀ he.1 (((le_abs_self _).trans hA).trans_eq (by rw [← hV'])) _)
end YM.Frontier.Tuning.AngularReceipt
