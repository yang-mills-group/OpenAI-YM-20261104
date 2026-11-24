import YM.RG01Estimate.Yonder
/-!
 # Aux → main Mask Price. Keeps same Loom labels. kinetic δ still carried in income
 expectation. Don't assume Deck entries without their real masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Precise
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard Award
open Evoc Deck AbsoluteSums.Animals Board Promise Slide Trio Abacus
open Progress.DirectedRecipe Next.Scheduling
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{U:Alloy X D}(R:Factor U)
   {c f:Side}{N m d n i j r ℓ e :ℕ} {Y:Type} (β:ℝ) (H : f.val=c.val*(U.B.a.S.block m).val)
   (V : Insured U N m d H β Y)
local notation "J" => U.B.a.clock.J (m+1)
local notation "I" => U.B.a.clock.J m
local notation "P" => U.B.a.clock.adm (m+1)
local notation "L" => D.L (U.B.a.clock.J (m+1))
local notation "B" => U.B.a.budget m
local notation "B'" => U.B.a.budget (m+1)
local notation "χ" => Chi.canonical
local notation "γ" => U.B.kin.alpha N m
local notation "x" => U.B.a.clock.hatBeta m
local notation "𝕊" => Pane.panel U m H
local notation "T" => Pane.orchestra U N H
local notation "A₀" => X.O
local notation "X₀" => (R.target (U.B.a.clock.J (m+1)) (U.B.a.clock.J m))
local notation "ε" => gStep β
local notation "B''"=> Meadow.studio ℓ (radiusB x)
local notation "n₀" => (Trio.tent ℓ (radiusB x))
local notation "z" => Trio.base ℓ (radiusB x)
local notation "D''" => 2*Trio.base ℓ (radiusB x)
local notation "C₀" => Precise.shape U m ℓ
local notation "η₀" => Trio.coverTicket ℓ
local notation "qt" => gStep β^(r+1)
local notation "Q'" => (Time.forecastK U.B.a m R.scout β)
variable (u₀ : Precise.Horizon X D (U.B.a.clock.J (m+1)) (U.B.a.clock.J m) ℓ r n (U.B.a.clock.adm (m+1)))
   {s a b h :ℝ→ℝ}(F₀: Folio D (U.B.a.clock.adm (m+1)) u₀ e s a b h)
local notation "Ε" => u₀.Y (U.B.a.clock.hatBeta m)
local notation "fQ" => wick G L u₀.y x
local notation "k''" => Precise.sideFee D R.shape I J x
local notation "k₀" => (Precise.sideFee D R.shape I J x + Precise.tiny G L x)
local notation "γ₀" => Precise.wage D P u₀ F₀ x
variable (hA : OpenAt D R.shape (U.B.a.clock.adm (m+1)) u₀ F₀ (R.scout (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) (U.B.a.clock.hatBeta m))
    (ht : m < N)(he:β ∈ Shoot.band U.B.a (m+1))

section work
variable (A: Chartlet R.shape U N m H V.rep) (hF:SeekR R.shape U N m H A) (M:Leads G c)
   (p': Herder β H V u₀ M s a b h e)
   {f':ℕ→ Config G c→ℝ} {h₁ d₁ : ℝ}
set_option quotPrecheck false
local notation "I₀" => (Beam.marquee A B)
local notation "Z₀"=> (Match.staple (H:=A) («J»:=A) rfl rfl rfl)
local notation "f''" => (Song.plusone A Z₀ χ γ)
local notation "A'" => (Caddy.stores (I₀) M.listing.reg)
local notation "S'" => (Caddy.posted f'')
local notation "y" => Caddy.righty M.trunk

variable (UQ : ℕ→Finset Y) (k:ℕ)


lemma levy_erh : Precise.sideFee D R.shape I J x= turnFee B*(betaF G x L ^ (R.expense (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)).wanting + betaF G x L ^ (-(7/16):ℝ)) := by
   unfold sideFee Height.away turnFee; congr 2; exact congr_arg RG.Stage.order (params_eq U.B.valid m).symm; exact congr_arg RG.Stage.power (params_eq U.B.valid m).symm
include hA ht he A p' UQ k hF
set_option maxHeartbeats 500000 in
lemma builds (f':ℕ→ Config G c→ℝ)(hq: Meadow.Budget (B) (I₀).reg ((f'').logRead - f') (h₁+Routed.spill (A:=U) m r + qt))
     (hD: Meadow.Budget (B) (I₀).reg f' k'')(L₀: Abacus.Rack (I₀) B'' f')(hz : ∀ s' t',Nonempty (((I₀).read (revise f'' ((f'').logRead-f'))).Moves s' t'))
     (hL₀ : L₀.polygon=Evoc.aspect A V.music (Fate.steps r) χ γ (UQ k) k)
     (hΨ:2*z<c.val) (hν:4* B''+16≤c.val) (F : Forest (𝕊).ratio)
     (t : ∀ i:Stars, Award.Position (G:=G) (B) x Ε β γ fQ (Precise.shape U m ℓ i) L B'' (r+1))
     (hC : Trio.CompatibleP (B) (B'') (Evoc.aspect A V.music (Fate.steps r) χ γ (UQ k) k - (p').statusP.polygon) (fun i=> (t i).pact.polygon))
     (hp:∀ i, (t i).q' ≤ qt * Precise.pot h x ∧ (t i).e'≤ k₀ ∧ (t i).y'≤F₀.mist x ∧ (t i).μ ≤ ε^((r+1)+2)*b x∧(t i).V = capΨ D P u₀ a x):
     let U':= (Caddy.signedR (I₀) L₀ p'.statusP)
     let X:= (Marlin.lodge A' z D'')
     let V':= Caddy.insertP (-(M.trunk-M.pioneers)) ((f'').logRead-f')
     let f':= Marlin.bison (revise S' (Caddy.righty M.trunk+V')) ((Trio.ornament (Precise.shape_ack U m ℓ) (fun i:Stars=> (t i).pact.polygon)): Trio.Offer G c) (U'.gap B (fun i=> (t i).pact.polygon) (Precise.shape_ack U m ℓ) z)
     let Z:= Marlin.pluck (B) X
     let D₁:= Marlin.poursP (B) X f'
     let U₁:= fun i:ℕ=> Abacus.tariff i (Caddy.righty M.trunk) 0
     (∀ Z':Config G c,(𝕊).push β V.rep.eval Z'= earlyValue Z (T).down (T).low B D₁ β ((Song.weighty A χ F) - U'.polygon 0 1) γ Z') ∧
       ∃ δ': ℕ→ Config G c→ℝ,D₁.logRead=U₁+δ' ∧ Collection.Local Z (B) (revise D₁ U₁) M.bill Q' ∧ Collection.Local Z (B) (revise D₁ δ') (h₁+qt*γ₀) (Q') ∧ Collection.Local Z (B) D₁ (M.bill+(h₁+qt*γ₀)) (Q') := by
   intro X' D' VΩ f₁ Z D₁ U₁
   obtain ⟨h',V'₀⟩:= Board.hammock R ht H he (A.laws.data.room.buys)
   obtain ⟨hx,hV,hh,hβ,hw'⟩:= authentication R H β he h'
   obtain ⟨hW,hO,hU,hQ,hZ,he',hs⟩:= hA.fare β hh hβ
   have hr:=Board.all_pay R ht H A hF Z₀
   let G':=p'.real_h
   obtain ⟨ht',hA',hB',hQ'⟩ := Caddy.shelf B I₀ M.listing f'' M.trunk f' M.pioneers hq G'.live G'.asking G'.extra hD
   have hW': X'.polygon=Evoc.aspect A V.music (Fate.steps r) χ γ (UQ k) k - p'.statusP.polygon:= by unfold X'; rw [Caddy.pacts,hL₀]
   have hm:= Caddy.symmetry B I₀ M.listing f'' M.trunk f' M.pioneers hr hz (fun s i=> (G'.mirror s i).1) (fun s i=> (G'.mirror s i).2.2) (fun s i=> (G'.mirror s i).2.1)
   have hρ: (B).supportExponent=(X.p.profile (I)).supportExponent:= congr_arg RG.Stage.supportExponent (params_eq U.B.valid m)
   have hκ(i:Site c): (coverNumber (B).B (neighbors D'' i):ℝ) ≤ η₀:= by
      unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters ℓ (radiusB x) (B).B_pos _ _ le_rfl).trans; rw [two_mul]
   obtain ⟨p'',hp'',hγ'⟩:= Board.intact (r:=r) (E:=V.sacrifice) R H A hF Z₀
   let Q:= incomeK B x L Ε β γ (2*Trio.base ℓ (radiusB x)) fQ t η₀ k₀
   let C:= CensusStep.hardCost R m
   have hE: U.B.a.clock.hatBeta (m+1)= betaF G x L:= PriceCompiler.beta_eq U.B.valid m
   have hξ : C ≤ (R.scout J I).pair.strong (betaF G x L) β / 8:= by
        have h := R.pledging.conducts.income.earns J I (step_paid U.B.a m) x (U.B.valid.pays m) β (show inBand (betaF G x L) β from hE ▸ trial_in he)
        apply le_trans h (le_of_eq ?_); ring
   have hk : Nonempty (Site c):=inferInstance
   have hu : 0≤ k₀:= by have hs:= hr.H_nonneg; rw [levy_erh R]; exact add_nonneg hs (by unfold Precise.tiny; positivity)
   have hΓ : ∀ i:Stars,0≤ fateZ B x L Ε β γ fQ t i:= by
       intro i; obtain ⟨k,hv,ht⟩:= (t i).voyage; unfold fateZ; exact mul_nonneg (by positivity) (Cost.nonneg (hv 0))
   have hΑ:0 ≤ Q:= by
       unfold Q incomeK Marlin.tithe; have hz : 0 ≤ Rack.beans (c:=C₀) (B'') k₀ (fun i=> fateZ B x L Ε β γ fQ t i):= by
           unfold Rack.beans; apply add_nonneg (by positivity); exact Finset.sum_nonneg (fun i hi=>mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (add_nonneg (hΓ i) (hΓ i))))
       exact mul_nonneg (mul_nonneg (by positivity) hz) (Real.exp_pos _).le
   obtain ⟨κ,hψ⟩:= hA.strong β (hE ▸ trial_in he) (B) hρ rfl C Ε γ fQ _ t le_rfl (fun i=> (hp i).2.1) (budget_nonneg (hγ' 0)) hξ hΑ
   let δ:= fun i:ℕ=>Abacus.tariff i VΩ (Trio.ornament (Precise.shape_ack U m ℓ) (fun i=> (t i).pact.polygon))
   obtain ⟨hᾱ,hN,hG,hΤ,hΩ⟩:= Award.supplies B x L Ε β γ (z) (D'') A' S' (Precise.shape_ack U m ℓ) fQ t X' (by unfold Trio.tent; omega) (by unfold Trio.base; omega) le_rfl hν (by unfold Meadow.studio Meadow.roomSize; omega) hA' hB' hQ' ht' (by rw [hW']; exact Precise.factors (Evoc.reflections _ _ _ _ _ _ _) p'.turns)
        (by rw [hW']; exact hC) rfl (hA.scene.2 _ (congr_arg RG.Stage.order (params_eq U.B.valid m))) hW (hQ.le.trans he') hh hβ hw' (hA.scene.1 (B) rfl hw' _ hh hβ c hΨ) hκ hA.bounds.2.1 hm.1 (fun s b=>(hm.2 s b).1) (fun s b=>(hm.2 s b).2.1) (fun s b=>(hm.2 s b).2.2.1) (fun s b=>(hm.2 s b).2.2.2) hψ hp'' hγ' le_rfl (Song.weighty A χ F) (T).down (T).low -- order check
   have hz': funds B x L Ε β γ z fQ t η₀ (u₀.lan x) ≤ qt * sFee D P u₀ F₀ x:= Award.dues ℓ (r+1) (X.p.profile I) _ _ _ _ _ _ t hW (congr_arg RG.Stage.order (params_eq U.B.valid m)) (congr_arg RG.Stage.power (params_eq U.B.valid m)) hρ hA.bounds.2.2 le_rfl (fun i=> (hp i).2.2.1) (fun i=> (hp i).2.2.2.2.le) (fun i=> (hp i).1) (fun i=> (hp i).2.2.2.1)
   have hw: (h₁+Routed.spill (A:=U) m r+qt+qt*h x)+turnFee B * (funds B x L Ε β γ z fQ t η₀ (u₀.lan x)) ≤ h₁+qt*γ₀:= by
       apply le_trans (add_le_add (add_le_add (add_le_add (add_le_add le_rfl (show Routed.spill (A:=U) m r≤ qt from by unfold Routed.spill; rw [hE]; exact hs)) le_rfl) le_rfl) (mul_le_mul_of_nonneg_left hz' (turnFee_pos _).le))
       rw [show turnFee B=Height.away (X.p.profile I) from (by unfold turnFee Height.away; congr; exact congr_arg RG.Stage.order (params_eq U.B.valid m); exact congr_arg RG.Stage.power (params_eq U.B.valid m))]; unfold Precise.wage Precise.pot; apply le_of_eq; ring
   have hψ' : (R.scout J I).pair.strong (betaF G x L) β=Time.forecastK U.B.a m R.scout β:= by rw [←hE]; rfl
   refine ⟨fun Z'₀=>?_,_,(show D₁.logRead=U₁+_ from hN),?_, VacuumListing.relax B hΤ hw hψ'.le,VacuumListing.relax B hΩ (add_le_add le_rfl hw) hψ'.le⟩
   · have hu := (Board.direct R ht H F A hF Z₀ Z'₀).symm; rw [V.β'] at hu
     exact hu.trans ((Caddy.preserve B I₀ M.listing.reg f'' ..).trans (hᾱ Z'₀))
   rwa [← hψ']
end work
end YM.RG01Estimate.Precise
