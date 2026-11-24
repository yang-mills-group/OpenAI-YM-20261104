import YM.RG01Estimate.SyntaxVac
/-!
 # Coeff rule closings and Ratio prices at candidate side. No ghost forecasts.
 -/
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
open Evoc Deck AbsoluteSums.Animals Board Promise Slide Trio
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
local notation "Ψ" => Mural.sheet X.p D (U.B.a.clock.adm (m+1))
local notation "Ω" => X.p.kernel
local notation "A₀" => X.O
local notation "A'" => (R.target (U.B.a.clock.J (m+1)) (U.B.a.clock.J m))
variable (u₀ : Precise.Horizon X D (U.B.a.clock.J (m+1)) (U.B.a.clock.J m) ℓ r n (U.B.a.clock.adm (m+1)))
   {s a b h :ℝ→ℝ}(F₀: Folio D (U.B.a.clock.adm (m+1)) u₀ e s a b h)
local notation "Ε" => u₀.Y (U.B.a.clock.hatBeta m)
local notation "H'" => (OpenAt D R.shape (U.B.a.clock.adm (m+1)) u₀ F₀ (R.scout J I) (U.B.a.clock.hatBeta m))
local notation "v" => Precise.amount s n F₀.tax
local notation "fQ" => wick G L u₀.y x
variable (hA : OpenAt D R.shape (U.B.a.clock.adm (m+1)) u₀ F₀ (R.scout (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) (U.B.a.clock.hatBeta m))
    (ht : m < N)(he:β ∈ Shoot.band U.B.a (m+1))
    (J₀ : Chartlet R.shape U N m H (Pane.virgin (Pane.orchestra U N H) (U.B.a.budget (m+1)) β))
    {W:ℕ→ Config G c→ℝ}     (Nh: Narrative β H V u₀ s a b W e) -- W needs var

variable (hw:1 ≤ n) (hx: c.val≤ Trio.most ℓ (U.B.a.clock.hatBeta m))

-- Exports Voucher composite. No tag-case particular letter assumption from estimated stencil on *other* history.
include hA ht he hw hx Nh J₀
lemma cards (K : Forest (𝕊).ratio)(k: (𝕊).Choices)(hs:0≤ s x) :
    ∃ (ρ: Bid.Dir G c→AxisChart G K) (U₀:Pill β H V u₀ s a b K ρ k W e),
        Promise.Card T K k ρ X.O (Promise.forecast T (Caddy.righty W) β γ) (Promise.liftsR T U₀.extra γ) (fun z=> Real.exp ∘ U₀.model z) (r+1) (B).order (B) β (Ε) (breath G L x) (gStep β^((r+1)+2)*b x) (capΨ D P u₀ a x) ∧
         (∀ z:Poll.Body (Precision.Key K G),∀ i∈ Metric.ball (0:Positions (Uniform.Primary c G)) Ε, Real.exp (U₀.model z (0,i))=1) ∧
         ∀ y: Positions (Uniform.Primary c G), ‖y‖+1 < Ε→ actual (gStep β • y)∈ Boulevard.sunny B→
             Receipt.Article T K (B') ρ x (v x) fQ Ε β (Real.exp 1) (v x) y V.rep.eval (fun z=> Real.exp ∘ U₀.model z) (e*n+0) n ∧
             Receipt.Note T K B' k ρ X.O x (v x) fQ Ε β (Real.exp 1) (v x) (F₀.solar x) (F₀.scrip x) (F₀.mist x) (F₀.moon x) y (e*n+0) n (r+1) (B).order := by
  let s' := s x; obtain ⟨hp,hK,hY,hΒ,hX⟩:= authentication R H β he J₀
  have hr: (𝕊).patch.L=L:= PriceCompiler.block_eq U.B.valid m
  have hs' : (B).order=(X.p.profile (I)).order:= congr_arg RG.Stage.order (params_eq U.B.valid _)
  have hB: (B).threshold=Pressure.temp x:=rfl
  obtain ⟨hu,hW,hQ,hP,hE,hM,hF⟩:= hA.fare β hY hΒ
  have ho : (A').table=X.O:= R.settles _ _
  have he' := hA.song; unfold Boardwise at he'; rw [← hs'] at he'
  obtain ⟨hp',hK',ρ,hJ,hA',hB',hZ⟩:= Board.songster R ℓ u₀.Hb ht H K β he hx J₀ he' (Real.exp_pos _).le (hA.bounds.2.1.le)
  obtain ⟨U₀⟩:= Nh.sings K ρ k hp hK hJ hA' hB'
  have hv := Trio.quilt G L ℓ x (Pane.panel U m H) T K (show c.val ≤ Trio.most ℓ x from hx) hr J₀.laws.data.room.larger
  refine ⟨ρ,U₀,⟨?_,?_,hP,?_⟩, fun z i hi=> by rw [U₀.zeroField z i (mem_ball_zero_iff.mp hi),Real.exp_zero],fun y hy hz=>?_⟩
  · intro p' ht'; have he := U.B.support.cap N m ht.le
    have hz: U.B.a.clock.loopCap m≤ ConnectedActivityE6.loopBill G L x := (coverBill ..).2.trans (brace x hQ)
    let C₀:= X.p.profile I; have hh:U.B.a.params m=C₀:= params_eq U.B.valid _
    have hW': (T).down.Bounds (T).low C₀.width C₀.paths (ConnectedActivityE6.loopBill G L x):= by rw [← hh]; exact {he with two:=budget_loosen he.two hz}
    have hU := U₀.horizon; rw [hs'] at hU ⊢; let P':=C₀.order+((r+1)+2)
    have hh':(T).low=C₀.clip:= congr_arg RG.Stage.clip hh
    unfold capΨ; rw [← show (T).low=(X.p.profile I).clip from hh']
    have hk := hv.one
    -- Ufee argument depends on clip? only C/μ.
    exact Promise.crest_view T (B) U₀.extra u₀.Ufee _ _ _ _ hW' (countsP _ _ hv.overall) hk (by omega) hA.bounds.2.1.le hE hM (Boulevard.coupling U _ _ ht) le_rfl hU _ ht'
  · intro z hz hh; apply Promise.supplies_forecast _ _ _ _ _ _ hu _ _ hz hh
    intro y hy hx; rw [← Board.cart]; exact U₀.writes _ (mem_ball_zero_iff.mp hy) hx
  · intro i hi l hl; exact U₀.peano l i (mem_ball_zero_iff.mp hi) hl
  obtain ⟨hZ,ε,hb⟩:= hZ k y hy (smoky hz)
  refine ⟨?_,by rwa [ho] at hZ⟩
  let A:= s' -- Card script
  have hG: V.rep.path=(T).up:= V.pathU
  have hp: V.rep.Lawful (U.B.a.params (m+1)).width (U.B.a.params (m+1)).paths (U.B.a.clock.loopCap (m+1)) (U.B.a.clock.allowance (m+1)) (U.B.a.clock.forcedAllowance (m+1)):= by
       refine ⟨?_,by rw [V.point]; exact V.point ▸ V.legal⟩
       rw [hG,V.clip]; exact U.B.support.cap _ _ ht
  refine LayoutWeight.affairs T K (B') ρ x y V.point Nh.hard hG V.β' Nh.scalar V.clip U₀.model F₀.tax (hr ▸ U₀.bill_s) U₀.tall
      (fun z i hi => U₀.zeroField _ _ (mem_ball_zero_iff.mp hi)) (hr ▸ hA.bounds.1) hw F₀.talons hs F₀.t' hp ?_ ?_ ?_
  · intro u hr' z hz; rw [hr] at hr'; obtain ⟨hτ,hδ⟩:= hb u hr'; have hh:= hδ.mask _ hz
    have h:= U₀.reads ((gStep β)⁻¹ • u) (mem_ball_zero_iff.mp hτ) z hz; rw [smul_inv_smul₀ (Fare.gS β hu).1.ne'] at h; exact h hh -- implication needs apply
  · intro u hu z hz; rw [hr] at hu; exact (hb u hu).2.mask z hz
  have hη: (U.B.a.clock.allowance (m+1))=incomingE G L x:= by unfold incomingE; rw [← PriceCompiler.beta_eq U.B.valid m]; rfl
  rw [hη]
  exact (Real.exp_monotone (mul_le_mul_of_nonneg_right hv.finalP (by unfold incomingE; positivity))).trans hA.menus -- hv lever maybe site? 
end YM.RG01Estimate.Precise
