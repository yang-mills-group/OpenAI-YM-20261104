import YM.MSbar.Tonic.Receipt
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
variable (hc:S.patch.Branches S.kernel G)
local notation "H"=>prior G f
include hc
variable (R: Rep G f)(τ A B C D:ℝ)(hR:R.Lawful τ A B C D)
-- density old milk U-term derivative `S likelihood`.
local notation "W"=> fun x:J=> postcard G c t x
local notation "i!"=>R.eval
local notation "q!"=> lid S β t G R v
include hR
variable (hβ:β=R.beta)(hs:∀ U, 0 < R.eval U)
include hs
local notation "Z!"=>rave S β t R L x
open Heath Heath.Stock Heath.Cottage Next.Fluctuations ConnectedActivityE6 Bulk
variable (F:Forest S.ratio)
local notation "Xc"=> Heath.canoe
variable (I Y: Support f)(J': Voice G)(p: Palisade) (ν:Positions (Key F G)){a b r K:ℝ}{n q j:ℕ} (g: Clear G J')
local notation "V₀"=> W x
local notation "Θ"=> hotel F I Y J' V₀ ν a b
local notation "z"=> chambers F Y J' V₀ ν
variable (hP: Posture p J' F a b r K n q I Y (t • x) ν R.p) (ht:∀ i∈L, S.ratio.embed (Measuring.chart c G i) ∈ I)
variable (hp: Picked G S F K)
local notation "m!"=> woolModel F I J' R Y v V₀ ν a b
local notation "g!"=> Rota.resample F (board F I) (woolModel F I J' R Y v V₀ ν a b) (hotel F I Y J' V₀ ν a b)
local notation "P"=> Bulk.expect S R V₀
variable {ε₀ ε K₀ V' s s':ℝ}
namespace Loan
omit hR hc hs
variable {R}
structure Tact (F:Forest S.ratio)(x0:Support f)(A:Set (Config G f))(r:Config G f→ℝ)(Y:Support f)(R:Rep G f)(V:Config G c)(E ε:ℝ):Prop where
   main : ∀ f:Config G f→ℝ,GaugeLocal S Y f →0≤ f→(∀ i,f i ≤ E)→|Bulk.expect S R V (Rota.resample F (board F x0) r A f)-Bulk.expect S R V f| ≤ ε
variable {r':Config G f→ℝ}{Ξ:Set (Config G f)} {k:Config G c}
variable (hS:Bulk.Admitted k R S τ A C B D)
-- adapt sign. need GaugeLocal and Rota.envelope for resample.Use unroll
variable (hY:Rota (S:=S) R k Y F (board F I) Ξ r' a K) -- remove
local notation "t!"=> Rota.resample F (board F I) r' Ξ
local notation "i₁"=> Bulk.expect S R k
variable (f':Config G f→ℝ)(hF:GaugeLocal S Y f') (he: ∀ i,|f' i|≤ s)
include hY hS hF he
lemma terms (hp:Tact F I Ξ r' Y R k (2*s) ε) : Envelope (t! f') ∧ (∀ i,i∉Ξ→ t! f' i=0) ∧ |i₁ (t! f')- i₁ f'| ≤ 2*ε:=by
    let v:Config G f →ℝ:= fun _ => s; let g:= f'+v; have hs0:0 ≤ s:= (abs_nonneg _).trans (he 1)
    have hV:GaugeLocal S Y v:= ⟨Envelope.const _,fun _ _ _=> rfl, fun _ _ _=> rfl⟩
    have hg:GaugeLocal S Y g:=⟨hF.1.add hV.1,fun i hi U=> congr_arg₂ (·+·) (hF.2 i hi U) (hV.2 i hi U),fun a b h=>congr_arg₂ (·+·) (hF.3 a b h) (hV.3 a b h)⟩
    let I':= Heath.Cottage.fence F (board F I) G
    have Hx(t)(h:GaugeLocal S Y t): Envelope (t! t):=by
        unfold Rota.resample; apply Heath.Cottage.unroll (f:=fun p:Config G f × IV F (board F I) G=>Rota.ghat r' p.2 t Ξ p.1); exact backdrop (Rota.stereo hS hY t h) measurable_swap
    have hu : 0 ≤ g:= fun i=>by change 0 ≤ f' i+s; linarith only [(abs_le.mp (he i)).1]; -- parse
    have hK(i): g i≤ 2*s:=by change f' i+s≤ _; linarith only [(abs_le.mp (he i)).2];
    have hδ:= hp.main g hg hu hK; have hV':=hp.main v hV (fun _=> hs0) (fun _=> by change s≤ _; linarith only [hs0]); have hz:t! g= t! f'+ t! v:=by
        funext i; unfold Rota.resample; rw [Pi.add_apply,← integral_add]; rotate_left; all_goals let w(f':Config G f→ℝ)(a: IV F (board F I) G):=Rota.ghat r' a f' Ξ i
        · exact ((show Envelope (w f') from backdrop (Rota.stereo hS hY f' hF) (measurable_id.prodMk measurable_const)).integrable I')
        · exact ((show Envelope (w v) from backdrop (Rota.stereo hS hY v hV) (measurable_id.prodMk measurable_const)).integrable I')
        exact integral_congr_ae (Eventually.of_forall (fun v'=>by unfold Rota.ghat g; simp only [Pi.add_apply]; ring))
    refine ⟨Hx _ hF,fun i hi=>?_,?_⟩; · unfold Rota.resample Rota.ghat; simp [Heath.spec,hi]
    unfold g at hδ; change |i₁ _- i₁ (f'+v)| ≤ _ at hδ; rw [hz,e_sum _ hS hF.1 hV.1,e_sum _ hS (Hx _ hF) (Hx _ hV)] at hδ; apply abs_le.mpr; constructor<;> linarith only [(abs_le.mp hδ).1,(abs_le.mp hδ).2,(abs_le.mp hV').1,(abs_le.mp hV').2]
end Loan
end YM.MSbar.Tonic
