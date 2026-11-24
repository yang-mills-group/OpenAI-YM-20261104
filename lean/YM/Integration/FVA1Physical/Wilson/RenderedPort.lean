import YM.Integration.FVA1Physical.Wilson.RenderedDraw
import YM.Integration.FVA1Physical.Wilson.PacketPort

/-! An arbitrary rooted interacting bank in the exact measured forest may be
sampled as the incoming field to the nonlinear normalized Wilson prescription.
The initial rooted norm pays both its full-volume source and every rough
exterior change at the original measured coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open MSbar.Jade MSbar.Lapaz MSbar.Parma MSbar.Tramp Push.Uniform Next.SectorChange Further.GaussianScalar
open MeasureTheory Matrix Metric YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}

/-- Both native chart representatives use the measured forest and the same
local posterior. The Boolean chooses its analytic copy or the uncropped field. -/
def packetConfig (A:Issue G) (V:Voice G) (y:ℝ) (b:Site A.f) (Z:Positions (Primary A.c G)) (copied:Bool)
    (U:Config G A.f) : Config G A.f :=
  if copied then chambers A.F (boxY y b) V (postcard G A.c A.fClock Z)
    (vest (priced A.F A.v A.pre.clip A.pre.path) (A.fClock•Z)) U else canoe (S:=A.S) A.F U

theorem rendered_packet_port (χ:ChartRatio G) (charts:LocalRatio χ) (V:Voice G) (clear:Clear G V)
    (P:Palisade) (K:Patch) (H H':RG.Stage) (m s p:ℕ) (h u:ℝ) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Mosaic.Issue G) (b:Site A.f) (T:Nesting G A.f)
      (Z:Positions (Primary A.c G)) (copied:Bool) {i:G.ColorIndex} (k σ w τ:ℕ) (ages:Ages) (pay:Salary)
      (cutoff:ℝ→ℝ) (color:Site A.f→G.Color) {D0 e d a B amount cost tagged fund:ℝ},
      let g:=A.fClock;let y:=tip G K.L x;let X:=boxX y b;let Y:=boxY y b
      let O:=postcard G A.c g Z;let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
      let live:=hotel A.F X Y V O ν (pillow y) (room y)
      let R':=woolModel A.F X V A.pre Y A.v O ν (pillow y) (room y)
      let φ:=fun U=>clockReading p g T (chartLog g (packetConfig A V y b Z copied U))
      K=A.S.patch → Season V H H' x A.pre A.post A.S (courage G K.L x) →
      A.Festival χ p i → Suite V χ A.F X Y O A.v A.pre ν (pillow y) (room y)
        (rot P y) (maxZ G P y) (topP V P y) D0 (linCash A.F (g•Z)) →
      Mosaic.Issue.Calibrate A V P X Y (g•Z) y e d →
      Ages.Vying ages p k g A.T A.F A.pre χ A.v → Lodge.Hat τ ages.w B cutoff →
      0 ≤ a → a ≤ αm y → m ≤ σ →
      (∀ n ≤ p, Tokew (address A.F G) a w σ 0 (PowerSeries.coeff n (barbed A.F A.v χ A.T)) amount ∧
        (PowerSeries.coeff n (barbed A.F A.v χ A.T)).totalDegree ≤ σ) →
      BankPaid b y s p m h T → enterFee G s^σ*y^h ≤ tagged → 0 ≤ fund →
      A.Port V χ P ages pay y k Z p σ color X Y amount (barry 0 σ p tagged ages.outer) a cost D0 →
      ∀ U∈live, |Rota.resample A.F (board A.F X) R' live φ U -
        localW A.F A.pre A.v V χ X Y U g Z A.T p cutoff color (enterRows A T)| ≤
        y^u+Salary.stamp pay p (Fintype.card (Lake A.F X G)) g cost fund := by
  have grow:=Work.E09.betaF_growth G K.L
  let r:=(LocalH.geom_patch G).choose
  have rpos:0 < r:=(LocalH.geom_patch G).choose_spec.1
  have vanishes: Tendsto (fun x:ℝ=>3*shade G*rot P (tip G K.L x)) atTop (𝓝 0) := by
    have rate:=((Mosaic.height grow P V).2.2.2.1.mulK grow (3*shade G)).bouquet grow (by norm_num)
    exact rate
  filter_upwards [grow.eventually (packet_draw (G:=G) m s p h u),grow.eventually_ge_atTop 2,
    vanishes.eventually (gt_mem_nhds rpos)] with x budget high small
  intro A b T Z copied i k σ w τ ages pay cutoff color D0 e d a B amount cost tagged fund g y X Y O ν live R' φ patch season fest suite cal vows hat ha cool sized action bank supply funded port U hit
  have law:=season.case_
  rw [←patch] at law
  have y1:1 ≤ y:=by linarith only [high]
  have band:lensT y g:=ever (zero_lt_one.trans_le y1) law.beta law.upper
  have β:1 ≤ A.pre.beta:=by linarith only [law.beta,high]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le β))
  have cap:g ≤ 1:=inv_le_one_of_one_le₀ (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt β)
  have env0:=chartLog_envelope g (clockReading_continuous p g T)
  have meas:Measurable (packetConfig A V y b Z copied):=by
    cases copied
    · exact (canoe_cont A.F).measurable
    · exact (informed A.F X Y V O ν clear (halo_subset ..)).1
  have env:Envelope φ:=⟨env0.1.comp meas,env0.2.choose,fun U=>env0.2.choose_spec _⟩
  have fwd:∀ n ≤ p,Vault (address A.F G) {b} a s σ 0 (PowerSeries.coeff n (enterRows A T))
      tagged ∧ (PowerSeries.coeff n (enterRows A T)).totalDegree ≤ σ := by
    intro n hn;obtain ⟨price,degree⟩:=packet_source_vault A ha cool T bank σ hn
    exact ⟨Quote.widen price supply le_rfl,degree.trans sized⟩
  apply packet_port A χ V P p k X Y Z b K H H' ages pay cutoff color (enterRows A T) φ env
    patch season clear fest charts suite cal vows cap hat ha action fwd port fund funded U hit
  cases copied
  · exact budget A V clear χ charts b T bank band gp (by simpa only [abs_of_pos gp] using cap) U Z _ _ _ _ _
      suite.seat.lifts small suite.positivity suite.seat
  · intro cent w inside
    change |clockReading p g T (chartLog g (chambers A.F Y V O ν (draw A.F X U cent g w)))-
      clockReading p g (enterRows A T) (meetVar Z (berth A.F A.pre A.v V X Y U Z g w))| ≤ y^u
    rw [copied_drawing_log A V clear χ charts X Y (halo_subset ..) U gp Z _ _ _ _ _ small
      suite.positivity suite.seat w inside,clockReading_enter,sub_self,abs_zero]
    exact Real.rpow_nonneg (zero_le_one.trans y1) _

end YM.Integration.FVA1Physical.Wilson
