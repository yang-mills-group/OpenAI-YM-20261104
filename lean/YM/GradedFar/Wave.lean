import YM.GradedFar.Emerge
/-!
# Through-coefficient comparisons in the project's MS scheme

Relative to the indicated other **physical** expenses. No changes of elections after setting these costs.
No new assertion of matching to graph integrals. This is in precisely `Main.Match`'s theory, with the
`Equator.wave` and `Gift_shape` on the scale and specified flag. Refund/concert transfers in the OPE
line are **on formal series**. All crop is after that composition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Filter Function Set PowerSeries
open Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.GradedFar FVA2.O.Enh FVA2.Dframe
open FVA2.O.Score FVA2.O.Canon FVA2.O.Project
open MS MS.Book MS.Fleet MS.Land FVA2.Register
open Spec Table Extraction OPE.Orbits
open scoped Topology Classical BigOperators
variable {G:Gauge} {n p h l:ℕ}{d: Fin n→ℕ} {hG:G.Simple} (N:WilsonPrescription G)
    (Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match N hG Z σ true) (ν:ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "Ζ" => Scale.Measure.Z N.scheme N.criterion ν Z
local notation "τ" => Scale.Measure.f N.criterion ν Z
local notation "Wave" => Equator.wave ν Z

-- bound by H.eqconv. Mixed cap arguments retained, lifted to one common through-order **here** on predictions.
def msCompact (hd:AppointedH140Through l d) (x:Stage n) (u:AppointedH140Inputs G d) : PowerSeries ℂ :=
    PowerSeries.mk fun k=> Facets.actMark (Ζ l) (Facets.couple τ (Wave l)) n x k (raised hd u)
include H in
lemma bookCompact (hd:AppointedH140Through l d)(x:Stage n)(u:AppointedH140Inputs G d): msCompact N Z ν hd x u=FormalCompact A l hd x u:= by
    ext k; simp_rw [msCompact, FormalCompact,coeff_mk,H.eqconv ν l]

-- input/output transfer for the h vector (x remains in the compact Near window)
def msBills (u:Scan G n)(x:Points n) := refund (seats Ζ) (seats (replay Ζ)) τ
      (fun i=> FarCoefficients (Equator.wave ν Z) i x) u
include H in
lemma bookBills (u:Scan G n)(x:Points n): msBills N Z ν u x= FarCoefficients A u x := by
    obtain ⟨HA,HB,Hg,hX⟩:= H.separatedOPE ν
    have hv:= spin_v (office (ν:=ν) H.details.toServed.toPosted.toQuoted.toContract)
    specialize Hg u 0 x
    change credit (seats Ζ) τ (fun i=> OPECoefficients Wave i 0 x) u=receipt (seats Ζ) (OPECoefficients A u 0 x) at Hg
    have ha : (fun i:Scan G n=> OPECoefficients Wave i 0 x)= fun i:Scan G n=> FarCoefficients Wave i x:= funext (fun i=> congrFun (HA.start_u i) x)
    rw [ha,HB.start_u u] at Hg
    unfold msBills refund; rw [Hg,timely,hv,receipt_K]

/-- MS OPE, **after** transformation, as in the cited equality. Sum over Near
slots by homogeneous basis, and Output through its horizon. -/
def msComponent (u:AppointedH140Inputs G d)(x:Points n) (a:Q G) := ∑ p:Picks G d,
    PowerSeries.C (multipliers u p) * msBills N Z ν (indexScan p) x a
def msVector (u:AppointedH140Inputs G d)(x:Points n) (p h:ℕ)(t:ℝ) : Sec G h :=
    ∑ a:Toon G h, appointedH140Crop p t (msComponent N Z ν u x (Dframe.flash a)) • theory a
include H in
lemma bookVector (u:AppointedH140Inputs G d)(x:Points n)(q h:ℕ)(t:ℝ) : msVector N Z ν u x q h t=croppedVector A h q u x t := by
    unfold msVector msComponent; simp_rw [bookBills N Z H ν]; rfl

local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G

variable {C:Family G}{fo:Extraction.Order}{S:Table C.book}(F:Final C fo S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(J:ℝ→tower S)
    {t:ℝ→ℝ}(ht:Coupling G t)

include ht hG in
lemma remaining_budget (p:ℕ): ∀ᶠ r in trail, g r^p ≤ (2*t r)^p := by
    filter_upwards [ (ratio_clock hG ht).eventually_const_lt (by norm_num:(1/2:ℝ)<1), strength_positive hG] with r hr hs
    exact pow_le_pow_left₀ hs.le (by linarith [(lt_div_iff₀ hs).mp hr]) _

-- final form of comparison for correlations, conditional on compact RoundPoint comparison at exact arguments (G9)
variable {Λ:ℝ}(hΛ:0<Λ) {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)
include H hx hΛ ht
theorem ms_at_compact (hd:AppointedH140Through l d)(p:ℕ) {B:ℝ}(hB:0<B) (hf:RoundPoint F J t A hd (nofare l) Λ B p K {0}):
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ v:OPE.Viewers F,∀ o x,∀ h: x∈K,∀ u,Box u 1 →
      ‖TrueCompact F J v r o x u - appointedH140Crop p (t r) (msCompact N Z ν hd ⟨x,hx h⟩ u)‖ ≤ C*(t r)^(p+1) := by
  obtain ⟨C,hC,H'⟩:=compact_price F J hG hx t A p hd hΛ hB hf
  refine ⟨C*2^(p+1),by positivity,?_⟩
  filter_upwards [H',remaining_budget (hG:=hG) ht (p+1)] with r hr hv v o x h u hu
  rw [bookCompact N Z H]; exact (hr v o x h u hu).trans ((mul_le_mul_of_nonneg_left hv hC).trans_eq (by rw [mul_pow, mul_assoc]))

include hK
/-- And OPE through all orders in H-frame and that prescription. *Point/corresponding prices*, at all the indicated
Near geometries, not a differentiation/the derivative version, not a regulator implementation.
Still using the pointwise G9 on required programs incl. compact pricing e.g. at coupling order zero for Gram, and
G1 growing frame operator forecast. Also uses the QScale2 upper frame log expenses. -/
theorem ms_ope (hd:AppointedH140Through l d)(hh:h≤l)
    (Hq:OPE.LogTrace F Q.port)(Hh:Fork.Coat F Q J h)(Hp:∀ i, Fork.Coat F Q J (d i))
    (hW:∀ B> (0:ℝ),FrameForecast J t W h Λ B)
    (fund:∀ B>0,LeadingTicket F J h t N Λ B)
    (hf:∀ B>0,∀ p,RoundPoint F J t A hd (e:=Output h) (fun _=>hh) Λ B p K {RootG})
    (hout:∀ B>0,∀ p,RoundPoint F J t A (d:=Output h) (fun _=>hh) (e:=Output h) (fun _=>hh) Λ B p {0} {RootG})
    (q:ℕ):∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ o x,x∈K→∀ u:AppointedH140Inputs G d, Box u 1→
       width (packet F J Q h o r x u - msVector N Z ν u x q h (t r)) ≤ C*(t r)^(q+1) := by
  obtain ⟨C,hC,H'⟩:= localized F Q J N Z H ν hd hh hΛ hK hx ht Hq Hh Hp hW fund hf hout q
  refine ⟨C*2^(q+1),by positivity,?_⟩; filter_upwards [H',remaining_budget (hG:=hG) ht (q+1)] with r hr hv o x hz u hu
  rw [bookVector N Z H]; exact (hr o x hz u hu).trans ((mul_le_mul_of_nonneg_left hv hC).trans_eq (by rw [mul_pow,mul_assoc]))
end YM.Integration.GradedFar
