import YM.FormalOPE.RG10.OpenSlots.Foundation
/-!
 # Full-field pull procedure at a step. One individual ticket at a time, keeping its
 weight and poles before restoring Laurent powers. Multiply tickets to value inserted pairs etc.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E K:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E][NormedAddCommGroup K][NormedSpace ℝ K]
namespace Quadratic
-- integration with determinant normalized immediately
variable (Q:Quadratic (E×K))
 def center (h:(core Q).RespectsPrice): E × K→ₗ[ℝ] E × K:= (LinearMap.fst ℝ E K + skew Q h ∘ₗ LinearMap.snd ℝ E K).prod (LinearMap.snd ℝ E K)
@[simp] lemma centering (h:(core Q).RespectsPrice)(x y): center Q h (x,y)= (x+skew Q h y,y):= rfl
variable [MeasurableSpace E][BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
 def integrateP (h:(core Q).RespectsPrice): Permit (E×K)→ₗ[ℝ] Permit K:= (Papers.splitting h.inner μ).comp (translation (center Q h)).toLinearMap
 lemma integrateP_display (h:(core Q).RespectsPrice)(p: Permit (E×K))(y:K): (integrateP Q μ h p).val y=h.inner.average μ (fun x=> p.val (x+skew Q h y,y)):= Penn h.inner μ (translation _ _) y
 def uptake (h:(core Q).RespectsPrice) : Ticket (E×K)→+ Ticket K:= throughPrice (integrateP Q μ h).toAddMonoidHom
lemma upright (h:(core Q).RespectsPrice){W:Ticket (E×K)}(hx:incline W): incline (uptake Q μ h W):= by unfold incline at hx ⊢; unfold uptake integrateP throughPrice; rw [←coeff_zero_eq_constantCoeff_apply]; simp [hx,singly]
 def fit (h:(core Q).RespectsPrice)(A W: Ticket (E×K)): Ticket K:= uptake Q μ h (W*A)* Return (uptake Q μ h W)
lemma fit_eq (h:(core Q).RespectsPrice)(A W: Ticket (E×K))(hx: incline W): uptake Q μ h W * fit Q μ h A W= uptake Q μ h (W*A):= by rw [fit, mul_left_comm _ (uptake Q μ h (W*A)),spend_it (upright Q μ h hx), mul_one]
end Quadratic

variable {G: Gauge} {c f n: Side}
variable {S: StepData c f} {L: Fabric G c} {P:Inside S.ratio}
variable {H:S.patch.Branches S.kernel G} {hf:_root_.Even f.val}{t:S.Choices} {C:Cloth L}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ω"=> Field (Cloth.choose T0)
local notation "F"=> Cross (G:=G) S P
local notation "B"=> Field C.choose
local notation "κ"=> exchange (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "π"=> spool (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Γ"=> layer S H t hf L
open Quadratic
 def receipt (P: Inside S.ratio) (t:S.Choices)(J:ChartRatio G)(w:PowerSeries ℝ)(U:Unmasked G f): Ticket (Cross (G:=G) S P × Flats G c) := boost (blankRight P) U.W * boost (LinearMap.fst ..) (tissue J (Index S P)) * chip w (substep P t)
lemma along {J:ChartRatio G}(h:LocalRatio J)(w:PowerSeries ℝ){U:Unmasked G f}(hw: incline U.W): incline (receipt P t J w U):= pool (pool (preserve_boost _ hw) (preserve_boost _ (awake h))) (OpenSlots.restores _ _)
namespace Bank
variable {J:ChartRatio G}{U:Unmasked G f}
variable {z:(layer S H t hf L).Cost→PowerSeries ℝ}
lemma x_pull (u:Ticket (Flats G f)): boost κ (boost (blankRight P) u) = boost (castAt T0) u:= by apply into; intro x; obtain ⟨⟨x,y⟩,rfl⟩:= (d).surjective x; simp_rw [caught, trade, moored]; rfl
lemma shipments {Λ: Law Ω}{V:Ticket Ω} (hj:LocalRatio J)
 (h:Bank T0 J z U Λ V): V = boost κ (receipt P t J (z none) U)* boost π (tissue J C.choose.Bulk * remExponent C (z ∘ some)):= by
 rw [h.price, split_tissue (J:=J) hj,stocked z]; unfold receipt; simp_rw [_root_.map_mul,x_pull]
 let Y:= boost (castAt T0) U.W; let K:= boost κ (boost (LinearMap.fst ..) (tissue J (Index S P))); let D:= boost π (tissue J C.choose.Bulk); let A:=boost κ (chip (z none) (substep P t)); let R:= boost π (remExponent C (z ∘ some))
 change Y * (K * D)*(A * R)= Y*K*A * (D * R); ring
end Bank
end YM.FormalOPE.RG10.OpenSlots
