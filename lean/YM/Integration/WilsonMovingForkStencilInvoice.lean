import YM.Integration.WilsonMovingForkStencilFees
import YM.Integration.WilsonMovingForkDatedExterior

/-! On an actual earlier receiver the finite detector needs only the original
charged stencil rows. Their signed coefficients are the true fitted ones. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilInvoice
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Pilot OPE
open WilsonMovingForkStencilProgramme (Programme Basis coefficient issued)
open WilsonMovingForkPrintedFile (allSlots)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkHeterogeneousCut (Filed Invoice)
open WilsonOriginalJointTrialHearing (fee)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonMovingForkSeededPoint (seats)
open Extra.Histories Motion Extraction Table Spec PhysicalNext RG16 RG16.Literal Overlay Bid
open RG05Readout Next.Rank Next.Rank.Station Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonPublicForkTrialHearing
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{n K N per:ℕ}{d h:Fin n → ℕ}
  (old:Filed R d K)(table:Programme R d K)(κ:(i:Fin n) → Knob (h i))(pt:Fin n → Chamber)
  {u v c j:ℕ}(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)(jk:j ≤ K)
  (o:Fin n → Cover)(top:K < N)(input:∀i,R.family.label (d i))
  (raw:Basis R d → (i:ℕ) → Config G (R.family.side i per) → Poly (Stock.census (Fin n)))

local notation "w₀" => doses R d old.station (N:=N) (per:=per) (old.A N per) input
local notation "ξ₀" => seats (R:=R) jk per o
local notation "α" => coefficient (R:=R) (K:=K) N per w₀
local notation "X" i:max => Config G (R.family.side i per)
local notation "face" q:max i:max => (fun U=>(raw (q) (i) U).part (allSlots n))

def edge (z i:ℕ):ℝ:=∑q:Basis R d,‖α q‖*‖fee R N per (1:X z) (raw q) i (allSlots n)‖

def gap:ℝ:=∑q:Basis R d,‖α q‖*
  ‖reading R (N:=N) (face q c) u (uv.trans vc)-reading R (N:=N) (face q c) v vc‖

def terminal:ℂ:=∑q:Basis R d,(α q)*reading R (N:=N) (face q v) v le_rfl

def bill (upper:ℝ):Invoice where
  upper:=upper
  fine:=edge (N:=N) old input raw u
  across:=gap (N:=N) old uv vc input raw
  coarse:=edge (N:=N) old input raw v
  terminal:=0

local notation "fitted" => WilsonMovingForkStencilFees.At (N:=N) table κ pt w₀ ξ₀ raw

theorem original (upper:ℝ)
    (entered:‖reading R (N:=N) (credit R.family N per 0 (word R d j N per (jk.trans top.le) o input)
        K top.le) u (uv.trans (vc.trans ck))-
      reading R (N:=N) (numerator R N per K (product R d (N:=N) ξ₀ w₀)) u (uv.trans (vc.trans ck))‖ ≤ upper)
    (held:∀i,v ≤ i → i ≤ K → fitted i)(rent:∀q i,v ≤ i → i ≤ K → Integrable (raw q i) (prior G _)):
    WilsonMovingForkDatedExterior.At (issued table κ pt old) uv vc ck jk o (N,per) top input
      (terminal (N:=N) (v:=v) old input raw) (bill (N:=N) old uv vc input raw upper):=by
  let M:=WilsonMovingForkStencilProgramme.row table κ pt N per w₀ ξ₀
  have readAt (i z:ℕ)(lo:v ≤ i)(hi:i ≤ K)(zi:z ≤ i):=
    WilsonMovingForkStencilFees.deposited table κ pt w₀ ξ₀ raw zi (held i lo hi) (fun q=>rent q i lo hi)
  have cost (z i:ℕ)(lo:v ≤ i)(hi:i < K)(zi:z ≤ i):
      ‖WilsonThermometerUnitFilingFlatTelescope.feeAt R N per z M i‖≤edge (N:=N) old input raw z i:=by
    rw [show M=WilsonMovingForkStencilProgramme.row table κ pt N per w₀ ξ₀ by rfl,
      WilsonMovingForkStencilFees.original table κ pt w₀ ξ₀ raw zi (hi.trans top)
        (fun k hk low=>held k (lo.trans hk) (by omega)) (fun q k hk low=>rent q k (lo.trans hk) (by omega))]
    simpa only [edge,norm_mul] using
      (norm_sum_le (univ:Finset (Basis R d)) (fun q=>(α q)*fee R N per (1:X z) (raw q) i (allSlots n)))
  refine ⟨fun i lo hi=>(readAt i i lo hi le_rfl).1,entered,?_,?_,?_,?_⟩
  · intro i hi
    exact cost u i (vc.trans (mem_Ico.mp hi).1) (mem_Ico.mp hi).2 (uv.trans (vc.trans (mem_Ico.mp hi).1))
  · change ‖reading R (N:=N) (numerator R N per c (M c)) u (uv.trans vc)-
        reading R (N:=N) (numerator R N per c (M c)) v vc‖≤gap (N:=N) old uv vc input raw
    rw [(readAt c u vc ck (uv.trans vc)).2,(readAt c v vc ck vc).2,←sum_sub_distrib]
    simpa only [gap,←mul_sub,norm_mul] using
      (norm_sum_le (univ:Finset (Basis R d)) (fun q=>(α q)*reading R (N:=N) (face q c) u (uv.trans vc)-
        (α q)*reading R (N:=N) (face q c) v vc))
  · intro i hi
    exact cost v i (mem_Ico.mp hi).1 (lt_of_lt_of_le (mem_Ico.mp hi).2 ck) (mem_Ico.mp hi).1
  · change ‖reading R (N:=N) (numerator R N per v (M v)) v le_rfl-terminal (N:=N) (v:=v) old input raw‖≤0
    rw [(readAt v v le_rfl (vc.trans ck) le_rfl).2]
    simp only [terminal,sub_self,norm_zero,le_refl]

end YM.Integration.WilsonMovingForkStencilInvoice
end
