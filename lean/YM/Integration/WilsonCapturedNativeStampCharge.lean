import YM.Integration.WilsonCapturedNativeClockFare
import YM.QuadraticLocal.Rebirth.Cash
import YM.X.Dial.Polo

/-! The actual filed clock is paid by its appointed semester. In a surviving
rank-r angular row the old coupling index is at least r, so charging the
original mark pole requires only its original shelf. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedNativeStampCharge
open Function Filter Finset Lattice RG Comparison.RG02 Comparison.RG02.Assembly
open Comparison.RG02.Adjacent Comparison.RG02.Moving.Path QuadraticLocal QuadraticLocal.Rebirth
open QuadraticLocal.Sunrise PositionX.Jet AllOrder AllOrder.Floe
open WilsonCapturedClockRankProjection
open scoped Classical ContDiff BigOperators Topology

private theorem coefficient (Q:Pace.Coin)(h:Q 0=0)(L pole i r q:ℕ)(inside:i ≤ q):
    motion (money ((caliber Q h).back L) (-(pole:ℤ)) i r) q =
      (Chart.tariff Q h L ((i:ℤ)-((r+pole:ℕ):ℤ)) (q-i):ℂ):=by
  let K:=(caliber Q h).back L
  let z:ℤ:=(i:ℤ)-((r+pole:ℕ):ℤ)
  let f:=fun t:ℝ=>K.rating t^z
  have germ:(fun t:ℝ=>(tags (-(pole:ℤ)) i r (K.rating t):ℂ)) =ᶠ[𝓝 0] Complex.ofReal ∘ f:=by
    filter_upwards [K.bright] with t ht
    apply congrArg Complex.ofReal
    rw [exchange _ _ _ ht.ne']
    change K.rating t^(_ : ℤ)=K.rating t^z
    congr 1;dsimp [z];ring
  have smooth:ContDiffAt ℝ (↑(q-i)) f 0:=(K.spin _).of_le le_top
  have read:motion (fun t:ℝ=>(tags (-(pole:ℤ)) i r (K.rating t):ℂ)) (q-i) =
      motion (Complex.ofReal ∘ f) (q-i):=by
    unfold Moving.Path.motion Assembly.jet
    rw [(germ.iteratedFDeriv ℝ (q-i)).eq_of_nhds]
  rw [triangular,if_pos inside,read]
  change motion (Complex.ofReal ∘ f) (q-i)=((someJ f (q-i):ℝ):ℂ)
  have same (g:ℝ→ℂ)(n:ℕ):motion g n=someJ g n:=by
    unfold Moving.Path.motion Assembly.jet someJ
    rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [same]
  exact PositionX.Dial.ofR f (q-i) smooth

local notation "fare" => WilsonCapturedCoveredSourceWage.fare
theorem filed (G:Gauge)(Q:Pace.Coin)(home:Q 0=0){g g₀ a ν rebate:ℝ}{L order shelf:ℕ}
    (credit:Recharged Q home g g₀ L order shelf a ν rebate)
    (pole q r:ℕ)(visible:pole ≤ shelf+1)(openShelf:0 < shelf)(upto:q ≤ order)
    {σ C:ℝ}(sp:0 < σ)(pc:0 ≤ C):
    charge ((caliber Q home).back L) (-(pole:ℤ)) q r (fun i=>fare G i r σ C) ≤
      a*(∑i∈range (q+1),fare G i r σ C):=by
  have cen:0 ≤ UVNext.PricedKernels.basin (σ/4):=by
    unfold UVNext.PricedKernels.basin;apply mul_nonneg (by norm_num)
    apply tsum_nonneg;intro t;unfold Next.Scheduling.decay;positivity
  unfold charge;rw [mul_sum]
  apply sum_le_sum;intro i hi
  by_cases rank:r ≤ i
  · have iq:=mem_range_succ_iff.mp hi
    let p:Loan:=⟨i,r+pole,shelf,openShelf,by omega⟩
    have receipt:=credit.progress p (iq.trans upto) le_rfl (q-i) (Nat.sub_le_sub_right upto i)
    change 1+|Chart.tariff Q home L ((i:ℤ)-((r+pole:ℕ):ℤ)) (q-i)| ≤ a at receipt
    rw [coefficient Q home L pole i r q iq,Complex.norm_real,Real.norm_eq_abs]
    have positive:0 ≤ fare G i r σ C:=by
      have fee:=WilsonOriginalSuspendedTensor.nonnegative G sp i
      unfold WilsonCapturedCoveredSourceWage.fare;positivity
    exact mul_le_mul_of_nonneg_right (by linarith) positive
  · letI : IsEmpty (Fin r ↪ Fin i):=⟨fun u=>rank (by simpa using Fintype.card_le_of_injective u u.injective)⟩
    simp [WilsonCapturedCoveredSourceWage.fare]

end YM.Integration.WilsonCapturedNativeStampCharge
