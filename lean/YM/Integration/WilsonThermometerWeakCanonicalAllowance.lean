import YM.Integration.WilsonThermometerWeakSourceRadius
import YM.MergeProof.SteamW

/-! The weak signed source uses the printed entrance allowance on the original panel.
The spare power of the initial inverse temperature pays both its finite physical
source fee and the requested detector amplitude. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCanonicalAllowance
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Next.Rank Perch Glimmer Tapes Atlas Station Vac.Numbers
open scoped Classical Topology BigOperators
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta

def maximum (G:Gauge) (D:ℕ):ℕ:=Finset.univ.sup fun e:Fin (D+1)=>winter G e.val

theorem printed {D:ℕ} {z:ℝ} (h:∀ j≤D,Accent.generator G j≤z):
    (2:ℝ)*(maximum G D+1:ℕ)≤z:=by
  let F:=fun e:Fin (D+1)=>winter G e.val
  have ho:Finset.univ.Nonempty:=⟨(0:Fin (D+1)),Finset.mem_univ _⟩
  obtain ⟨e,_,he⟩:=Finset.exists_mem_eq_sup (s:=Finset.univ) ho F
  have own:=h e.val (Nat.lt_succ_iff.mp e.isLt)
  unfold maximum;rw [he];exact own

theorem source {D d:ℕ} (hd:d≤D) {u a:ℝ} {j:ℕ} (one:1≤β j) (positive:0<far (A) j)
    (u0:0≤u) (a0:0≤a) (cash:a*(pulseFee d*u*(Fintype.card (Letter d):ℝ))≤β j):
    pricesTop (fly (A)) (far (A)) j d*(a*u)≤far (A) j*(β j)^(maximum G D+1):=by
  let b:=β j
  let q:=maximum G D
  let K:=far (A) j
  have rent (i:Letter d):K/fly (A) (kept i) j≤K*b^q:=by
    have qh:kept i≤D:=(Nat.sub_le ..).trans hd
    have h:winter G (kept i)≤q:=Finset.le_sup (f:=fun e:Fin (D+1)=>winter G e.val) (Finset.mem_univ ⟨kept i,by omega⟩)
    unfold Bandage.fly MergeProof.fog;rw [div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one h) positive.le
  have est:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>rent i)) (feepos d).le) (mul_nonneg a0 u0)
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at est
  calc
    _ ≤ _ := est
    _ = (K*b^q)*(a*(pulseFee d*u*(Fintype.card (Letter d):ℝ))):=by ring
    _ ≤ (K*b^q)*b:=mul_le_mul_of_nonneg_left cash (mul_nonneg positive.le (pow_nonneg (zero_le_one.trans one) _))
    _ = _:=by rw [pow_succ];ring

theorem restored (simple:G.Simple) {H:ℕ} (plan:Panel H) {c:ℝ} (hc:0≤c):
    ∀ᶠ k:ℕ in atTop,c*Perch.bill ((plan.bag ((A).clock.J k)).credit-1) (clim (A) k)≤β k:=by
  let b:ℝ:= -9-plan.currency
  filter_upwards [(hat_rate (A) simple).eventually (Paint.absorb b (b+1) (by linarith) c),
    (hat_rate (A) simple).eventually (Paint.monitors (b+1) 1 zero_lt_one)] with k fee cost
  have eq:=plan.vital ((A).clock.J k)
  have h:=(plan.bag ((A).clock.J k)).fits
  have le:(plan.bag ((A).clock.J k)).credit-1≤b:=by dsimp only [b];linarith only [eq,h]
  refine ((mul_le_mul_of_nonneg_left (Glimmer.billed _ le) hc).trans fee).trans ?_
  calc
    _ ≤ Real.exp (Real.log (β k)):=by
      unfold Perch.bill;apply Real.exp_le_exp.mpr
      simpa only [one_mul,mul_comm] using cost
    _ = _:=Real.exp_log (WardBin.hot (A) k)

end YM.Integration.WilsonThermometerWeakCanonicalAllowance
end
