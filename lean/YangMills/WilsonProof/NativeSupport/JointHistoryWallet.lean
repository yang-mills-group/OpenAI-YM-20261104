import YangMills.WilsonProof.NativeSupport.JointPolynomialCalendar
import YangMills.WilsonProof.NativeSupport.JointOriginalTempo
import YangMills.WilsonProof.NativeSupport.JointInletBootstrap
import YangMills.WilsonProof.NativeSupport.JointPrimitiveBudget
import YangMills.WilsonProof.NativeSupport.JointProjectionLedger

/-! One allowance on every date of the actual block schedule.  Both sheets
fit it; its product consists only of native block lengths to a fixed power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice Wilson RG RGComparison.Core16 Marker Extra.Multi PhysicalNext.Repeat
open scoped Classical BigOperators
variable {G:Gauge} {A:Levels G} {per:ℕ}

def wallet (N:ℕ) (L:ℕ→ℝ) (k r:ℝ) (j:ℕ):ℝ:=
  Nat.rec (0:ℝ) (fun i v=>L (N-(i+1))*v+k*(v^2+r^2)) (N-j)

theorem wallet_top (N:ℕ) (L:ℕ→ℝ) (k r:ℝ):wallet N L k r N=0 := by simp [wallet]

theorem wallet_step {N j:ℕ} (jn:j<N) (L:ℕ→ℝ) (k r:ℝ):
    wallet N L k r j=L j*wallet N L k r (j+1)+k*(wallet N L k r (j+1)^2+r^2) := by
  have count:N-j=N-(j+1)+1:=by omega
  unfold wallet
  rw [count]
  change L (N-(N-(j+1)+1))*_+_=_
  rw [show N-(N-(j+1)+1)=j by omega]

theorem wallet_positive (N:ℕ) {L:ℕ→ℝ} (price:∀ j,0 ≤ L j) {k r:ℝ} (k0:0 ≤ k) (j:ℕ):
    0 ≤ wallet N L k r j := by
  unfold wallet
  induction N-j with
  | zero=>exact le_rfl
  | succ n ih=>exact add_nonneg (mul_nonneg (price _) ih) (mul_nonneg k0 (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem paid_calendar (T:Slices A per) {t N:ℕ} (tn:t ≤ N) (W s ν:ℕ) {x:ℝ}
    (heat:256 ≤ x) (width:2*(W:ℝ) ≤ x) (duration:((N-t:ℕ):ℝ) ≤ (W:ℝ)*x)
    (span:(scale (traversal T tn):ℝ) ≤ x^W) :
    let L j:=((A.S.block j).val:ℝ)^ν
    let k:=x^(2*priceDegree W s+1)
    let r:=(x^radiusDegree W s ν)⁻¹
    (∀ j,0 ≤ wallet N L k r j) ∧ (∀ j,t ≤ j → j ≤ N → wallet N L k r j ≤ r) ∧ r ≤ 1/2 := by
  intro L k r
  have x1:1 ≤ x:=by linarith
  have xp:=zero_lt_one.trans_le x1
  have r0:0 < r:=inv_pos.mpr (pow_pos xp _)
  have positive:=wallet_positive N (L:=L) (r:=r) (fun j=>pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg xp.le (2*priceDegree W s+1))
  refine ⟨positive,fun j tj jn=>(original_bootstrap T tn ν (pow_nonneg xp.le _) r0 _ positive (wallet_top ..)
    (calendar_bootstrap_fee W s ν x1 width (Nat.cast_nonneg _) duration span)
    (fun j _ top _=>(wallet_step top L k r).le) j tj jn).2,?_⟩
  have d:1 ≤ radiusDegree W s ν:=by unfold radiusDegree;omega
  have large:2 ≤ x^radiusDegree W s ν:=by
    calc (2:ℝ) ≤ x^1 := by rw [pow_one];linarith
         _ ≤ _ := pow_le_pow_right₀ x1 d
  simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<2) large

theorem funded_date (W s ν:ℕ) {x μ S z box Γ u:ℝ}
    (heat:256 ≤ x) (mu:1 ≤ μ) (s0:0 ≤ S) (z0:0 ≤ z) (bx:1 ≤ box)
    (load:μ ≤ x^(4*W+2)) (sites:S ≤ x^13) (primitive:z ≤ x^(s+1)) (boxCap:box ≤ x^13)
    (q0:0 ≤ Γ) (vac:Γ ≤ 1/x^priceDegree W s)
    (u0:0 ≤ u) (fit:u ≤ (x^radiusDegree W s ν)⁻¹) :
    let K:=x^priceDegree W s
    let r:=(x^radiusDegree W s ν)⁻¹
    let h:=r^2
    let a:=oldRadius K u h
    let d:=bornRadius K h
    let old:=a*(μ*S*u)
    let fresh:=μ*S*(d*(h*z))
    1 ≤ a ∧ 1 ≤ d ∧ box*(Γ+old+fresh) ≤ 3 ∧ fullFare (mountedFare Γ old fresh) ≤ (1/x^2)/μ ∧
      2/min d (a^2) ≤ x^(2*priceDegree W s+1)*(u^2+r^2) := by
  intro K r h a d old fresh
  have xp:0 < x:=by linarith
  have m0:=zero_le_one.trans mu
  have b0:=zero_le_one.trans bx
  obtain ⟨hpos,_,a1,d1,au,dh,fee⟩:=calendar_radii W s ν (by linarith : 2 ≤ x) fit
  have capacity:=calendar_capacity W s heat m0 s0 z0 b0 load sites primitive boxCap
  have mS:=mul_nonneg m0 s0
  have oldFee:old ≤ μ*S/K:= by
    calc
      old = μ*S*(a*u) := by dsimp only [old];ring
      _ ≤ μ*S*(1/K) := mul_le_mul_of_nonneg_left au mS
      _ = _ := by ring
  have freshFee:fresh=μ*S*z/K := by
    change μ*S*(d*(h*z))=_
    rw [←mul_assoc d h z,dh];ring
  have room:= heap_cash (pow_pos xp (priceDegree W s)) mu s0 z0 bx (by linarith : 1 ≤ x)
    q0 (mul_nonneg (zero_le_one.trans a1) (mul_nonneg mS u0))
    (mul_nonneg mS (mul_nonneg (zero_le_one.trans d1) (mul_nonneg hpos.le z0))) capacity vac oldFee freshFee.le
  exact ⟨a1,d1,room.1,room.2,fee⟩

theorem both_sheets {q:ℝ} (Θ:Luna.Tableau q 300) (L:Side) (big:3 ≤ L.val) {γ u e k r:ℝ}
    (u0:0 ≤ u) (stain:Real.sqrt γ ≤ 1) (err:e ≤ k*(u^2+r^2)) :
    Luna.Frets.tempo Θ L*(4*u)+e ≤ ((L.val:ℝ)^tariffDegree Θ.price)*u+k*(u^2+r^2) ∧
    Real.sqrt γ*(4*u)+e ≤ ((L.val:ℝ)^tariffDegree Θ.price)*u+k*(u^2+r^2) := by
  have rate:=original_tempo Θ L big stain
  have τ:0 ≤ Luna.Frets.tempo Θ L := by change 0 ≤ (Θ.price*(1+(L.val:ℝ))+1)*2;have hh:=Θ.sane;positivity
  have gp:=Real.sqrt_nonneg γ
  constructor
  · rw [←mul_assoc];exact add_le_add (mul_le_mul_of_nonneg_right (by linarith only [rate,gp,τ]) u0) err
  · rw [←mul_assoc];exact add_le_add (mul_le_mul_of_nonneg_right (by linarith only [rate,gp,τ]) u0) err

end YM.Integration.InletSusceptibility.Packet
namespace YM.Integration.InletSusceptibility.JointShadow
open Lattice Wilson RG Marker Packet
variable {G:Gauge} {n:Side} {I V:Type} [Fintype I] [Fintype V] [DecidableEq V]
theorem root_mono {p:BudgetPoint} {X:I→Support n} {E:I → Config G n → Poly (Stock.census V)} {w:V→ℝ} {a b:ℝ}
    (root:RootedSheet p X E w a) (h:a ≤ b) : RootedSheet p X E w b := by
  obtain ⟨c,h1,h2,h3⟩:=root;exact ⟨c,h1,h2,fun i=>(h3 i).trans h⟩
end YM.Integration.InletSusceptibility.JointShadow
