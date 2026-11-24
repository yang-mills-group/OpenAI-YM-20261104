import YM.Integration.WilsonRootedForcedProfileCash
import YM.Integration.WilsonVacuumPreResetLocalStore

/-! Keep the original scratch location inside its own hard support until its first
attachment. A single quarter of the genuine covering exponent pays the site count. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedHardAddressTariff
open Function Filter Finset Lattice Wilson RG Ac Marker
open Push.AbsoluteSums PhysicalNext.Repeat.Legato WilsonLimitConstruction
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}

def strip (p:BudgetPoint):ℝ := ((p.B+p.B+1:ℕ)^4:ℕ)*(4/p.supportExponent)

theorem site (p:BudgetPoint)(S:Support n):
    (S.card:ℝ)*Real.exp ((3*p.supportExponent/4)*coverNumber p.B S)  ≤  strip p*Real.exp (p.supportExponent*coverNumber p.B S):=by
  let k:ℝ:=coverNumber p.B S
  let a:=p.supportExponent
  let H:ℝ:=((p.B+p.B+1:ℕ)^4:ℕ)
  have ap:0<a:=p.exponent_pos
  have kk:0 ≤ k:=by dsimp only [k];positivity
  obtain ⟨C,covered,exactly⟩:=coverNumber_realized p.B S
  have length:S.card ≤ (p.B+p.B+1)^4*coverNumber p.B S:=by
    calc
      _  ≤  (halo p.B C).card:=Finset.card_le_card covered.1
      _  ≤  C.card*(p.B+p.B+1)^4:=Corona.halo_size C p.B
      _ = _ :=by rw [exactly,Nat.mul_comm]
  have number:(S.card:ℝ) ≤ H*k:=by dsimp only [H,k];exact_mod_cast length
  have area:k ≤ (4/a)*Real.exp (a*k/4):=by
    calc
      _=(4/a)*(a*k/4):=by field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (a*k/4)]) (by positivity)
  change (S.card:ℝ)*Real.exp ((3*a/4)*k)  ≤  (H*(4/a))*Real.exp (a*k)
  calc
    _ ≤ (H*((4/a)*Real.exp (a*k/4)))*Real.exp ((3*a/4)*k):=
      mul_le_mul_of_nonneg_right (number.trans (mul_le_mul_of_nonneg_left area (by dsimp only [H];positivity))) (Real.exp_pos _).le
    _=(H*(4/a))*(Real.exp (a*k/4)*Real.exp ((3*a/4)*k)):=by ring
    _= _:=by rw [←Real.exp_add,show a*k/4+(3*a/4)*k=a*k by ring]

variable (A:Activities G n)(p:BudgetPoint)
local notation "S" => (fun i:ℕ=>(A.forced i).support)

def tagged (h:Site n → ℂ)(q:ℕ → Site n → Config G n → ℂ)(i:ℕ)(U:Config G n):ℂ:=
  ∑x∈S i,h x*q i x U*(A.K i U:ℂ)

theorem earned {w:ℝ}(bound:A.KBound p w){M:ℝ}(mp:0 ≤ M):
    ∃b:ℕ → ℝ,(∀i,0 ≤ b i ∧ ∀U,‖A.K i U‖ ≤ b i) ∧
    Hit (S) p.B b p.supportExponent w ∧
    Hit (S) p.B (fun i=>(S i).card*(M*b i)) (3*p.supportExponent/4) ((strip p*M)*w) ∧
    ∀(h:Site n → ℂ)(q:ℕ → Site n → Config G n → ℂ), (∀x,‖h x‖ ≤ 1)  → 
      (∀i x,x∈S i → ∀U,‖q i x U‖ ≤ M)  →  ∀ i U,‖tagged A h q i U‖ ≤ (S i).card*(M*b i):=by
  obtain ⟨b,pay,rooms⟩:=bound
  have t0:0 ≤ strip p:=by unfold strip;exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) p.exponent_pos.le)
  refine ⟨b,pay,?_,?_,?_⟩
  · intro y
    simpa only [BudgetPoint.mass,mul_comm] using rooms y
  · intro y
    apply budget_mono (budget_scale (mul_nonneg t0 mp) (rooms y))
    · intro i
      split
      · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg mp (pay i).1)) (Real.exp_pos _).le
      · exact le_rfl
    · intro i
      by_cases alive:y∈S i
      · simp only [alive,if_pos,BudgetPoint.mass]
        have k:=mul_le_mul_of_nonneg_right (site p (S i)) (mul_nonneg mp (pay i).1)
        linarith only [k]
      · simp [alive]
  · intro h q hh hq i U
    have ac:‖(A.K i U:ℂ)‖ ≤ b i:=by rw [Complex.norm_real];exact (pay i).2 U
    calc
      _ ≤ ∑x∈S i,‖h x*q i x U*(A.K i U:ℂ)‖:=norm_sum_le _ _
      _ ≤ ∑_x∈S i,M*b i:=Finset.sum_le_sum (fun x hx=>by
        rw [norm_mul,norm_mul]
        exact mul_le_mul (by simpa using mul_le_mul (hh x) (hq i x hx U) (norm_nonneg _) zero_le_one) ac (norm_nonneg _) mp)
      _= _:=by simp

theorem original (R:Run G){N per j:ℕ}(live:j ≤ N){M:ℝ}(mp:0 ≤ M):
    let Q:=R.family.path.rep N per j
    ∃b:ℕ → ℝ,(∀i,0 ≤ b i ∧ ∀U,‖Q.activities.K i U‖ ≤ b i) ∧
      Hit (fun i=>(Q.activities.forced i).support) Q.p.B b Q.p.supportExponent (R.family.path.levels.clock.forcedAllowance j) ∧
      Hit (fun i=>(Q.activities.forced i).support) Q.p.B (fun i=>(Q.activities.forced i).support.card*(M*b i))
        (3*Q.p.supportExponent/4) ((strip Q.p*M)*R.family.path.levels.clock.forcedAllowance j) ∧
      ∀(h:Site (R.family.side j per) → ℂ)(q:ℕ → Site (R.family.side j per) → Config G (R.family.side j per) → ℂ),
        (∀x,‖h x‖ ≤ 1)  →  (∀i x,x∈(Q.activities.forced i).support → ∀U,‖q i x U‖ ≤ M)  → 
        ∀i U,‖tagged Q.activities h q i U‖ ≤ (Q.activities.forced i).support.card*(M*b i):=
  earned _ _ (R.makes.wilson.represents N per j live).good.labels.boundK mp
end YM.Integration.WilsonRootedHardAddressTariff
