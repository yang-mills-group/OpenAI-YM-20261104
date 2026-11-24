import YM.Integration.WilsonThermometerWeakPhysicalCombination
import YM.Next.RANK.Prepaid

/-! The radius invoice for a fixed real weak detector. It includes both its actual
measured field dilation and its independent position dilation, before the regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakDetectorStake
open Function Filter Set MeasureTheory RG RG12 Extra.Histories Lattice Wilson Source Labels
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "A" => R.family.path.levels

theorem original (simple:G.Simple) (exam:Tapes.Panel H) (dH:d≤H) (v:(Rf).label d):
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N),
    let P:=(Rf).path.rep N p k;let g:=GaugeScale Rf k N p;let s:=clim (A) k
    let ξ:=exam.bag ((A).clock.J k)
    let F:=(Rf).labels.level d
    let x:=Price.weightTag Rf d (mag (A) ξ.band k) v
    (2*F.coeffSize (F.scaled (P.p.threshold/g) x)≤bill (ξ.credit-1) s) ∧
      (∀ y:ℝ,y≤bill (ξ.credit-1) s→(2*bill (5/8) s)*y≤bill ξ.credit s):=by
  let F:=(Rf).labels.level d
  let q:=leash F
  let b:=exam.arc
  let γ:=b*d+(q:ℝ)
  have hb:0<b:=by have :=exam.huge;dsimp only [b];linarith only [this,Nat.cast_nonneg (α:=ℝ) H]
  filter_upwards [(hat_rate (A) simple).eventually (Paint.absorb γ (γ+1) (by linarith) (2*2^q*F.coeffSize v)),
    (hat_rate (A) simple).eventually (Paint.absorb (5/8) 1 (by norm_num) 2)] with k cost absorb N p hk P g s ξ F' x
  have ratio:P.p.threshold/g=(Price.shrink Rf k N p)⁻¹:=by
    change P.p.threshold/_=(_/(A).clock.threshold k)⁻¹
    rw [inv_div,show P.p.threshold=(A).clock.threshold k from ((R.makes.wilson.represents N p k hk).vac) ▸ rfl];rfl
  let a:=Price.shrink Rf k N p
  have az:0<a:=Price.shrink_pos Rf R.makes hk p
  let m:=(A).clock.monitor k
  have m1 : 1 ≤ m := Real.one_le_exp (sq_nonneg _)
  let ρ:=mag (A) b k
  have hρ:1≤ρ:=Real.one_le_rpow m1 hb.le
  let B:ℝ:=2*m
  have lens (i):‖F.scaled a⁻¹ (Price.weightTag Rf d ρ v) i‖≤B^q*ρ^d*‖v i‖:=by
    unfold Price.weightTag;simp only [Frame.scaled_apply,LinearMap.coe_mk,AddHom.coe_mk,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr az).le _),Real.norm_of_nonneg (zero_le_one.trans hρ)]
    rw [←mul_assoc];apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul ((pow_le_pow_left₀ (inv_pos.mpr az).le (Price.shrink_min Rf R.makes hk p) _).trans
      (pow_le_pow_right₀ (show 1≤B by dsimp only [B];linarith only [m1]) (Finset.le_sup (f:=fun i=>(F.grades i).2) (Finset.mem_univ i))))
      (pow_le_pow_right₀ hρ (F.bound i)) (pow_nonneg (zero_le_one.trans hρ) _) (pow_nonneg (by dsimp only [B];linarith only [m1]) _)
  have sum:F.coeffSize (F.scaled a⁻¹ (Price.weightTag Rf d ρ v))≤B^q*ρ^d*F.coeffSize v:=by
    unfold Frame.coeffSize;rw [Finset.mul_sum];exact Finset.sum_le_sum fun i _=>lens i
  have horizon:(q:ℝ)≤H:=by
    have h:=Tapes.savings Rf d
    change (q:ℝ)+2≤(d:ℝ)+2 at h;linarith only [h,(show (d:ℝ)≤H by exact_mod_cast dH)]
  have spent:γ+1≤ξ.credit-1:=by
    have h:=exam.loose ((A).clock.J k)
    change b*(H:ℝ)+H+2≤ξ.credit at h
    dsimp only [γ];linarith only [h,horizon,mul_le_mul_of_nonneg_left (show (d:ℝ)≤H by exact_mod_cast dH) hb.le]
  refine ⟨?_,fun y hy=>?_⟩
  · change 2*F.coeffSize (F.scaled (P.p.threshold/g) (Price.weightTag Rf d (mag (A) ξ.band k) v))≤_
    rw [ratio,show ξ.band=b from exam.factor _]
    calc
      _ ≤ 2*(B^q*ρ^d*F.coeffSize v):=mul_le_mul_of_nonneg_left sum (by norm_num)
      _ = (2*2^q*F.coeffSize v)*bill γ s:=by
        dsimp only [B,ρ,γ];rw [mul_pow,show m=bill 1 s from fire_bill (A) k,mag_bill,bills,bills]
        rw [show clim (A) k=s from rfl,←overlap];ring_nf
      _ ≤ bill (γ+1) s:=cost
      _ ≤ _:=Glimmer.billed _ spent
  · apply (mul_le_mul_of_nonneg_left hy (mul_nonneg (by norm_num) (Real.exp_pos _).le)).trans
    calc
      _ ≤ bill 1 s*bill (ξ.credit-1) s:=mul_le_mul_of_nonneg_right absorb (Real.exp_pos _).le
      _ = _:=by rw [overlap,add_sub_cancel]

end YM.Integration.WilsonThermometerWeakDetectorStake
end
