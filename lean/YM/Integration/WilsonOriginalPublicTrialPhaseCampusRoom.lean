import YM.Integration.WilsonOriginalPublicTrialPhaseFlock
import YM.RG05Readout.Many.Preflight
import YM.Overlay.Prior

/-! The original stationary budget pays every all-copy renewal gap inside one true halo width. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCampusRoom
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Filter WilsonOriginalPublicTrialPhaseRay
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "β" => (A).clock.hatBeta
local notation "P" => (A).budget

theorem ribbon (simple:G.Simple)(stock:RG05Readout.Many.Storage (C) R.doors):
    ∀ᶠ i:ℕ in atTop,guard (C).S i (Bandage.renal (A) i)≤((P) i).B:=by
  filter_upwards [RG05Readout.Many.shifts stock simple,
    (Next.Rank.Station.hat_rate (A) simple).eventually (polestar 1 zero_le_one 5 0),
    (Next.Rank.Station.hat_rate (A) simple).eventually_ge_atTop (Real.exp 8)] with i hi paid hot
  let L:ℝ:=((C).S.block i).val
  let x:ℝ:=(β) i
  let y:ℝ:=(β) (i+1)
  let b:=((P) i).B
  have x1:1≤x:=(Real.one_le_exp (by norm_num : (0:ℝ)≤8)).trans hot
  have x0:0<x:=zero_lt_one.trans_le x1
  have y0:0<y:=zero_lt_one.trans ((A).fits.delayed (i+1))
  have l1:1≤L:=by
    change 1≤(((C).S.block i).val:ℝ)
    exact_mod_cast (show 1≤((C).S.block i).val from ((C).S.block i).property)
  have inv:(Doors.rate ((C).S.block i)*Bandage.renal (A) i)⁻¹=L^(2/5:ℝ)*y^2:=by
    unfold Doors.rate Bandage.renal Mallow.probe
    rw [Real.rpow_neg (zero_le_one.trans l1),Real.rpow_neg y0.le,Real.rpow_ofNat]
    simp [L,y,mul_comm]
  have lp:L^(2/5:ℝ)≤L:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le l1 (show (2/5:ℝ)≤1 by norm_num)
  have hcap:x^5≤Real.exp ((b:ℝ)/128):=by
    simp only [one_mul,add_zero] at paid
    exact paid
  have eight:(8:ℕ)≤b:=by
    have h0:Real.exp 8≤x^5:=hot.trans (le_self_pow₀ x1 (by norm_num))
    have k:=Real.exp_le_exp.mp (h0.trans hcap)
    exact_mod_cast (show (8:ℝ)≤(b:ℝ) by linarith)
  have amount:L^(2/5:ℝ)*y^2≤Real.exp ((b:ℝ)/128):=by
    calc
      _ ≤ x*(x^2)^2:=mul_le_mul (lp.trans hi.2.1) (pow_le_pow_left₀ y0.le hi.2.2 2) (sq_nonneg _) x0.le
      _ = x^5:=by ring
      _ ≤ _:=hcap
  unfold WilsonOriginalPublicTrialPhaseRay.guard
  refine max_le eight (Nat.ceil_le.mpr ?_)
  rw [inv]
  have t:Real.log (L^(2/5:ℝ)*y^2)≤(b:ℝ)/128:=(Real.log_le_iff_le_exp (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le l1) _) (sq_pos_of_pos y0))).mpr amount
  linarith

theorem opened (simple:G.Simple)(stock:RG05Readout.Many.Storage (C) R.doors)
    (tabs : Stock.Tabs (A)) (j : ℕ) : ∃ u, ∃ ju : j ≤ u, ∀ (m : ℕ) (um : u ≤ m) (per : ℕ)
      (o:Site ((C).side m per)), 4 * (pdist o : ℝ) ≤ (C).S.a j / (C).S.a m →
        pdist o+pdist o+((P) m).B*guard (C).S m (Bandage.renal (A) m)<
          ((C).S.toDepth (ju.trans um) per).count.val:=by
  obtain ⟨i,open₀⟩:=Stock.Tabs.mayOpen (A) 4 tabs j
  obtain ⟨k,late⟩:=eventually_atTop.mp (ribbon R simple stock)
  refine ⟨max k i,open₀.1.trans (le_max_right ..),?_⟩
  intro m hm per o here
  have im:=le_trans (le_max_right k i) hm
  have jm:=open₀.1.trans im
  have cash:=Stock.Tabs.open_later (A) 4 tabs open₀ im (by norm_num)
  let box:=(C).S.toDepth jm per
  have count:(box.count.val:ℝ)=(C).S.a j/(C).S.a m:=
    (eq_div_iff ((C).S.a_pos m).ne').mpr ((mul_comm ..).trans ((C).S.embeds_scale box))
  have cap:4*(((P) m).B:ℝ)^2≤(box.count.val:ℝ):=by rw [count];exact cash.2
  have here':4*(pdist o:ℝ)≤(box.count.val:ℝ):=by rwa [count]
  have positive:0<(box.count.val:ℝ):=by exact_mod_cast box.count.pos
  have gap:(((P) m).B:ℝ)*(guard (C).S m (Bandage.renal (A) m):ℝ)≤(((P) m).B:ℝ)^2:=by
    rw [pow_two]
    gcongr
    exact_mod_cast late m ((le_max_left k i).trans hm)
  exact_mod_cast (show (pdist o:ℝ)+pdist o+((P) m).B*(guard (C).S m (Bandage.renal (A) m):ℝ)<(box.count.val:ℝ) by linarith)

end YM.Integration.WilsonOriginalPublicTrialPhaseCampusRoom
end
