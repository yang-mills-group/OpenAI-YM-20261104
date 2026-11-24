import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyStageFare
import YM.Integration.WilsonOriginalPublicTrialPhaseLocated

/-! The normalized pre-capture address and its true original ride on a common currency. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyPaidAddress
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramBlockedTrialAddBack
open RG05Readout RG05Readout.Address Offsets
open Extra.Multi MergeProof.Ribbons
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G)
variable {m N per:ℕ}{T:Campaign R}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "S" => (C).path
local notation "P" => (S).rep N per (m+1)
local notation "Q" => (S).rep N per m
local notation "O" => (S).levels.clock.op m per


open ProjectorNext.Equivariance RG05Readout.View


private theorem price (L c β α x r B:ℝ) (d:ℕ) (lo:2≤L) (cl:c≤L)
    (bl:β≤L) (al:α≤1) (xp:0≤x) (xb:x≤B) (rp:0≤r) (rb:r≤B):
    L^d*c*x+α*r≤L^(d+4)*B ∧ (1+L^d*c+β)*x+(2+α)*r≤L^(d+4)*B:=by
  have l1:1≤L:=by linarith only [lo]
  have lp:0≤L:=zero_le_one.trans l1
  have lq:1≤L^d:=one_le_pow₀ l1
  have lq0:=zero_le_one.trans lq
  let U:=L^d*L
  have ul:L≤U:=le_mul_of_one_le_left lp lq
  have ou:=l1.trans ul
  have ell:L^d*c≤U:=mul_le_mul_of_nonneg_left cl lq0
  have b0:=xp.trans xb
  have block:6*U≤L^(d+4):=by
    simp only [U,show d+4=d+1+3 by omega,pow_add,pow_one]
    have gain:(2:ℝ)^3≤L^3:=by gcongr
    norm_num at gain
    nlinarith only [mul_nonneg (mul_nonneg lq0 lp) (show 0≤L^3-6 by linarith only [gain])]
  have pre :L^d*c*x≤U*B:=mul_le_mul ell xb xp (zero_le_one.trans ou)
  have old :α*r≤U*B:=mul_le_mul (al.trans ou) rb rp (zero_le_one.trans ou)
  have cfee:(1+L^d*c+β)*x≤(3*U)*B:=mul_le_mul (by linarith only [ou,ell,bl.trans ul]) xb xp (by linarith only [ou])
  have ofee:(2+α)*r≤(3*U)*B:=mul_le_mul (by linarith only [ou,al]) rb rp (by linarith only [ou])
  have cap:=mul_le_mul_of_nonneg_right block b0
  constructor <;> nlinarith only [pre,old,cfee,ofee,cap,mul_nonneg (zero_le_one.trans ou) b0]

set_option maxHeartbeats 700000 in
theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors) (d:ℕ):
    ∀ᶠ m:ℕ in Filter.atTop, ∀ N per:ℕ,∀ live:m<N,
    ∀ o:Site ((C).side (m+1) per),∀ q:Coefficient ((C).labels.level d) ((C).side (m+1) per),
    ∀ r B:ℝ, 0≤r  → r≤B → ((C).labels.level d).coeffSize q.x≤B  → 
    q.Format o (C).params ((S).rep N per (m+1))  → 
    q.remBound o ((S).rep N per (m+1)) (Push.Local.kappa (S) (m+1)) r  → 
    let b:=((S).levels.clock.op m per).ratio.parent o
    let L:=((C).S.block m).val
    let bill:=(L:ℝ)^(d+4)*B
    ∃ k:Coefficient ((C).labels.level d) ((C).side m per), k.Format b (C).params ((S).rep N per m) ∧
      k.remBound b ((S).rep N per m) (Push.Local.kappa (S) m) bill ∧
      ((C).labels.level d).coeffSize k.x≤bill ∧
      Ride ((S).levels.clock.op m per) o b (R.doors N per m live) ((L:ℂ)^d)
        (invoice q o ((C).localSection d) ((S).rep N per (m+1)))
        (invoice k b ((C).localSection d) ((S).rep N per m)) bill:=by
  filter_upwards [WilsonMeasuredPublicEntranceTransferCopyStageFare.original R simple shop d,
    (A).fits.deep.eventually_ge_atTop (d+3)] with m paid grade N per live o q r B rp rb xb fmt rem
  have hit:Push.Local.hitWidth ((S).rep N per m).p*Push.Local.kappa (S) m≤1:=
    (R.makes.wilson.represents N per m live.le).vac.symm ▸ RG05Readout.UV.stalls R.b m
  have fine:Push.Local.kappa (S) (m+1)≤1:=
    (le_mul_of_one_le_left (Real.sqrt_nonneg _) (Push.Local.width_one_le ((A).budget (m+1)))).trans
      (RG05Readout.UV.stalls R.b (m+1))
  obtain ⟨k,kf,kr,kx,ride⟩:=WilsonOriginalPublicTrialPhaseLocated.original R simple shop stock live d grade o q hit fine r fmt rem
  have large:(2:ℝ)≤((C).S.block m).val:=by exact_mod_cast ((by decide:2≤3).trans ((C).S.block_large m))
  have lo:1≤(((C).S.block m).val:ℝ):=by linarith only [large]
  have al:Doors.rate ((C).S.block m)≤1:=Real.rpow_le_one_of_one_le_of_nonpos lo (by norm_num)
  have cost:=price _ _ _ _ _ _ _ d large paid.2.1 paid.2.2.2 al
    (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) xb rp rb
  exact ⟨k,kf,rem_mono kr cost.1,kx.trans cost.1,ride.cost cost.2⟩

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyPaidAddress
