import YM.Integration.WilsonCapturedPrimaryWardRoute
import YM.Integration.WilsonThermometerOwnOffsetField

/-! Retiming an engineering-normalized addressed source on one original track. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardRetimed
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical OPE MergeProof Push Local Extra.Trajectories
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address Copper
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {D:Rail C} {B:ℕ→ℕ→ℝ} {N p d k m j:ℕ} {h:C.Makes}
    {sites:∀i,Bud C p i} {V:Sight C d p} {r:Emblems C d}

def ratio (C:Family G) (i j d:ℕ):ℂ:=((C.S.a i/C.S.a j:ℝ):ℂ)^d

theorem cancel (i j d:ℕ):((C.S.a j:ℝ):ℂ)^d*ratio C i j d=((C.S.a i:ℝ):ℂ)^d:=by
  unfold ratio
  rw [Complex.ofReal_div,div_pow]
  field_simp [(C.S.a_pos j).ne']

theorem norm_ratio (i j d:ℕ):‖ratio C i j d‖=(C.S.a i/C.S.a j)^d:=by
  rw [ratio,norm_pow,Complex.norm_real,Real.norm_of_nonneg (div_pos (C.S.a_pos i) (C.S.a_pos j)).le]

def lift (r:Emblems C d) (hk:k ≤ m) (y:Palette C d):Palette C d:=ratio C k m d • finer r hk y

def descend (r:Emblems C d) (mk:m ≤ k) (y:Palette C d):Palette C d:=ratio C k m d • (finer r mk).symm y

def reading (r:Emblems C d) (upper:m ≤ N) (y:Palette C d):C.label d:=
  (C.S.a m:ℂ)^d • (C.factory d N p).terminal (finer r upper y (primaryLetter d))

theorem lift_read (km:k ≤ m) (mn:m ≤ N) (y:Palette C d):
    reading (p:=p) r mn (lift r km y)=reading (p:=p) r (km.trans mn) y:=by
  simp only [reading,lift,Many.sumwalk r km mn,LinearEquiv.trans_apply,map_smul,Pi.smul_apply]
  apply (congrArg (fun u:C.label d=>((C.S.a m:ℂ)^d) • u)
    ((C.factory d N p).terminal.map_smul (ratio C k m d) _)).trans
  rw [smul_smul,cancel]

theorem descend_read (mk:m ≤ k) (kn:k ≤ N) (y:Palette C d):
    reading (p:=p) r (mk.trans kn) (descend r mk y)=reading (p:=p) r kn y:=by
  simp only [reading,descend,Many.sumwalk r mk kn,LinearEquiv.trans_apply,map_smul,Pi.smul_apply,
    LinearEquiv.apply_symm_apply]
  apply (congrArg (fun u:C.label d=>((C.S.a m:ℂ)^d) • u)
    ((C.factory d N p).terminal.map_smul (ratio C k m d) _)).trans
  rw [smul_smul,cancel]

private theorem block (m j:ℕ):C.S.a m/C.S.a (j+1)=(C.S.a m/C.S.a j)*(C.S.block j).val:=by
  rw [C.S.a_step]
  field_simp [(C.S.a_pos j).ne',(show ((C.S.block j).val:ℝ)≠0 by exact_mod_cast (C.S.block j).property.ne')]

theorem down {beg:ℕ} (t:Enrolled h D B beg N p d sites V r) (begun:beg ≤ m) (mj:m ≤ j) (jn:j ≤ N) (y:Palette C d):
    size ((finer r mj).symm y) ≤ stringCost C mj*(C.S.a m/C.S.a j)^d*size y:=by
  induction j,mj using Nat.le_induction generalizing y with
  | base=>simp [base_value,string_base,(C.S.a_pos m).ne']
  | succ j mj ih=>
    have one:=((t.follows j (begun.trans mj) jn).payment y).2
    have fee:=one.trans (mul_le_mul_of_nonneg_left (size_tuned (C.S.block j) y) (zero_le_one.trans (lamp_nn (C:=C) j)))
    have earlier:=ih (j.le_succ.trans jn) (r j y)
    rw [finer_next mj]
    change size ((finer r mj).symm (r j y)) ≤ _
    rw [string_next mj,block m j,mul_pow]
    refine earlier.trans ((mul_le_mul_of_nonneg_left fee ?_).trans_eq ?_)
    · exact mul_nonneg (zero_le_one.trans (Many.stampCosts mj)) (pow_nonneg (div_pos (C.S.a_pos m) (C.S.a_pos j)).le _)
    · ring

theorem lift_price {beg:ℕ} (t:Enrolled h D B beg N p d sites V r) (begun:beg ≤ k) (km:k ≤ m) (mn:m ≤ N) (y:Palette C d):
    size (lift r km y) ≤ (C.S.a k/C.S.a m)^d*stringCost C km*size y:=by
  rw [lift,size_smul,norm_ratio,mul_assoc]
  exact mul_le_mul_of_nonneg_left (t.inverse begun km mn y) (pow_nonneg (div_pos (C.S.a_pos _) (C.S.a_pos _)).le _)

theorem descend_price {beg:ℕ} (t:Enrolled h D B beg N p d sites V r) (begun:beg ≤ m) (mk:m ≤ k) (kn:k ≤ N) (y:Palette C d):
    size (descend r mk y) ≤ stringCost C mk*size y:=by
  rw [descend,size_smul,norm_ratio]
  refine (mul_le_mul_of_nonneg_left (down t begun mk kn y) (pow_nonneg (div_pos (C.S.a_pos _) (C.S.a_pos _)).le _)).trans_eq ?_
  have cancel:(C.S.a k/C.S.a m)^d*(C.S.a m/C.S.a k)^d=1:=by
    rw [←mul_pow];field_simp [(C.S.a_pos k).ne',(C.S.a_pos m).ne'];exact one_pow _
  calc
    _ = ((C.S.a k/C.S.a m)^d*(C.S.a m/C.S.a k)^d)*(stringCost C mk*size y):=by ring
    _ = _:=by rw [cancel,one_mul]

theorem cash (C:Family G):∀ᶠ m:ℕ in atTop,∀j (h:m ≤ j),stringCost C h ≤ C.S.a m/C.S.a j:=by
  filter_upwards [string_paid (C:=C) zero_lt_one] with m fee j hj
  apply (fee j hj).trans_eq
  rw [one_mul,Real.exp_sub,Schedule.scale,Schedule.scale,Real.exp_log (inv_pos.mpr (C.S.a_pos j)),
    Real.exp_log (inv_pos.mpr (C.S.a_pos m)),inv_div_inv]

end YM.Integration.WilsonCapturedPrimaryWardRetimed
