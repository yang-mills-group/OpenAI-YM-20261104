import YM.Integration.WilsonPositionProgramArithmetic
import YM.Integration.WilsonPositionProgramCommonWindow
import YM.Integration.WilsonPositionProgramInversion
import YM.Integration.WilsonPositionProgramInfraredBlocks
import YM.Integration.WilsonPositionProgramInfraredWindow
import YM.Integration.WilsonPositionProgramSubmittedDates
import YM.Integration.WilsonPositionProgramReporterBand

/-! The original position construction on a run with the two arithmetic receipts.
The same native blocks, circuits, prescriptions and tests are retained in each publication. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticCommonWindow
open WilsonPositionProgramCommonWindow
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Run G) {simple : G.Simple} {a : Axis} {ε : ℝ}

/- The selected physical run's actual blocks inherit the pre-period choice. -/
theorem blocks (purchase : WilsonPositionProgramArithmetic.divides simple a ε C.kit) (d : ℕ)
    (hd : 0 < d) : ∀ᶠ m in atTop, ∃ u : ℕ, C.family.S.block m = ((3:Side)^d)^u := by
  have h := WilsonPositionProgramLengths.eventual purchase hd
  have dates := C.alloy.B.a.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [dates.eventually h] with m hm
  obtain ⟨u,hu⟩ := hm
  exact ⟨u,(block_eq C.alloy.B.valid m).trans hu⟩

variable (D : XSpace.Run)
/- At a sufficiently fine reporter each actual finer block has an integer exponent in the given fixed regulator. -/
theorem dates (purchase : WilsonPositionProgramArithmetic.divides simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (hr : D.ratio = 3^d) : ∀ᶠ m in atTop, ∃ w : ℕ → ℕ,
      ∀ j : ℕ, (C.family.S.block (m+j)).val = D.ratio ^ w j := by
  obtain ⟨m₀,all⟩ := eventually_atTop.1 (blocks C purchase d hd)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  have each (j : ℕ) := all (m+j) (hm.trans (Nat.le_add_right m j))
  choose w hw using each
  refine ⟨w,fun j => ?_⟩
  rw [hw,hr,PNat.pow_coe,PNat.pow_coe]
  rfl
/- These are the successive original dates after the reporting site, expressed in the one fixed-block grid. -/
/- At fixed top `j`, reproduce every actual physical block ratio on the auxiliary period. -/
/- Exactly the fixed regulator's deployed fine spacing, retaining both actual physical dates. -/
end YM.Integration.WilsonPositionProgramArithmeticCommonWindow
end

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticInversion
open WilsonPositionProgramInversion
open Filter Lattice RG PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow
open scoped BigOperators Topology
variable {G : Gauge} (C : Run G) (simple : G.Simple) (D : XSpace.Run) {a : Axis} {ε : ℝ}
local notation "A" => C.family.path.levels
local notation "Λ" => RG16.Lambda A
local notation "β" => C.family.path.levels.clock.hatBeta

include simple in
private theorem allowance : ∀ᶠ m in atTop, (Λ m)^((3:ℝ)/2) ≤ β m := by
  let x := WilsonAdmissionScale.logarithm A
  have hx : Tendsto x atTop atTop := WilsonAdmissionScale.logarithm_tendsto A simple
  have small := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hx
  have bound : ∀ᶠ m in atTop, (x m)^2*Real.exp (-(x m)) < 1/4 :=
    small.eventually_lt_const (by norm_num)
  filter_upwards [hx.eventually_ge_atTop 2,bound] with m large low
  have pos : 0 < β m := zero_lt_one.trans (C.family.path.levels.fits.delayed m)
  change x m ^ 2 * Real.exp (-Real.log (β m)) < _ at low
  rw [Real.exp_neg,Real.exp_log pos,←div_eq_mul_inv,div_lt_iff₀ pos] at low
  have big : 1 ≤ 2+x m := by linarith
  calc (Λ m)^((3:ℝ)/2) ≤ (2+x m)^((2:ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le big (by norm_num)
    _ = (2+x m)^2 := Real.rpow_natCast ..
    _ ≤ β m := by nlinarith [sq_nonneg (x m-2),mul_nonneg (by linarith : 0 ≤ x m-2) (by linarith : 0 ≤ x m+2)]
/- The independent fine-date parameter and the admissible native period are chosen from the
actual variable blocks. Its inverse spacing has the manuscript's three-halves logarithmic order. -/
theorem chosen (purchase : WilsonPositionProgramArithmetic.divides simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (hr : D.ratio = 3^d)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) :
    ∀ᶠ m in atTop, ∃ (w : ℕ → ℕ) (j : ℕ), 0 < j ∧
      (∀ k, (C.family.S.block (m+k)).val = D.ratio^w k) ∧
      C.family.S.a (m+j) / C.family.S.a m = (D.step (elapsed w j)).spacing ∧
      Λ m ^ ((3:ℝ)/2) ≤ (elapsed w j : ℝ)*Real.log D.ratio ∧
      (elapsed w j : ℝ)*Real.log D.ratio ≤ Λ m ^ ((3:ℝ)/2) + 2*Λ m := by
  let x := WilsonAdmissionScale.logarithm A
  have hx : Tendsto x atTop atTop := WilsonAdmissionScale.logarithm_tendsto A simple
  have slope := Gauge.slopeConstant_pos simple
  filter_upwards [WilsonPositionProgramArithmeticCommonWindow.dates C D purchase hd hr,allowance C simple,
    hx.eventually_ge_atTop (Real.log (1+G.slopeConstant))] with m eligible capped large
  obtain ⟨w,paid⟩ := eligible
  let need := (Λ m)^((3:ℝ)/2)
  have pos : 0 < Λ m := by
    exact add_pos (by norm_num) (WilsonAdmissionScale.logarithm_pos A m)
  have existsDate : ∃ j : ℕ, need ≤ C.family.S.scale (m+j) - C.family.S.scale m := by
    have go : Tendsto (fun j : ℕ => m+j) atTop atTop :=
      tendsto_atTop_mono (fun j => Nat.le_add_left j m) tendsto_id
    obtain ⟨j,hj⟩ := ((C.family.S.divergent.comp go).eventually_ge_atTop (C.family.S.scale m + need)).exists
    exact ⟨j,by change _ ≤ C.family.S.scale (m+j) at hj; linarith⟩
  let j := Nat.find existsDate
  have reaches : need ≤ C.family.S.scale (m+j)-C.family.S.scale m := Nat.find_spec existsDate
  have positive : 0 < j := by
    by_contra! hn
    rw [Nat.le_zero.mp hn,Nat.add_zero,sub_self] at reaches
    exact (Real.rpow_pos_of_pos pos _).not_ge reaches
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  have before : C.family.S.scale (m+k)-C.family.S.scale m < need :=
    lt_of_not_ge (Nat.find_min existsDate (show k < j by omega))
  have price : β (m+k) ≤ (1+G.slopeConstant) * β m := by
    have shift : β (m+k)-β m = G.slopeConstant * (C.family.S.scale (m+k)-C.family.S.scale m) := by
      unfold RG.Calendar.hatBeta
      ring
    have xpay := mul_le_mul_of_nonneg_left (before.le.trans capped) slope.le
    nlinarith
  have bpos : 0 < β m := zero_lt_one.trans (C.family.path.levels.fits.delayed m)
  have logpay := Real.log_le_log (zero_lt_one.trans (C.family.path.levels.fits.delayed (m+k))) price
  rw [Real.log_mul (by linarith : (1+G.slopeConstant:ℝ) ≠ 0) bpos.ne'] at logpay
  have lap : Real.log ((C.family.S.block (m+k)).val:ℝ) ≤ 2 * Λ m := by
    have v₁ := Real.log_le_sub_one_of_pos (by exact_mod_cast (C.family.S.block (m+k)).property : 0 < ((C.family.S.block (m+k)).val:ℝ))
    have v₂ := Real.log_le_sub_one_of_pos (add_pos (by norm_num : (0:ℝ)<2) (WilsonAdmissionScale.logarithm_pos A (m+k)))
    have budget := pace (m+k)
    change Real.log (1+G.slopeConstant) ≤ Real.log (β m) at large
    change Real.log (2+Real.log (β (m+k))) ≤ 2+Real.log (β (m+k))-1 at v₂
    change _ ≤ Real.log (2+Real.log (β (m+k))) at budget
    change _ ≤ 2*(2+Real.log (β m))
    linarith
  refine ⟨w,j,positive,paid,fine_spacing C D m w paid j,?_,?_⟩
  · exact (logged C D m w paid j) ▸ reaches
  · rw [←logged C D m w paid j,hk]
    change C.family.S.scale ((m+k)+1)-C.family.S.scale m ≤ need + 2*Λ m
    rw [C.family.S.scale_succ]
    linarith

end YM.Integration.WilsonPositionProgramArithmeticInversion
end

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticInfraredBlocks
open WilsonPositionProgramInfraredBlocks
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler WilsonPositionProgramCommonWindow
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {simple : G.Simple} {a : Axis} {ε : ℝ}

/- Above one finite date every consecutive authentic exponent divides all its successors. -/
theorem nested (purchase : WilsonPositionProgramArithmetic.course simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (ratio : D.ratio=(3:ℕ)^d) : ∃ start : ℕ, ∃ w : ℕ → ℕ,
      (∀ k, (C.family.S.block (start+k)).val=D.ratio^(w k)) ∧ ∀ k l, k ≤ l → w k ∣ w l := by
  obtain ⟨h,mono,lengths⟩ := purchase.1
  obtain ⟨start,active⟩ := eventually_atTop.mp (C.alloy.B.a.fits.deep.eventually (eventually_ge_atTop d))
  let index := fun k => C.alloy.B.a.clock.J (start+k+1)
  have divid (k : ℕ) : d ∣ (h (index k)).factorial := Nat.dvd_factorial hd
    ((active _ (by change start ≤ start+k+1; omega)).trans
      ((Nat.le_succ (index k)).trans (lengths _).1))
  choose w hw using divid
  refine ⟨start,w,fun k => ?_,fun k l hkl => ?_⟩
  · have step : C.family.S.block (start+k)=(3:Side)^(h (index k)).factorial :=
      (block_eq C.alloy.B.valid _).trans (lengths _).2
    rw [step,PNat.pow_coe,show (3:Side).val=3 from rfl,hw,ratio,pow_mul]
  · have hle : index k ≤ index l := C.alloy.B.a.fits.mono (by omega)
    obtain ⟨q,hq⟩ := Nat.factorial_dvd_factorial (mono hle)
    rw [hw,hw,Nat.mul_assoc] at hq
    exact ⟨q,Nat.eq_of_mul_eq_mul_left hd hq⟩

/- If the remaining exponent fits below this date, the backwards crossing is exact. -/
end YM.Integration.WilsonPositionProgramArithmeticInfraredBlocks
end

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticInfraredWindow
open WilsonPositionProgramInfraredWindow
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler WilsonPositionProgramCommonWindow
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Run G) (simple : G.Simple) (D : XSpace.Run) {a : Axis} {ε : ℝ}
local notation "Λ" => RG16.Lambda C.family.path.levels
private theorem uniform (L : ℝ) (hL : 0 < L) (v : ℕ) (ell : ℝ) (h : 1 ≤ ell) (i : ℕ)
    (upper : (i:ℝ)*L ≤ ell^((3:ℝ)/2)+2*ell) :
    (v*i*i:ℕ) ≤ (v:ℝ)*(3/L)^2*ell^4 := by
  have sq : ell^((3:ℝ)/2) ≤ ell^2 := by
    rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
  have base : ell ≤ ell^2 := by nlinarith only [mul_nonneg (zero_le_one.trans h) (sub_nonneg.mpr h)]
  have cnt : (i:ℝ) ≤ (3/L)*ell^2 := by
    apply (le_div_iff₀ hL).2 at upper
    calc _ ≤ (ell^((3:ℝ)/2)+2*ell)/L := upper
         _ ≤ (3*ell^2)/L := by apply div_le_div_of_nonneg_right _ hL.le; linarith
         _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg i) cnt 2) (Nat.cast_nonneg v)
  push_cast
  nlinarith only [hs]

/- All prices use this single index. The physical infrared date is exact as well as the top. -/
theorem chosen (purchase : WilsonPositionProgramArithmetic.course simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (ratio : D.ratio=(3:ℕ)^d) (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) :
    ∃ start : ℕ, ∃ w : ℕ → ℕ, (∀ k, (C.family.S.block (start+k)).val=D.ratio^(w k)) ∧
      ∀ᶠ n in atTop, ∃ b ≤ n, ∃ j > 0, let i := elapsed (next w n) j
        C.family.S.a ((start+n)+j)/C.family.S.a (start+n)=(D.step i).spacing ∧
        Λ (start+n)^((3:ℝ)/2) ≤ (i:ℝ)*Real.log D.ratio ∧
        (i:ℝ)*Real.log D.ratio ≤ Λ (start+n)^((3:ℝ)/2)+2*Λ (start+n) ∧
        elapsed w b + D.reserve*i*i = elapsed w n ∧
        elapsed (next w b) (n+j-b)=D.reserve*i*i+i := by
  obtain ⟨start,w,stamps,dv⟩ := WilsonPositionProgramArithmeticInfraredBlocks.nested C D purchase hd ratio
  refine ⟨start,w,stamps,?_⟩
  have grow : Tendsto (fun n : ℕ => start+n) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left n start) tendsto_id
  let L := Real.log D.ratio
  have hp : 1 < D.ratio := lt_of_lt_of_le (by decide) D.large
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp)
  have top := grow.eventually (WilsonPositionProgramArithmeticInversion.chosen C simple D
    (WilsonPositionProgramArithmetic.prior purchase) hd ratio pace)
  have room := WilsonPositionProgramInfraredRoom.capacity C simple D start w stamps ((D.reserve:ℝ)*(3/L)^2) 4
  filter_upwards [top,room] with n top enough
  obtain ⟨weights,j,jpos,file,_,low,high⟩ := top
  have increasing : StrictMono fun k : ℕ => D.ratio^k := strictMono_nat_of_lt_succ fun k => by
    rw [pow_succ]; exact lt_mul_of_one_lt_right (pow_pos (Nat.zero_lt_of_lt hp) _) hp
  have same : weights=next w n := by
    funext k
    apply increasing.injective
    exact (file k).symm.trans (by simpa only [next,Nat.add_assoc] using stamps (n+k))
  subst weights
  let i := elapsed (next w n) j
  have big : 1 ≤ Λ (start+n) := by
    have pos := WilsonAdmissionScale.logarithm_pos C.family.path.levels (start+n)
    change 1 ≤ 2+Real.log _
    change 0 < Real.log _ at pos
    linarith
  have available : D.reserve*i*i ≤ elapsed w n := by
    exact_mod_cast (uniform L hL D.reserve (Λ (start+n)) big i high).trans enough
  have portions (k : ℕ) (hk : k < n) : w k ∣ D.reserve*i*i := by
    have hi : w k ∣ i := Finset.dvd_sum fun l _ => dv k (n+l) (by omega)
    exact dvd_mul_of_dvd_right hi _
  obtain ⟨b,hb,till⟩ := WilsonPositionProgramInfraredBlocks.close w dv n _ available portions
  have actual (k : ℕ) : (C.family.S.block ((start+n)+k)).val=D.ratio^(next w n k) := by
    simpa only [next,Nat.add_assoc] using stamps (n+k)
  refine ⟨b,hb,j,jpos,fine_spacing C D _ _ actual j,low,high,till,?_⟩
  have both := append w b (n+j-b)
  rw [show b+(n+j-b)=n+j by omega,append w n j] at both
  change elapsed w n+i=elapsed w b+elapsed (next w b) (n+j-b) at both
  change elapsed (next w b) (n+j-b)=D.reserve*i*i+i
  exact Nat.add_left_cancel (calc
    elapsed w b+elapsed (next w b) (n+j-b) = elapsed w n+i := both.symm
    _ = elapsed w b+(D.reserve*i*i+i) := by rw [←till,Nat.add_assoc])

end YM.Integration.WilsonPositionProgramArithmeticInfraredWindow
end

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticSubmittedDates
open WilsonPositionProgramSubmittedDates
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow WilsonPositionProgramInfraredWindow
variable {G : Gauge} (C : Run G) (D : XSpace.Run) (simple : G.Simple)
local notation "Λ" => RG16.Lambda C.family.path.levels
local notation "β" => C.family.path.levels.clock.hatBeta

private theorem uniform (L : ℝ) (hL : 0 < L) (v : ℕ) (ell : ℝ) (h : 1  ≤  ell) (i : ℕ)
    (upper : (i:ℝ)*L  ≤  ell^((3:ℝ)/2)+2*ell) :
    (v*i*i:ℕ)  ≤  (v:ℝ)*(3/L)^2*ell^4 := by
  have sq : ell^((3:ℝ)/2)  ≤  ell^2 := by
    rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
  have base : ell  ≤  ell^2 := by nlinarith only [mul_nonneg (zero_le_one.trans h) (sub_nonneg.mpr h)]
  have cnt : (i:ℝ)  ≤  (3/L)*ell^2 := by
    apply (le_div_iff₀ hL).2 at upper
    calc _  ≤  (ell^((3:ℝ)/2)+2*ell)/L := upper
         _  ≤  (3*ell^2)/L := by apply div_le_div_of_nonneg_right _ hL.le; linarith
         _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg i) cnt 2) (Nat.cast_nonneg v)
  push_cast
  nlinarith only [hs]

include simple in
private theorem timely (start : ℕ) (w : ℕ → ℕ) (blocks : ∀ t,
    (C.family.S.block (start+t)).val=D.ratio^(w t)) (stage fine : ℕ) :
    ∀ᶠ n in atTop, ∀ b i : ℕ, b ≤ n →
      Λ (start+n)^((3:ℝ)/2)  ≤  (i:ℝ)*Real.log D.ratio →
      (i:ℝ)*Real.log D.ratio  ≤  Λ (start+n)^((3:ℝ)/2)+2*Λ (start+n) →
      elapsed w b + D.reserve*i*i=elapsed w n →
      stage ≤ start+b ∧ fine  ≤  i ∧ 1 ≤ β (start+b) ∧ Λ (start+b)  ≤  (i:ℝ)*Real.log D.ratio := by
  let l := Real.log (D.ratio:ℝ)
  let K := (D.reserve:ℝ)*(3/l)^2
  let B := (elapsed w stage:ℝ)
  have L : 0<l := Real.log_pos (by exact_mod_cast (show 1<D.ratio from (by decide : 1<3).trans_le D.large))
  have rise := WilsonPositionProgramInfraredRoom.capacity C simple D start w blocks (K+B+1) 4
  have shift : Tendsto (fun n:ℕ => start+n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n start) tendsto_id
  have enough := ((RG16.Literal.lambda_leads C.family simple).comp shift).eventually_ge_atTop ((fine:ℝ)*l)
  filter_upwards [rise,enough] with n room weight
  intro b i hb lo hi stock
  have ell : 1 ≤ Λ (start+n) := by
    have pos := (C.family.path.levels.fits.delayed (start+n)).le
    change 1 ≤ 2+Real.log (β (start+n));linarith [Real.log_nonneg pos]
  have one : (1:ℝ) ≤ (Λ (start+n))^4 := one_le_pow₀ ell
  have bound := uniform l L D.reserve (Λ (start+n)) ell i hi
  change (D.reserve*i*i:ℕ)  ≤  K*(Λ (start+n))^4 at bound
  have coarse : stage ≤ start+b := by
    by_contra h
    have before : b ≤ stage := by omega
    have cmp : elapsed w b ≤ elapsed w stage := Finset.sum_le_sum_of_subset (Finset.range_mono before)
    have cmpR : (elapsed w b:ℝ) ≤ B := by dsimp only [B]; exact_mod_cast cmp
    have eqR := congrArg (fun k:ℕ => (k:ℝ)) (show elapsed w b+D.reserve*i*i=elapsed w n from stock)
    push_cast at eqR bound
    have b0 : 0 ≤ B := by positivity
    nlinarith only [room,bound,eqR,cmpR,one,mul_nonneg b0 (sub_nonneg.mpr one)]
  have elo : Λ (start+n)  ≤  Λ (start+n)^((3:ℝ)/2) := by
    calc _ = Λ (start+n)^(1:ℝ) := (Real.rpow_one _).symm
         _  ≤  _ := Real.rpow_le_rpow_of_exponent_le ell (by norm_num)
  have age := (RG16.Literal.lambda_mono C.family simple).monotone (Nat.add_le_add_left hb start)
  refine ⟨coarse, ?_,(C.family.path.levels.fits.delayed _).le,age.trans (elo.trans lo)⟩
  exact_mod_cast (le_of_mul_le_mul_right (weight.trans (elo.trans lo)) L)

include simple in
/- Every pre-elected local resource and every subsequently required numerical error threshold
applies on the very same constant-block re-expression of the actual variable Wilson dates. -/
theorem original {a : Axis} {ε : ℝ} (purchase : WilsonPositionProgramArithmetic.course simple a ε C.kit) {d : ℕ}
    (hd : 0<d) (ratio : D.ratio=(3:ℕ)^d) (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) :
    ∃ start : ℕ, ∃ w : ℕ→ℕ, (∀ k, (C.family.S.block (start+k)).val=D.ratio^(w k)) ∧
      ∀ stage fine : ℕ, ∀ᶠ n in atTop, ∃ b ≤ n, ∃ j>0, let i := elapsed (next w n) j
        stage ≤ start+b ∧ fine  ≤  i ∧ 1 ≤ β (start+b) ∧ Λ (start+b) ≤ (i:ℝ)*Real.log D.ratio ∧
        C.family.S.a ((start+n)+j)/C.family.S.a (start+n)=(D.step i).spacing ∧
        Λ (start+n)^((3:ℝ)/2)  ≤  (i:ℝ)*Real.log D.ratio ∧
        (i:ℝ)*Real.log D.ratio  ≤  Λ (start+n)^((3:ℝ)/2)+2*Λ (start+n) ∧
        elapsed w b+D.reserve*i*i=elapsed w n ∧ elapsed (next w b) (n+j-b)=D.reserve*i*i+i := by
  obtain ⟨start,w,blocks,dates⟩ := WilsonPositionProgramArithmeticInfraredWindow.chosen C D (simple:=simple) purchase hd ratio pace
  refine ⟨start,w,blocks,fun stage fine => ?_⟩
  filter_upwards [dates,timely C D simple start w blocks stage fine] with n choose due
  obtain ⟨b,hb,j,hj,spacing,lo,hi,eq,full⟩ := choose
  obtain ⟨age,index,initial,meter⟩ := due b _ hb lo hi eq
  exact ⟨b,hb,j,hj,age,index,initial,meter,spacing,lo,hi,eq,full⟩

end YM.Integration.WilsonPositionProgramArithmeticSubmittedDates
end

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticReporterBand
open WilsonPositionProgramReporterBand
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow WilsonPositionProgramInfraredWindow
open private timely from YM.Integration.WilsonPositionProgramSubmittedDates
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
local notation "Λ" => RG16.Lambda C.family.path.levels
local notation "β" => C.family.path.levels.clock.hatBeta
theorem original (simple : G.Simple) {a : Axis} {ε : ℝ}
    (purchase : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    {d : ℕ} (hd : 0 < d) (ratio : D.ratio=(3:ℕ)^d)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) (stage : ℕ) :
    Nonempty (Band C D stage) := by
  obtain ⟨start,w,clock,dates⟩ := WilsonPositionProgramArithmeticSubmittedDates.original C D simple purchase hd ratio pace
  obtain ⟨n₀,later⟩ := eventually_atTop.mp (dates stage 0)
  let n := fun t : ℕ => n₀+t
  let I := fun t j => elapsed (next w (n t)) j
  have chooseDate (t : ℕ) : ∃ b j, b ≤ n t ∧ 0<j ∧ stage ≤ start+b ∧
      1≤β (start+b) ∧ Λ (start+b)≤(I t j:ℝ)*Real.log D.ratio ∧
      C.family.S.a (start+n t+j)/C.family.S.a (start+n t)=(D.step (I t j)).spacing ∧
      Λ (start+n t)^((3:ℝ)/2) ≤ (I t j:ℝ)*Real.log D.ratio ∧
      (I t j:ℝ)*Real.log D.ratio ≤ Λ (start+n t)^((3:ℝ)/2)+2*Λ (start+n t) ∧
      elapsed w b+D.reserve*(I t j)*(I t j)=elapsed w (n t) ∧
      elapsed (next w b) (n t+j-b)=D.reserve*(I t j)*(I t j)+I t j := by
    obtain ⟨b,hb,j,hj,st,_,β₀,bill,space,lo,hi,before,reached⟩ :=
      later (n t) (Nat.le_add_right n₀ t)
    exact ⟨b,j,hb,hj,st,β₀,bill,space,lo,hi,before,reached⟩
  choose b j data using chooseDate
  refine ⟨⟨start+n₀,(fun t => start+b t),(fun t => n t+j t-b t),j,(fun t => I t (j t)),
    (fun t => next w (b t)),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro t k
    simpa only [next,Nat.add_assoc] using clock (b t+k)
  · exact fun t => (data t).2.2.2.2.2.2.2.2.2
  · exact fun t => (data t).2.2.1
  · exact fun t => (data t).2.2.2.1
  · exact fun t => (data t).2.2.2.2.1
  · intro t
    have := (data t).1
    dsimp only [n] at this ⊢
    omega
  · exact fun t => (data t).2.1
  · intro t
    simpa only [n,Nat.add_assoc] using (data t).2.2.2.2.2.1
  · intro t
    simpa only [n,Nat.add_assoc] using (data t).2.2.2.2.2.2.1
  · intro t
    simpa only [n,Nat.add_assoc] using (data t).2.2.2.2.2.2.2.1
  · refine tendsto_atTop.2 fun h => ?_
    have grow : Tendsto n atTop atTop := tendsto_atTop_mono (fun t => Nat.le_add_left t n₀) tendsto_id
    filter_upwards [grow.eventually (timely C D simple start w clock 0 h)] with t enough
    obtain ⟨hb,_,_,_,_,_,lo,hi,before,_⟩ := data t
    exact (enough (b t) (I t (j t)) hb lo hi before).2.1
end YM.Integration.WilsonPositionProgramArithmeticReporterBand
end
