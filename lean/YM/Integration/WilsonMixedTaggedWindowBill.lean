import YM.Integration.WilsonMixedTaggedReserve
import YM.Integration.WilsonMixedTaggedCaptureRadii
import YM.FullVolume.Cross

/-! A common D at the original reporting date funds all its lower intervals
meeting the two explicit numerical bounds of the physical capture window.
Every regulator and lower observable is quantified after D. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedWindowBill
open Filter Finset Function Lattice Wilson RG Marker RG05Readout Many OPE
open PhysicalNext.Repeat.Legato WilsonMixedTaggedCaptureRadii
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem original (R:Run G) (simple:G.Simple) (T d k h L p:ℕ) {ε:ℝ} (ep:0 < ε) :
    ∀ᶠ m:ℕ in atTop,let C:=R.family
      let B:=(C.path.levels.budget m).B
      let β:=C.path.levels.clock.hatBeta m
      ∃ D:ℕ,D*(4*B+2)+2*B ≤ B^2 ∧ β^((k+h)*L)*Real.exp (-(D:ℝ)) ≤ 1 ∧ 
        ∀b:ℕ,C.S.a b/C.S.a m ≤ (RG05Readout.Lambda C.path.levels m)^T → 
          ((m-b:ℕ):ℝ) ≤ (T:ℝ)*(1+Real.log (RG05Readout.Lambda C.path.levels m)) → 
          ∀N:ℕ,m ≤ N → ∀per:ℕ,
            let g:=(Real.sqrt (C.path.rep N per m).beta)⁻¹
            ∀i:ℕ,b ≤ i → i ≤ m → ∀ {V:Type}[DecidableEq V]{J:Census V} (Q:V → ℝ),
              (∀v,0 < Q v) → (∀v,Q v ≤ β^h) → ∀s:J.Mode,s.val.card ≤ L → 
              β^((k+h)*L)*Real.exp (-(D:ℝ)) ≤ (ε*g^p)*
                Poly.toll (fun v=>envelope C m d k (Q v) i) s := by
  let charge:=cost T d k h
  let M:ℕ:=(k+h)*L
  let F:ℝ:=(L:ℝ)*charge+M+p+|Real.log ε|
  have posC : 0 ≤ charge := by unfold charge cost; positivity
  have pf : 0 ≤ F := by unfold F; positivity
  have grown:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  filter_upwards [grown.eventually (WilsonMixedTaggedReserve.quarter F pf),
    grown.eventually_ge_atTop (Real.log 2)] with m reserve above
  intro C B β
  let x:=Real.log β
  let mast:=RG05Readout.Lambda C.path.levels m
  let y:=Real.log mast
  let H:=(1+x)*(1+y)
  obtain ⟨D,room,all⟩ := reserve B (Nat.le_ceil _)
  have bp : 0 < β := zero_lt_one.trans (C.path.levels.fits.delayed m)
  have x0 : 0 ≤ x := Real.log_nonneg (C.path.levels.fits.delayed m).le
  have yp : 1 ≤ mast := by change 1 ≤ 2+x; linarith
  have y0 : 0 ≤ y := Real.log_nonneg yp
  have xp : x ≤ H := by unfold H; nlinarith only [x0,y0,mul_nonneg x0 y0]
  have cap1 : 1 ≤ H := by unfold H; nlinarith only [x0,y0,mul_nonneg x0 y0]
  have bill : F*H ≤ D := by
    change F*(1+x)*(1+y) ≤ (D:ℝ) at all
    simpa only [H,mul_assoc] using all
  have powβ : β^M=Real.exp ((M:ℝ)*x) := by
    change β^M=Real.exp ((M:ℝ)*Real.log β)
    rw [←Real.log_pow,Real.exp_log (pow_pos bp _)]
  have raw : β^M*Real.exp (-(D:ℝ)) ≤ 1 := by
    rw [powβ,←Real.exp_add,Real.exp_le_one_iff]
    have mF : (M:ℝ) ≤ F := by
      unfold F
      linarith only [mul_nonneg (Nat.cast_nonneg L : (0:ℝ) ≤ L) posC,
        abs_nonneg (Real.log ε),(Nat.cast_nonneg p : (0:ℝ) ≤ p)]
    have F0 : 0 ≤ H := zero_le_one.trans cap1
    linarith only [bill,mul_le_mul_of_nonneg_right mF F0,
      mul_le_mul_of_nonneg_left xp (Nat.cast_nonneg M : (0:ℝ) ≤ M)]
  refine ⟨D,room,raw,?_⟩
  intro b ratio gap N mn per g i bi im V de J Q qp price s count
  let βr := (C.path.rep N per m).beta
  have band:=(R.makes.wilson.represents N per m mn).band
  have br : 0 < βr := (half_pos bp).trans_le band.1
  have logbr : Real.log βr ≤ 2*x := by
    have hh:=Real.log_le_log br band.2
    change Real.log βr ≤ Real.log (2*β) at hh
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) bp.ne'] at hh
    change Real.log βr ≤ Real.log 2+x at hh
    change Real.log 2 ≤ x at above
    linarith
  have gpos : 0 < g := inv_pos.mpr (Real.sqrt_pos.2 br)
  have logg : Real.log g= -(Real.log βr)/2 := by
    rw [show g=(Real.sqrt βr)⁻¹ from rfl,Real.log_inv,Real.log_sqrt br.le]; ring
  have cents : (M:ℝ)*x -(D:ℝ)+L*charge*H ≤ Real.log ε+(p:ℝ)*Real.log g := by
    rw [logg]
    unfold F at bill
    have e:=mul_le_mul_of_nonneg_left cap1 (abs_nonneg (Real.log ε))
    nlinarith only [bill,mul_le_mul_of_nonneg_left xp (Nat.cast_nonneg M : (0:ℝ) ≤ M),
      mul_le_mul_of_nonneg_left xp (Nat.cast_nonneg p : (0:ℝ) ≤ p),e,
      neg_le_abs (Real.log ε),mul_le_mul_of_nonneg_left logbr (Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  let W:=Real.exp ((L:ℝ)*charge*H)
  have complete : β^M*Real.exp (-(D:ℝ))*W ≤ ε*g^p := by
    have powg : g^p=Real.exp ((p:ℝ)*Real.log g) := by
      rw [←Real.log_pow,Real.exp_log (pow_pos gpos _)]
    rw [powβ,powg,show ε=Real.exp (Real.log ε) from (Real.exp_log ep).symm]
    unfold W
    rw [←Real.exp_add,←Real.exp_add,←Real.exp_add,Real.exp_le_exp]
    linarith only [cents]
  have one : 1 ≤ W*Poly.toll (fun v=>envelope C m d k (Q v) i) s := by
    simpa only [W,H,charge,mul_assoc] using mode simple bi im Q qp price ratio gap s count
  have w0 : 0 ≤ Poly.toll (fun v=>envelope C m d k (Q v) i) s :=
    Finset.prod_nonneg fun v _=>(radius simple bi im (qp v) (price v) ratio gap).1.le
  calc
    _ ≤ (β^M*Real.exp (-(D:ℝ)))*(W*Poly.toll (fun v=>envelope C m d k (Q v) i) s) :=
      le_mul_of_one_le_right (by positivity) one
    _ = (β^M*Real.exp (-(D:ℝ))*W)*Poly.toll (fun v=>envelope C m d k (Q v) i) s := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right complete w0


end YM.Integration.WilsonMixedTaggedWindowBill
