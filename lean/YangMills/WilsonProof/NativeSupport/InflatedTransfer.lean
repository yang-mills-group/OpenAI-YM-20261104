import YangMills.WilsonProof.NativeSupport.NativeSecantEnvelope
import YangMills.WilsonProof.NativeSupport.TwoPointMarkers

/-! Remove the temporary color inflation from the fresh and nonlinear
outputs of the original marked tariff, including their real secants. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset RG Wilson Marker Lattice Extra.Trajectories Packet Painted
open FullVolume.Ray PhysicalNext.Repeat.Luna PhysicalNext.Repeat.Jams Push.GridApprox.Nil
open scoped BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {I Y : Type} {n : Side}
local notation "Census₀" => Stock.census (Ink V)
local notation "Mode₀" => (Stock.census (Ink V)).Mode

def gains (fresh : Finset V) (S : Finset (Ink V)) : Prop :=
  2≤(S.filter (fun p=>p.2.1)).card ∨ 1≤(S.filter (fun p=>p.1∈fresh)).card

theorem earned {A D : ℝ} (a : 1≤A) (d : 1≤D) (w : V→ℝ) (hw : ∀ x,0<w x)
    (fresh : Finset V) (s : Mode₀) (hit : gains fresh s.val) :
    min D (A^2) * Poly.toll (fun p : Ink V=>w p.1) s ≤
      Poly.toll (weight w A D fresh) s := by
  let k := (s.val.filter (fun p=>p.2.1)).card
  let l := (s.val.filter (fun p=>p.1∈fresh)).card
  have count (u : Ink V→Prop) [DecidablePred u] (v : ℝ) :
      (∏ p∈s.val, if u p then v else 1)=v^(s.val.filter u).card := by
    rw [← prod_filter,prod_const]
  have parts : Poly.toll (weight w A D fresh) s =
      Poly.toll (fun p : Ink V=>w p.1) s * A^k * D^l := by
    simp only [Poly.toll,Painted.weight,prod_mul_distrib,count,k,l]
  have gain : min D (A^2) ≤ A^k*D^l := by
    rcases hit with hk | hl
    · exact (min_le_right ..).trans ((pow_le_pow_right₀ a hk).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ d)))
    · have hd : D≤D^l := by
        nth_rewrite 1 [← pow_one D]; exact pow_le_pow_right₀ d hl
      exact (min_le_left ..).trans (hd.trans
        (le_mul_of_one_le_left (by positivity) (one_le_pow₀ a)))
  rw [parts,mul_assoc,mul_comm (min ..)]
  exact mul_le_mul_of_nonneg_left gain (Poly.worth (fun p : Ink V=>hw p.1) s).le

/-- Point values may be tested at independent configurations for each mode
and support. Thus this bound also prices sums of individual suprema. The
site is the projection of the requested original root by Burns or Flow. -/
theorem fresh_or_quadratic {A D q e C θ : ℝ} {b : ℕ} {X : I→Support n}
    (a : 1≤A) (d : 1≤D) (w : V→ℝ) (hw : ∀ x,0<w x) (fresh : Finset V)
    {F : sun→I→Y→Poly Census₀} (h : Ankh (weight w A D fresh) q F b X e C)
    (s : sun) (pos : 0<θ) (short : |s.val|≤θ)
    (Q : I → Finset Mode₀) (paid : ∀ i S, S∈Q i → gains fresh S.val)
    (U Z : I → Mode₀ → Y) (x : Site n) (J : Finset I)
    (through : ∀ i∈J,x∈X i) :
    min D (A^2) * (∑ i∈J,
      (∑ S∈Q i, Poly.toll (fun p : Ink V=>w p.1) S *
        (‖(F tip i (U i S)).part S‖+
          ‖(F s i (Z i S)).part S-(F tip i (Z i S)).part S‖/θ)) *
        Real.exp (e*coverNumber b (X i))) ≤ 2*C := by
  obtain ⟨u,v,_,hits,bills,est⟩ := marked_secant h s pos short
  let base (S : Mode₀) := Poly.toll (fun p : Ink V=>w p.1) S
  let loaded (S : Mode₀) := Poly.toll (weight w A D fresh) S
  let c (i : I) (S : Mode₀) :=
    ‖(F tip i (U i S)).part S‖+‖(F s i (Z i S)).part S-(F tip i (Z i S)).part S‖/θ
  let L := min D (A^2)
  have nn : 0≤L := le_min (zero_le_one.trans d) (sq_nonneg _)
  have weight_pos (p : Ink V) : 0<weight w A D fresh p := by
    have wp := hw p.1
    have ap : 0<A := zero_lt_one.trans_le a
    have dp : 0<D := zero_lt_one.trans_le d
    unfold Painted.weight; split <;> split <;> positivity
  have localCost (i : I) : L*(∑ S∈Q i,base S*c i S)≤2*u i := by
    calc
      L*(∑ S∈Q i,base S*c i S) ≤ ∑ S∈Q i,2*(loaded S*v i S) := by
        rw [mul_sum]; apply sum_le_sum
        intro S hs
        have value : c i S ≤ v i S+v i S := add_le_add (est i (U i S) S).1 (est i (Z i S) S).2
        have positive : 0≤base S := (Poly.worth (fun p : Ink V=>hw p.1) S).le
        have left : L*base S ≤ loaded S := earned a d w hw fresh S (paid i S hs)
        calc
          L*(base S*c i S) = (L*base S)*c i S := (mul_assoc ..).symm
          _ ≤ (L*base S)*(v i S+v i S) := mul_le_mul_of_nonneg_left value (mul_nonneg nn positive)
          _ ≤ loaded S*(v i S+v i S) := mul_le_mul_of_nonneg_right left (add_nonneg ((bills i).1 S) ((bills i).1 S))
          _ = _ := by ring
      _ = 2*(∑ S∈Q i,loaded S*v i S) := (mul_sum ..).symm
      _ ≤ 2*wordsPrice (weight w A D fresh) (v i) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun S _ _=>
          mul_nonneg (Poly.worth weight_pos S).le ((bills i).1 S))
      _ ≤ 2*u i := mul_le_mul_of_nonneg_left (bills i).2 (by norm_num)
  have hit := (hits x).2.1.sum_le_tsum J (fun i _=>(hits x).1 i)
  have projected : (∑ i∈J,u i*Real.exp (e*coverNumber b (X i)))≤C := by
    refine le_trans ?_ (hit.trans (hits x).2.2)
    apply sum_le_sum; intro i hi; rw [if_pos (through i hi)]
  change L*(∑ i∈J,(∑ S∈Q i,base S*c i S)*_)≤_
  calc
    _ ≤ ∑ i∈J, 2*(u i*Real.exp (e*coverNumber b (X i))) := by
      rw [mul_sum]; apply sum_le_sum
      intro i _
      rw [← mul_assoc,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (localCost i) (Real.exp_pos _).le
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left projected (by norm_num)

end YM.Integration.InletSusceptibility
