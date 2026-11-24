import YM.FormalBulk08.Shore.Roam

/-! Tiling limit by copying gauge parameters and repeated cell. NOTE: reduces translations only, no cancellation of scalar claims exported. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Shore
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick Lotus Orb
open scoped BigOperators Classical ENNReal Topology
variable {I : Type*} [Fintype I] {r : ℕ} (n : Side)
lemma onward : Tendsto (fun m=>m*n) atTop atTop:= tendsto_atTop.mpr fun m=> (eventually_ge_atTop m).mono fun k h=>le_trans h (by change k.val≤ k.val*n.val; exact Nat.le_mul_of_pos_right _ n.property)

variable (i : Fin r) (v : chain (Tor n I) r)
omit [Fintype I] in
def joltUp : Jolt (Picks i n (boil n (v i)) v) (fun m=>Pupil m n i v) where
    give m w:=⟨drip (m*n) ∘ w.val, funext fun j=>by rw [comp_apply,comp_apply,tray_drip]; exact congr_fun w.property.2 j,congr_arg (drip (m*n)) w.property.1⟩
    undo m w:=⟨update (boil (m*n) ∘ w.val) i (boil n (v i)),update_self ..,funext fun j=> by
       by_cases h:i=j
       · subst j; simp
       rw [comp_apply, update_of_ne (Ne.symm h),comp_apply,←tray_drip m n,drip_boil]; exact congr_fun w.property.1 j⟩
    back m x:=Subtype.ext (funext fun j=>by
       change drip (m*n) (update (boil (m*n) ∘ x.val) i (boil n (v i)) j)=_;by_cases e:j=i
       · subst j; simpa only [update_self] using x.property.2.symm
       rw [update_of_ne e,comp_apply,drip_boil])
    tame x:=by
       filter_upwards [eventually_all.mpr (fun j=> (onward n).eventually (boil_drip (x.val j)))] with m hm
       apply Subtype.ext; funext j; change update _ _ _ _=_; by_cases e:i=j
       · subst j;rw [update_self];exact x.property.1.symm
       rw [update_of_ne (Ne.symm e)]; exact hm j
omit [Fintype I] in
lemma prod_shine (w : chain (Biglot I) r) (η : ℝ): ∏ i,coast η (w i)=Real.exp (-η*(∑ j,size (w j).1 : ℕ)) := by simp only [coast, Nat.cast_sum,Finset.mul_sum,Real.exp_sum]
lemma pupils_limit {η C : ℝ} {T : Tile (Biglot I) r} {S : (n:Side)→ Tile (Tor n I) r} (hs : 0<η)
   (ht : Light T S) (hp : Bright S η C) : Tendsto (fun m=> ∑ j:Pupil m n i v,S (m*n) j.val) atTop (𝓝 (vat i n (boil n (v i)) T v)) := by
   let W:=Picks i n (boil n (v i)) v
   let x:=boil n (v i); let R:= size x.1
   have hr : 0<r:= Nat.pos_of_ne_zero (by intro h; have :=i.isLt;omega)
   have hx := div_pos hs (Nat.cast_pos.mpr hr); let g : W→ℝ:=fun w=> (Real.exp (η*R)*C)*(∏ j,coast (η/r) (w.val j)); let D:= joltUp n i v
   have hc: 0 ≤ C:=hp.exists.choose_spec.1
   have hU : Tendsto (fun m:Side=>∑' j:Pupil m n i v,S (m*n) j.val) atTop (𝓝 (∑' w:W,T w.val)) := by
      refine jolt_limit D _ (fun w=> T w.val) g (((monsoon (r:=r) (I:=I) hx).comp_injective (show Injective (Subtype.val (p:=fun w:chain (Biglot I) r=>w i=boil n (v i) ∧ drip n ∘ w=v)) from Subtype.val_injective)).mul_left _) (fun w=>mul_nonneg (mul_nonneg (Real.exp_pos _).le hc) (Finset.prod_nonneg fun _ _=>(Real.exp_pos _).le)) (fun w=>(ht w.val).comp (onward n)) ?_
      filter_upwards [(onward n).eventually hp] with m hm u
      let a:=S (m*n) u.val; let K:=wide (lake (m*n) I) u.val; let b:= D.undo m u
      have e : Real.exp (η*K)* ‖a‖ ≤ C:=palmed hm u.val i
      have he : (∑ j,size (b.val j).1 : ℕ) ≤ r*(K+R) := by
         have hy j: size (b.val j).1 ≤ K+R := by
            by_cases hj:j=i
            · subst j; rw [b.property.1];change R≤_; omega
            change size ((Function.update (boil (m*n) ∘ u.val) i x j).1) ≤ _;rw [update_of_ne hj]; apply (skit_anchor _ u.val i j).trans (Nat.add_le_add_left ?_ _); rw [u.property.2];exact skirt ..
         refine (Finset.sum_le_sum fun j _=>hy j).trans ?_; simp
      unfold g; rw [prod_shine];change ‖a‖≤Real.exp _*C*Real.exp (-(η/r)*_)
      calc
        _ = Real.exp (-(η*K))*(Real.exp (η*K)* ‖a‖):= by rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
        _ ≤ Real.exp (-(η*K))*C:=mul_le_mul_of_nonneg_left e (Real.exp_pos _).le
        _ ≤ _ := by rw [mul_right_comm (Real.exp (η*R))]; apply mul_le_mul_of_nonneg_right _ hc; rw [←Real.exp_add];apply Real.exp_monotone
                    change -(η*K) ≤ η*R + (-(η/r))*((∑ j,size (b.val j).1 : ℕ):ℝ); let t : ℕ := ∑ j,size (b.val j).1;have he' : (t:ℝ) ≤ (r:ℝ)*((K:ℝ)+(R:ℝ)):= by exact_mod_cast he
                    change -(η*K) ≤ η*R+ (-(η/r))*(t:ℝ); have hh : -(η/r)*(t:ℝ)≥ -(η/r)*((r:ℝ)*((K:ℝ)+(R:ℝ))) := mul_le_mul_of_nonpos_left he' (by linarith)
                    refine le_trans ?_ (add_le_add_right hh _)
                    apply le_of_eq; field_simp; ring
   simp_rw [tsum_fintype] at hU; exact hU
end YM.FormalBulk08.Shore
