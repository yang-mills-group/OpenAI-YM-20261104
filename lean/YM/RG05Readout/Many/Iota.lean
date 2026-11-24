import YM.RG05Readout.Many.Pick
/-!
# Repaint cost on actual shrinking aperture

In physical cluster geometry WM m observed, b from above, need replenish over
entire close interval without using Drake. Check subexponential power in m.
Not sufficient for comparing perturbative coefficient errors; this is for
REAL tight charges. Precisely RateIs on observation filter/height, uniform
in admitted geometry. Coupling domain real m into admitted tail.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {p k :ℕ} {E:Type} {l:Filter E} {D: Address.Rail C}
    {B:ℝ} {n m:E→ℕ} {T r:E→ℝ}
set_option quotPrecheck false
local notation "Z"=> C.path.levels
local notation "s"=> C.S.scale
local notation "β"=> C.path.levels.clock.hatBeta
local notation "α"=> C.S.a
local notation "Λ"=> Lambda C.path.levels

-- Capture convention exactly enough from above
structure CaptureW (C:Family G)(n m:ℕ)(r B:ℝ):Prop where
   lit : measured C.path.levels m r B
   nearF : r ≤ C.S.a n
   right : C.S.a (n+1) < r
lemma nearest (_hw:Storage C D) (hG:G.Simple)(ht:Tendsto T l atTop)(hm:Height C.S l T m 1) (hb:4 < B) (hp:∀ᶠ i in l,measured (Z) (m i) (r i) B):
    let n' i:=crossLevel C.S (r i)-1
    Height C.S l T n' 1∧∀ᶠ i in l, CaptureW C (n' i) (m i) (r i) B ∧ n' i < m i :=by
    intro A; obtain ⟨he,h⟩:=pace_crossing (Z|>.fits.mesh) ht (measured_rate hG ht hm hp)
    refine ⟨Log.previous ht he (Z).fits.mesh,?_⟩
    filter_upwards [h,he.grows.eventually_gt_atTop 0,hp] with i hi hX hp
    have hh : 1 < (Λ (m i)) ^ B:=Real.one_lt_rpow (one_lt_two.trans (lambda_gt ..)) (by linarith only [hb]); let P:= crossLevel C.S (r i); have hF:A i+1=P:=Nat.sub_add_cancel (show 1 ≤ P from hX)
    exact ⟨⟨hp,hi.2, hF.symm ▸ hi.1⟩,C.S.strictAnti.lt_iff_gt.mp ((lt_of_lt_of_le (lt_mul_of_one_lt_right (C.S.a_pos _) hh) hp.1).trans_le hi.2)⟩
-- gap charged by end.Start at n b fixed under Replay
lemma tall (x y :ℕ)(he:x≤y) : ((y-x:ℕ):ℝ) ≤ s y - s x:=by
    induction y,he using Nat.le_induction with
    | base=> simp
    | succ i hi ih=>
        have hu : Real.log 3 ≤ Real.log ((C.S.block i).val:ℝ):= Real.log_le_log (by norm_num) (by exact_mod_cast (C.S.block_large i))
        have hv: 1 ≤ Real.log 3:= (Real.le_log_iff_exp_le (by norm_num)).mpr (Real.exp_one_lt_d9.le.trans (by norm_num)) -- syntax
        rw [Schedule.scale_succ,show i+1-x=i-x+1 from by omega,Nat.cast_add,Nat.cast_one]; linarith
-- prove rust inverse rate via Height mix.Geometry.Scales
lemma beta_tends (hG:G.Simple) (hi:Height C.S l T n B): RateIs l T (fun i=> β (n i)) 0:=
    height0 (v:=fun i=> β i) ⟨fun i=>zero_lt_one.trans ((Z).fits.delayed i), (Work.I04.hat_receipt Z hG).tendsto_div_nhds_zero⟩ hi
lemma logpow (hG:G.Simple) (ht:Tendsto T l atTop)(hm:Height C.S l T m 1)(j:ℕ) : Tendsto (fun i=> (Real.log (β (m i)))^j / T i) l (𝓝 0):=by
    have hh:Tendsto (fun i=> β (m i)/ T i) l (𝓝 (G.slopeConstant)):=by
       let b:=(Z).clock.bar; have hb:= (show Tendsto (fun i=>b / T i) l (𝓝 0) from tendsto_const_nhds.div_atTop ht)
       have hB:= hb.add (hm.pace.const_mul G.slopeConstant); rw [mul_one,zero_add] at hB; refine hB.congr fun i=>?_; unfold Calendar.hatBeta; rw [add_div,mul_div_assoc]
    have he:= ((Real.isLittleO_pow_log_id_atTop (n:=j)).tendsto_div_nhds_zero).comp ((Next.Rank.Station.hat_rate Z hG).comp hm.grows)
    have hP:= he.mul hh; rw [zero_mul] at hP
    refine hP.congr (fun i=>?_); have hv:0 < β (m i):= zero_lt_one.trans ((Z).fits.delayed _); change _/ β (m i) *(β (m i)/T i)=_; field_simp; rfl

lemma sizes_rust (hw:Storage C D)(hG:G.Simple)(ht:Tendsto T l atTop)(hm:Height C.S l T m 1)(hn:Height C.S l T n 1)
    (hh:∀ᶠ i in l,n i ≤ m i) (hc:∀ᶠ i in l,CaptureW C (n i) (m i) (r i) B) (he:4 < B) :
       RateIs l T (fun i=> rusty C (m i) k (n i)) 0:=by
    let y(i):= (β (m i))^((3*k+4)*(m i - n i))
    let f(i):= rusty C (m i) k (n i)
    have hg(i): 1≤ β (m i):= (Z).fits.delayed _|>.le
    have hx :∀ᶠ i in l,(f i)⁻¹ ≤ y i:=by
        filter_upwards [hh] with i hi; unfold f y rusty; rw [inv_inv,pow_mul]; have ht (j:ℕ)(h:j∈ Finset.Ico (n i) (m i)) : j ≤ m i:= (Finset.mem_Ico.mp h|>.2).le;
        refine (Finset.prod_le_prod (fun j _=> pow_nonneg (zero_le_one.trans ((Z).fits.delayed j).le) _) (fun j hj=>pow_le_pow_left₀ (zero_le_one.trans ((Z).fits.delayed j).le) (beta_le' hG (ht j hj)) (3*k+4))).trans_eq ?_; rw [Finset.prod_const, Nat.card_Ico]
    have Hy:RateIs l T y 0:=by
       have hκ:= logpow hG ht hm 2
       let b(i):=β (m i); let x i:=Real.log (b i); let d i:=m i-n i; have hh' : Tendsto (fun i=>x i/T i) l (𝓝 0):=(beta_tends hG hm).rate
       have hxv:= hn.grows.eventually (shifts hw hG); have hy i:0 < b i:= zero_lt_one.trans_le (hg i); have hv (i):Real.log (y i)=↑(3*k+4:ℕ)*↑(d i)* x i:=by unfold y; rw [Real.log_pow,Nat.cast_mul]
       let ε:ℝ:=↑(3*k+4:ℕ); have hT : Tendsto (fun i=> ε*(x i^2/T i+(B+1)*(2*x i/T i+x i^2/T i))) l (𝓝 0):=by
          have hu:= (hh'.const_mul 2); have h:= ((hu.add hκ).const_mul (B+1)); have ht:= (hκ.add h).const_mul ε; rw [mul_zero,add_zero,mul_zero,add_zero,mul_zero] at ht; apply ht.congr; intro i; unfold x b; ring
       refine ⟨Eventually.of_forall (fun i=>pow_pos (hy i) _), squeeze_zero' ?_ ?_ hT⟩ -- Upper should be log^2/T not log/T factor: d ≤ log b + (B+1)(2+log b); *log b => log^2 + (B+1)(2log+log²)
       · filter_upwards [ht.eventually_ge_atTop 0] with i hi using div_nonneg (Real.log_nonneg (one_le_pow₀ (hg i))) hi
       filter_upwards [hxv,hc,hh,ht.eventually_ge_atTop 0] with i hi he' h0 ht
       have hl : ((C.S.block (n i)).val:ℝ) ≤ b i:= hi.2.1.trans (beta_le' hG h0); have hvx:= lambda_gt Z (m i); let w:=Λ (m i); have hW:= zero_lt_two.trans hvx; have hxl:Real.log w ≤ w:= Real.log_le_self hW.le
       have hps: (d i:ℝ) ≤ x i+ (B+1)*(2+x i):=by
          have hu: α (n i+1) ≤ (C.path.levels.S.a (m i))* w^(B+1):= le_trans he'.right.le he'.lit.2
          let L:= ((C.S.block (n i)).val:ℝ); have hL: Real.log (α (n i) / L) ≤ Real.log (α (m i)*w^(B+1)):=Real.log_le_log (div_pos (C.S.a_pos _) (by positivity)) (by rw [← show α (n i+1)= _ from C.S.a_step _]; exact hu)
          rw [Real.log_div (C.S.a_pos _).ne' (show L ≠ 0 from Nat.cast_ne_zero.mpr (C.S.block (n i)).property.ne'), Real.log_mul (C.S.a_pos _).ne' (Real.rpow_pos_of_pos hW _|>.ne'),Real.log_rpow hW] at hL
          apply le_trans (tall (C:=C) (n i) (m i) h0); unfold Schedule.scale; rw [Real.log_inv,Real.log_inv]; have heξ:0≤ B+1:=by linarith only [he]
          have hw: Real.log L ≤x i:=Real.log_le_log (show 0<L by unfold L; positivity) hl; have hz:w=2+x i:=rfl; nlinarith only [hL,hxl,heξ,hz,hw]
       rw [hv]; exact ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hps (show 0≤ ε by unfold ε; positivity)) (Real.log_nonneg (hg _))) ht)).trans_eq (by unfold x b ε; ring)
    have hi: RateIs l T (fun i=> (f i)⁻¹) 0:= RateIs.of_sandwich (RateIs.const ht (c:=1) one_pos) (Hy.pays ht) (.of_forall fun i=> (one_le_inv₀ (show 0 < f i from (rust_paid _).1)).mpr (rust_paid _).2) hx ht
    refine hi.inv.congr ?_ |>.swap (neg_zero)
    exact Eventually.of_forall (fun x=> inv_inv (f x))
variable (hw:Storage C D)(hG:G.Simple)(ht:Tendsto T l atTop)(hm:Height C.S l T m 1)(hn:Height C.S l T n 1)
    (hh:∀ᶠ i in l,n i ≤ m i) (hc:∀ᶠ i in l,CaptureW C (n i) (m i) (r i) B) (he:4 < B) {q:E→ℝ}
include hw hG ht hm hn hh hc he
lemma rust_end (hq:RateIs l T q 0)(d k:ℕ): RateIs l T (fun i=> Many.envelope C (m i) d k (q i) (n i)) 0:=by
     have hx:RateIs l T (fun i=> total C (q i) d (m i) (n i)) 0:=by
         refine (hq.mul ((hn.mesh.div hm.mesh).power d)).congr ?_|>.swap (by ring)
         filter_upwards [hh] with i hi; unfold total; rw [dif_neg (by omega)]
     let P:= beta_tends hG hn; let l':=sizes_rust (k:=k) hw hG ht hm hn hh hc he
     exact (l'.mul (((RateIs.power (n:=k) P).inv).div hx)).swap (by ring)
end YM.RG05Readout.Many
