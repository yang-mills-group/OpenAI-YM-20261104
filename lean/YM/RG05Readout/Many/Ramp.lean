import YM.RG05Readout.Many.Run
/-!
# Exact palette envelopes

Physically instantiate Pencils from advertised true representation(s)
all levels intervals. When measuring at m, in threshold units at native
mesh we already include reexpression along this germ transfer. Recalibration
to g conventions is not here. Close marker price from Rust, poles at β_i.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{W:Type*}
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "L!"=> C.path.levels.clock.op
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "π₀"=> C.path.levels.clock.hatBeta
local notation "ψ₀"=> far C.path.levels
local notation "ℓ"=> Copper.ld C.path.levels
local notation "x₀"=> C.S.block
local notation "a₀"=> C.S.a
variable {Q:ℝ}{B:ℕ→ℕ→ℝ}
-- pre-conditions to set # all touched.Lean definitional h proof for nonzero part.

def total (C:Family G)(Q:ℝ)(d m i:ℕ):ℝ:= if h:m < i then Q * stringCost C h.le else Q*(C.S.a i/C.S.a m)^d
noncomputable def rusty (C:Family G)(m t i:ℕ):ℝ:= (∏ j ∈ Finset.Ico i m, (C.path.levels.clock.hatBeta j)^(3*t+4))⁻¹
local notation "P!"=> total C Q d m
local notation "η"=> rusty C m k

lemma rust_paid (i:ℕ): 0< η i ∧ η i ≤ 1:=by
    let P j:= (π₀ j)^(3*k+4); have hp j: 1 ≤ P j:= one_le_pow₀ ((Z₀).fits.delayed j).le
    have h := Finset.one_le_prod (f:=P) (s:=Finset.Ico i m) (fun i _=>hp i); exact ⟨inv_pos.mpr (zero_lt_one.trans_le h),inv_le_one_of_one_le₀ h⟩
lemma rust_local {i:ℕ}(h:i < m): η i= η (i+1)*((π₀ i)^(3*k+4))⁻¹:=by unfold rusty; rw [Finset.prod_eq_prod_Ico_succ_bot h,mul_inv_rev] -- syntax
lemma rust_above {i:ℕ}(h:m ≤ i): η i=1:=by unfold rusty; rw [Finset.Ico_eq_empty_of_le h,Finset.prod_empty,inv_one]
lemma total_middle : P! m= Q:=by unfold total; rw [dif_neg (lt_irrefl _),div_self (C.S.a_pos _).ne',one_pow,mul_one]
lemma total_upper {i:ℕ} (hi:m ≤ i) : P! i=Q*stringCost C hi:=by
    by_cases h:m=i
    · subst i; rw [total_middle,string_base,mul_one]
    exact dif_pos (lt_of_le_of_ne hi h)
lemma totaltail {i:ℕ}(hi:m ≤ i): P! (i+1)= (ℓ i)* (P! i):=by
    rw [total_upper (hi.trans i.le_succ), string_next hi, total_upper hi]; ring
lemma totalclose {i:ℕ}(hi:i < m): P! i= ((x₀ i).val:ℝ)^d * P! (i+1):=by
    have he:= C.S.a_step i
    unfold total; rw [dif_neg hi.asymm, dif_neg (show ¬m < i+1 by omega),he]
    have hp : 0 < ((x₀ i).val:ℝ):=by positivity
    have hv:0 < C.S.a m:= C.S.a_pos _; rw [div_pow,div_pow,div_pow]; field_simp
lemma stampCosts {m i:ℕ}(h:m ≤ i) : 1 ≤ stringCost C h:=by
    induction i,h using Nat.le_induction with
    | base=> rw [string_base]
    | succ i hi ih=>rw [string_next hi]; exact one_le_mul_of_one_le_of_one_le (lamp_nn _) ih
lemma totalpos (h:0 < Q)(i:ℕ) : 0<P! i:=by
    unfold total; split
    next he=> exact mul_pos h (zero_lt_one.trans_le (stampCosts he.le))
    exact mul_pos h (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _)

-- v true tuning in sharp root; if mixture centers require coherence via `centered_about` at auction
noncomputable def point {d:ℕ} (T:Emblems C d) (x:Palette C d)(m i:ℕ):= if h:m < i then finer T h.le x else (finer T (Nat.le_of_not_lt h)).symm x
lemma point_here {x:Palette C d}{T:Emblems C d}: point T x m m=x:=by unfold point; rw [dif_neg (lt_irrefl _),base_value]; rfl
lemma weave_fine {i:ℕ}(hi:m≤ i)(T:Emblems C d)(x:Palette C d): point T x m i= finer T hi x:=by
    by_cases ht:m=i; subst i; rw [base_value,point_here]; rfl
    exact dif_pos (lt_of_le_of_ne hi ht)
-- need chain to LEFT. compositional.
lemma sumwalk (T:Emblems C d){i j l:ℕ}(h:i≤ j)(ht:j≤l): finer T (h.trans ht)= (finer T h).trans (finer T ht):=by
    induction l,ht using Nat.le_induction with
    | base=>rw [base_value, LinearEquiv.trans_refl]
    | succ i₁ hi ih=> rw [finer_next hi, finer_next (h.trans hi),ih];rfl
lemma nearpoints (T : Emblems C d) (x:Palette C d)(i:ℕ): T i (point T x m (i+1))=point T x m i:=by
    by_cases ht:m ≤ i
    · rw [weave_fine (ht.trans i.le_succ),finer_next ht, LinearEquiv.trans_apply,(T i).apply_symm_apply, weave_fine ht]
    unfold point; rw [dif_neg (show ¬m < i+1 from by omega),dif_neg (by omega),show finer T (show i ≤ m from by omega)=(finer T i.le_succ).trans (finer T (show i+1≤ m by omega)) from sumwalk T _ _,finer_next (le_refl i),base_value]; rfl

variable {h:C.Makes}{u:Emblems C g}{H:Sight C g p}{i:ℕ}{x:Palette C g}
local notation "c!"=> point u x m
lemma lamp_head (i:ℕ): ℓ i≤( (x₀ i).val:ℝ):=Real.rpow_le_self_of_one_le (by exact_mod_cast (C.S.block i).property) (by apply (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (by positivity))) -- notation C binder issue embedded section var via quotation intentional?
lemma head_cost (ht:Spine D B h n p g N H u)(hn:n≤ m)(hp:m≤ N)(hx:g+1≤d)(hh:size x≤Q)(hi:n≤ i)(he:i≤ N): size (c! i) ≤ P! i:=by
    by_cases hv:m ≤ i
    · rw [weave_fine hv,total_upper hv]; exact ((ht.inverse_cost hn hv he x).trans ((mul_le_mul_of_nonneg_left hh (zero_le_one.trans (stampCosts hv))).trans_eq (mul_comm ..)))
    have h_cost (k:ℕ)(hf:n ≤ k)(hm:k ≤ m): size (c! k) ≤ P! k:=by
       induction hm using Nat.decreasingInduction with
       | self=> rw [point_here,total_middle]; exact hh
       | of_succ k hK ih=>
           let p':=(x₀ k).val; have hK':1 ≤ (p':ℝ):=by exact_mod_cast (C.S.block k).property
           have hL:= (ht.follows k hf (hK.trans_le hp)).strength (c! (k+1)); let x':= size (c! (k+1)); have hb := size_tuned (C.S.block k) (c! (k+1))
           rw [totalclose hK, ← nearpoints u]; apply le_trans hL.2 _
           have hy:= ih (hf.trans k.le_succ)
           refine (mul_le_mul (lamp_head (C:=C) k) (hb.trans (mul_le_mul_of_nonneg_left hy (pow_nonneg (zero_le_one.trans hK') _))) (size_ge _) (zero_le_one.trans hK')).trans ?_
           rw [← mul_assoc,← pow_succ']; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK' hx) ((size_ge _).trans hy)
    apply h_cost _ hi (le_of_not_ge hv)

-- The following estimates use the storage bound and OPE package for the same data.
variable (hC:Storage C D)(L : OPE.Package C w r D)(hG:G.Simple)
include hC L hG
structure Warm (C:Family G)(b d k:ℕ):Prop where
   lanes i : i ≤ d → C.ref i ≤ b
   bears i : b ≤ i → 8 ≤ (C.path.levels.budget i).B ∧ Refresh (C:=C) d k i
   buys (i N:ℕ) : i ≤ d → b ≤ N → pricesTop (Legato.Bandage.fly C.path.levels) (far C.path.levels) N i ≤ far C.path.levels N * ((C.path.levels.clock.hatBeta N)^k) -- j unused remove
lemma warmups (d:ℕ) : ∃ k:ℕ,∀ᶠ n in atTop,Warm C n d k:=by
    obtain ⟨k,h,hK⟩:= startPay (C:=C) hG d 1 zero_lt_one
    obtain ⟨l,hl⟩:= eventually_atTop.mp hK; obtain ⟨z,hz⟩:= eventually_atTop.mp (refreshes hC hG d k h)
    refine ⟨k,?_⟩
    filter_upwards [eventually_ge_atTop l,eventually_ge_atTop z, (eventually_all_finset (Finset.range (d+1))).mpr (fun i _=> eventually_ge_atTop (C.ref i))] with i hi hv hS
    refine ⟨fun j hh=> hS j (Finset.mem_range.mpr (by omega)),fun j hj=>⟨L.system.costs.stay.support _ (Nat.zero_le _), hz _ (hv.trans hj)⟩,fun j k hj hk=>?_⟩ -- Warm.buys
    exact (Eq.trans_le (mul_one _).symm ((hl k (hi.trans hk)).2 j hj))
omit hC L hG
lemma ignite (hp: Warm C n d k)(hx:0 < Q) (hd:1 ≤ d):Purse C η (P!) n N d k:=by
   have hh(i:ℕ):0 < P! i:= totalpos hx i
   refine ⟨fun i _ _=> hh i,?_,fun _ _ _=>rust_paid _,fun i hi _=> (hp.bears i hi).symm⟩
   intro i h hn p
   have he:1≤ p:=by unfold p; exact_mod_cast (C.S.block i).property
   have hm: p ≤ p^d:= calc p = p^1:=by simp
                             _ ≤ p^d:=pow_le_pow_right₀ he hd
   by_cases hv:m ≤ i
   · have ht:=totaltail (C:=C) (Q:=Q) (d:=d) hv; refine ⟨le_trans ?_ (le_mul_of_one_le_left (hh _|>.le) (one_le_pow₀ he)),by rw [ht]; exact mul_le_mul_of_nonneg_right ((lamp_head (C:=C) i).trans hm) (hh _|>.le)⟩ -- Le_mul wrong orientation inspect
     rw [ht]; exact le_mul_of_one_le_left (hh i|>.le) (lamp_nn _)
   have ht:=totalclose (C:=C) (Q:=Q) (d:=d) (show i < m by omega); have ha : 1 ≤ p^d:= one_le_pow₀ he
   exact ⟨ht.le, (le_trans (show P! (i+1) ≤ P! i from ht.symm ▸ le_mul_of_one_le_left (hh _|>.le) ha) (le_mul_of_one_le_left (hh _|>.le) ha))⟩
end YM.RG05Readout.Many
