import YM.RG12.Kintsugi.Course
/-! # Calibration toll at four in the persistent/physical sheets -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Set Function MeasureTheory Analysis Extraction Table Climb Ward Next.UVStress Spec Org Next.Rank Next.Rank.Perch
open Next.Rank.Atlas Next.Rank.East MergeProof MergeProof.East Source UVNext.FreeStress
open scoped Topology BigOperators ContDiff Classical
open Further.CorrectedLift
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d)
variable (P:Commission.Port C)(T: MaxwellData C)
local notation "A!"=>C.path.levels
local notation "H!"=>U.room.kernel
local notation "B!"=>Bel C.book
local notation "V!"=>U.sector.derivatives
local notation "p!"=>T.T.W
local notation "χ"=>C.path.levels.clock.hatBeta
lemma solid_mass {d:ℕ}(x y:C.label d):mass C d (x+y) ≤ mass C d x + mass C d y:=by
   unfold mass Labels.Frame.coeffSize; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=>norm_add_le (x i) (y i)
lemma supplies_mass {d:ℕ}(c:ℂ)(x:C.label d):mass C d (c•x)= ‖c‖ * mass C d x:=by
   unfold mass Labels.Frame.coeffSize; simp_rw [Pi.smul_apply,norm_smul,Finset.mul_sum]
variable {D k:ℕ}{Z:TableL C D}(ha:Authentic U M P T k D Z)
include ha
lemma spatial_fee (hk:4≤D)(x:C.label 4):mass C 4 (Z ⟨4,Nat.lt_succ_of_le hk⟩ x) ≤ 32*(χ k)^8*mass C 4 x:=by
   let b:= Station.mag (A!) (P.panels D 0).arc k
   let a:= (A!).clock.monitor k
   let t:= χ k
   have he:= ha.above (⟨4,Nat.lt_succ_of_le hk⟩ : Fin (D+1)) x
   have h0 : 0<a:=Real.exp_pos _
   have h1 : 0<b:=by dsimp [b]; rw [mag_bill]; exact Real.exp_pos _
   change _≤ 2*(2*a)^4*b^4*mass C 4 x at he
   apply he.trans
   apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..)
   let q:=(χ k)
   apply le_trans (b:=2*(2*q)^4*q^4)
   · apply mul_le_mul
     · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left ha.monitored (by norm_num)) _) (by norm_num)
     · exact pow_le_pow_left₀ h1.le ha.leveled _
     · positivity
     exact mul_nonneg (by norm_num) (by positivity)
   exact le_of_eq (by unfold q; ring)
lemma recovers_cost (hk:4≤D)(x:C.label 4): mass C 4 x ≤ 24 * mass C 4 (Z ⟨4,Nat.lt_succ_of_le hk⟩ x):=by
   have h:= ha.below (⟨4,Nat.lt_succ_of_le hk⟩ : Fin (D+1)) x
   change mass C 4 x ≤ (2^4*(3/2):ℝ)*_ at h; norm_num at h; linarith only [h]
lemma clock_fee :
    let l:= C.S.a k; let r:=Next.Rank.Station.gap (A!) (P.panels D 0).arc k
    1 ≤ χ k ∧ l ≤ r ∧ r ≤ l * χ k:=by
   have hp:0 ≤ (P.panels D 0).arc:=by linarith only [(P.panels D 0).huge,Nat.cast_nonneg (α:=ℝ) D]
   let b:= Station.mag (A!) (P.panels D 0).arc k
   have he:1 ≤ b:=by dsimp [b]; rw [mag_bill]; exact Next.Rank.Glimmer.costed _ _ hp
   exact ⟨he.trans ha.leveled,le_mul_of_one_le_right (C.S.a_pos _).le he,mul_le_mul_of_nonneg_left ha.leveled (C.S.a_pos _).le⟩

variable (R:Drop (Bel C.book))
def sinking : (B!).Field 4→ₗ[ℂ](B!).Field 4:=LinearMap.id-(adjStep (p!) 3).comp (R 3)
local notation "cR"=>corrected (V!) (p!) R (shore M k D Z)
omit ha
lemma chart_rep (hG:G.Simple)(hk:4≤D)
    (L:Drop (Bel C.book))(X₁:(B!).Field 3≃ₗ[ℂ] S.Field 3)(he:X₁.toLinearMap=corrected (V!) (p!) L (shore M k D Z) 3)(h₁:X₁ ((B!).unit 3)=S.unit 3) (v:(B!).Field 4) :
    ∃ a:ℂ,L 3 v=a • (B!).unit 3 ∧ corrected (V!) (p!) L (shore M k D Z) 4 v = a • S.unit 4 +
       S.project 4 ((Arche.aligned C M k (Z ⟨4,Nat.lt_succ_of_le hk⟩)) (ladder C 4 (sinking T L v))):=by
    obtain ⟨a,ht⟩:= UVNext.FreeStress.below C.book.grid hG (d:=3) (by norm_num) (L 3 v)
    refine ⟨a,ht,?_⟩
    change corrected (V!) (p!) L _ (3+1) v=_
    rw [correction,← he,LinearEquiv.coe_coe,shore_at _ _ _ _ _ hk]
    congr 1
    rw [ht,map_smul,h₁]; exact ((V!).rise (Nat.le_succ 3)).map_smul a _ |>.trans (congr_arg (a • ·) ((V!).fixs U.phase.transport.injection (H!).laws _))
include T in
lemma rung_quote (v:(B!).Field 3) (a:ℂ) (h:v = a • (B!).unit 3):‖a‖ ≤ ‖(B!).unit 3‖⁻¹ * ‖v‖:=by
   have hp: (B!).unit 3≠0:= (B!).alive 3 T.hT.laws
   rw [h,norm_smul]; exact le_of_eq (by field_simp [(norm_ne_zero_iff.mpr hp)])
lemma ladder_fee {d:ℕ} : ∃ l:ℝ, 0≤l ∧ ∀ v:(B!).Field d,mass C d (ladder C d v) ≤ l*‖v‖:=by
   let e:ℝ:= (↑((C.labels.level d).extra+1):ℝ)
   have he:0 ≤ e:=Nat.cast_nonneg _
   exact ⟨e*‖ladder C d‖,by positivity,fun v=> (mass_le_norm ..).trans ( (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm ..) he).trans_eq (mul_assoc ..).symm)⟩
lemma price_nearby (hG:G.Simple)(U: Final C f S)(M:∀ d,ℕ→RepChart C d)
   (T:MaxwellData C)(L:Drop (Bel C.book)) :
   ∃ J:ℝ,0 < J ∧ ∀ (P:Commission.Port C)(D k:ℕ)(Z:TableL C D) (_: Authentic U M P T k D Z)(_hk:4≤D)
    (X₁:(B!).Field 3≃ₗ[ℂ] S.Field 3)(_:X₁.toLinearMap=corrected U.sector.derivatives T.T.W L (shore M k D Z) 3)(_:X₁ ((B!).unit 3)=S.unit 3)
    (K:(B!).Field 4≃ₗ[ℂ] S.Field 4)(_:K.toLinearMap=corrected U.sector.derivatives T.T.W L (shore M k D Z) 4)
    (_:M 4 k (unitVec (C.labels.level 4) C.path k) = C.refUnit 4),
    let r:= Next.Rank.Station.gap C.path.levels (P.panels D 0).arc k;
    ∀ x:S.Field 4,
    ∃ v : C.label 4,S.project 4 (M 4 k v)=x ∧ mass C 4 v≤ J*(χ k)^8 * ‖K.symm ((r^4:ℝ) • x)‖:=by
   let w:= (sinking T L).toContinuousLinearMap
   let t:= (L 3).toContinuousLinearMap
   let q:= ‖(B!).unit 3‖⁻¹*‖t‖
   obtain ⟨j,hj,hp⟩:=ladder_fee (C:=C) (d:=4)
   let W:=32*j*‖w‖
   have hq:0≤q:=by dsimp [q]; positivity
   have hw:0≤W:=by dsimp [W]; positivity
   refine ⟨1+(q+W),by positivity,?_⟩
   intro P D k Z H hk X hX hY K hK hM r x
   let β:= χ k; let c:=C.S.a k
   obtain ⟨hg,hv,-⟩:= clock_fee _ _ _ _ H
   change c ≤ r at hv; have hc:0<c:= C.S.a_pos _; have hr:0<r:=hc.trans_le hv
   have hβ : 1 ≤ β := hg
   let i:Fin (D+1):=⟨4,Nat.lt_succ_of_le hk⟩
   let e:=K.symm ((r^4:ℝ) • x)
   obtain ⟨a,ht,hv'⟩:= chart_rep U M T hG hk L X hX hY e
   let y:C.label 4:= Z i (ladder C 4 (sinking T L e)); let u:= unitVec (C.labels.level 4) C.path k
   have he: ((↑(r^4):ℂ)) • x= a • S.unit 4 + (↑(c^4):ℂ) • S.project 4 (M 4 k y):=by
      rw [← hK,LinearEquiv.coe_coe,K.apply_symm_apply] at hv'
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), Arche.aligned,LinearMap.smul_apply,map_smul] at hv'; exact hv'
   refine ⟨((↑(r^4):ℂ)⁻¹ * a) • u + (↑((c / r)^4):ℂ) • y,?_,?_⟩
   · have hh : S.project 4 (M 4 k u)=S.unit 4:= by rw [show u=_ from rfl,hM]; rfl
     simp only [map_add,map_smul,hh]
     have hr : (↑(r^4):ℂ)≠0:= by exact_mod_cast pow_ne_zero 4 hr.ne'
     rw [show (↑((c/r)^4):ℂ)= (↑(r^4):ℂ)⁻¹ * (↑(c^4):ℂ) from by push_cast; field_simp,← smul_smul,← smul_smul,← smul_add,← he,inv_smul_smul₀ hr]
   have hp1: mass C 4 y ≤ W*β^8*‖e‖:=by
     apply (spatial_fee U M P T H hk _).trans
     apply (mul_le_mul_of_nonneg_left ((hp _).trans (mul_le_mul_of_nonneg_left (w.le_opNorm _) hj)) (show (0:ℝ)≤32*(χ k)^8 by positivity)).trans_eq; unfold W β; ring
   have hp2: ‖a‖ ≤ q*‖e‖:=
     (rung_quote T _ _ ht).trans ((mul_le_mul_of_nonneg_left (t.le_opNorm _) (inv_nonneg.mpr (norm_nonneg _))).trans_eq (mul_assoc ..).symm)
   have hd : 0 ≤ c/r:=by positivity
   have heq: c/r≤1:=div_le_one_of_le₀ hv hr.le; have hb:1 ≤ β^8:=one_le_pow₀ hβ
   apply le_trans (solid_mass ..)
   rw [supplies_mass (↑((c/r)^4):ℂ),Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hd _),mass_unit,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hr.le _)]
   change _ ≤ (1+(q+W))*β^8*_ -- Notice u let reducible in mass_unit
   rw [show (r^4)⁻¹*‖a‖*C.S.a k^4=(c/r)^4*‖a‖ from by unfold c;field_simp]
   have hg4:= pow_le_one₀ hd heq (n:=4)
   have hu := (mul_le_of_le_one_left (norm_nonneg a) hg4).trans hp2
   have ht := (mul_le_of_le_one_left (mass_nonneg C 4 y) hg4).trans hp1
   refine (add_le_add hu ht).trans ?_
   change _ ≤ (1+(q+W))*β^8*‖e‖
   have hh:= mul_le_mul_of_nonneg_right hb (mul_nonneg hq (norm_nonneg e))
   nlinarith only [hh, mul_nonneg (zero_le_one.trans hb) (norm_nonneg e)]
end YM.RG12.Kintsugi
