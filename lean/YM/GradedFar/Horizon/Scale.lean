import YM.GradedFar.Horizon.Garage

/-!
# Dyadic G.2 budgets (polynomial bounds only, needed for G.6)
For H-framed mark inputs with fixed horizon & for endpoints on any actual filtration.
-/
namespace YM.FVA2.GradedFar.Horizon
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth Pose Moving
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable [NormedAddCommGroup E][NormedSpace ℂ E]

local notation "Ch"=> RowSpace G d
local notation "Tn"=> Toon G d

def keep (e : ℕ): Maps G d:= LinearMap.toContinuousLinearMap (LinearMap.pi fun b:Tn=> if b.size<e then 0 else LinearMap.proj b)
lemma keeps (b : Tn) (e : ℕ) (x : Ch): keep e x b=if b.size<e then 0 else x b := by
    unfold keep; change (if _ then (0 : Ch →ₗ[ℂ] ℂ) else LinearMap.proj b) x = _; split <;> rfl
lemma keeper (e : ℕ) : ‖keep (G:=G) (d:=d) e‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun b=> ?_ ; rw [keeps,one_mul]; split; · rw [norm_zero]; positivity
    exact norm_le_pi_norm ..
lemma retained (F : Ch →L[ℂ] E) (e : ℕ) (hF : ∀ b : Tn, b.size<e → F (chair G d (theory b))=0) : F ∘L keep e = F := by
    ext1 x; obtain ⟨x,rfl⟩:=(chair G d).surjective x
    have ht (b : Tn) : keep e (chair G d (theory b))=if b.size<e then (0:Ch) else chair G d (theory b):= by
      ext1 i; by_cases hh:i=b; · subst i; rw [keeps]; split_ifs <;> rfl
      rw [keeps]; split_ifs <;> first | rfl | (simp only [fee_elt,pivotδ, if_neg (Ne.symm hh)] <;> rfl)
    rw [← reconstructed x,map_sum,map_sum,map_sum]; refine Finset.sum_congr rfl fun b _=>?_ ; rw [_root_.map_smul (f:=chair G d), _root_.map_smul, _root_.map_smul]; simp_rw [ContinuousLinearMap.comp_apply, ht]; split_ifs with he; · rw [map_zero,hF b he]
    rfl
lemma units_go (s : ℝ) (hs : 0 ≤ s) (e : ℕ) :
    ‖(keep (G:=G) (d:=d) e) ∘L engine G d (-s)‖≤(exp s ^ e)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x; apply (pi_norm_le_iff_of_nonneg (by positivity)).2; intro b
    rw [ContinuousLinearMap.comp_apply,keeps,engine_amount]; split_ifs with hi; · rw [norm_zero]; positivity
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (exp_pos _|>.le),Real.exp_neg,inv_pow]
    exact mul_le_mul (inv_anti₀ (by positivity) (pow_le_pow_right₀ (Real.one_le_exp hs) (le_of_not_gt hi)))
      (norm_le_pi_norm ..) (norm_nonneg _) (by positivity)

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
  (θ:ℝ→ℝ) (Z:Rolled G d) (h : PFrame N M (Zenith Z) θ 1)
include H h
lemma pushed (F : ℝ→(Ch→L[ℂ] E))
    (hq : ∀ᶠ r in τ, ∀ s∈ Growth.Small,F r=F (resize r s) ∘L downward Z r s)
    (e : ℕ) (hr : ∀ᶠ r in τ,∀ b : Tn,b.size<e → F r (chair G d (theory b))=0) :
    ∃ k : ℕ,∃ C : ℝ,0 < C ∧ ∀ᶠ r in τ, ‖F r‖ ≤ C*r^e * (1+degrees r)^k := by
  -- normalize by r^(-e)
  let f r:= (|r|⁻¹)^e * ‖F r‖
  obtain ⟨C,hC,h⟩:= step_fee N M H θ Z h
  let D:= (exp doubling)^e*C
  have hs' : ∀ᶠ r in τ, ∀ s∈ Growth.Small,∀ b : Tn, b.size<e → F (resize r s) (chair G d (theory b))=0 := by
    have hs' := (span_nears filed N M Prod.fst (fun i:ℝ × ↥Growth.Small => i.2.val) tendsto_comap
      (Eventually.of_forall fun i=> i.2.property) H).eventually hr
    exact (eventually_comap.mp hs').mono fun r h s hs => h (r,⟨s,hs⟩) rfl
  obtain ⟨k,P,hP,h⟩:= advances simple (C:=D) (show ∀ r, 0 ≤ f r from fun r=> by unfold f; positivity) (by unfold D; positivity) (by
    filter_upwards [hq,h,positive_g simple,self_mem_nhdsWithin,hr,hs'] with r hq h hp (hr' : r∈Ioi 0) hr hs
    intro s hc
    let t:= exp s; let u:= resize r s; let T:ℝ:=t^e; let W:=F u
    let A:=engine G d (-s); let Y:=downward Z r s
    have hf : 0 < r:=hr'; have ht : 0<t:= exp_pos _; have hw : 0 < u:= mul_pos hf ht; have hT : 0 < T := pow_pos ht _
    let L':= ‖W‖
    have hz : ‖W ∘L A‖≤ L'*T⁻¹:= by rw [← retained W e (hs s hc), ContinuousLinearMap.comp_assoc];
                                                    exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul_of_nonneg_left (units_go _ hc.1 _) (norm_nonneg _))
    have hk : ‖W ∘L (Y-A)‖≤ L'*(C*g r^2) := (ContinuousLinearMap.opNorm_comp_le ..).trans
      (mul_le_mul_of_nonneg_left (h s hc).2 (norm_nonneg _))
    have hj : ‖F r‖≤ (1+D*g r^2) * (L' * T⁻¹) := by
      have hk' : ‖F r‖≤ L' * (C*g r^2) + L'*T⁻¹ := by
        rw [hq s hc,← show W ∘L (Y-A)+W ∘L A=W ∘L Y by rw [ContinuousLinearMap.comp_sub,sub_add_cancel]]; exact (norm_add_le ..).trans (add_le_add hk hz)
      apply hk'.trans
      have he' : T ≤ exp doubling ^ e:= pow_le_pow_left₀ ht.le (Real.exp_le_exp.mpr hc.2) e
      have hv : L' * (C*g r^2) ≤ D*g r^2 * (L'*T⁻¹) := by
        have ht' : T⁻¹ * (exp doubling)^e ≥ 1 := by rw [inv_mul_eq_div]; exact (one_le_div hT).mpr he'
        calc
         L' * (C*g r^2) ≤ (T⁻¹ * (exp doubling)^e) * (L' * (C*g r^2)) := by
           conv_lhs=>rw [← one_mul (L'*(C*g r^2))]
           apply mul_le_mul_of_nonneg_right ht'; unfold L'; positivity
         _ = _ := by unfold D; ring
      linarith only [hv]
    unfold f; rw [abs_of_pos hf,abs_of_pos (show 0 < resize r s from hw)]
    change _ ≤ (1+D* g r^2)*(u⁻¹^e * L'); exact ((mul_le_mul_of_nonneg_left hj (show 0≤(r⁻¹)^e from by positivity))).trans_eq (by unfold u resize T t; rw [mul_inv_rev,mul_pow,inv_pow]; ring))
  refine ⟨k,P,hP,(h.and (show ∀ᶠ r in τ,0<r from self_mem_nhdsWithin)).mono fun r ⟨hh,hr⟩=> ?_⟩
  unfold f at hh; rw [abs_of_pos hr,inv_pow, inv_mul_eq_div] at hh
  exact ((div_le_iff₀ (pow_pos hr _)).mp hh).trans_eq (by ring)

/-- Inverse price on the entire fixed-physical through-cap arguments. -/
lemma fetched (F : ℝ→(E →L[ℂ] Ch))
    (hq : ∀ᶠ r in τ, ∀ s∈ Growth.Small, F r= Zenith Z r s ∘L F (resize r s)) :
    ∃ k : ℕ,∃ C : ℝ,0 < C ∧ ∀ᶠ r in τ, ‖F r‖ ≤ r⁻¹^d * C * (1+degrees r)^k := by
  let f r:= |r|^d * ‖F r‖
  obtain ⟨C,hC,h⟩:= step_fee N M H θ Z h
  obtain ⟨k,P,hP,h⟩:= advances simple (C:=C) (show ∀ r, 0 ≤ f r from fun r=> by unfold f; positivity) hC (by
    filter_upwards [hq,h,positive_g simple,self_mem_nhdsWithin] with r hq h hp (hr' : r∈Ioi 0)
    intro s hc
    let t:= exp s; let u:= resize r s; let T:ℝ:=t^d; let W:=F u
    let A:=engine G d s; let Y:= Zenith Z r s
    have hf : 0 < r:=hr'; have ht : 0<t:= exp_pos _; have hw : 0 < u:= mul_pos hf ht; have hT : 1 ≤ T := one_le_pow₀ (Real.one_le_exp hc.1)
    have hj : ‖F r‖≤ (1+C*g r^2)*T * ‖W‖:= by
      rw [hq s hc]; apply le_trans (ContinuousLinearMap.opNorm_comp_le ..); apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have he : ‖Y-A‖≤ C*g r^2:= (h s hc).1
      have hZ:= norm_add_le (Y-A) A; rw [sub_add_cancel] at hZ
      have hx:‖A‖≤T:=engine_pos_bound _ hc.1 d
      have hk:=mul_nonneg (show 0 ≤ C*g r^2 by positivity) (show 0 ≤ T-1 from sub_nonneg.mpr hT)
      change ‖Y‖ ≤ _; nlinarith only [he,hZ,hx,hk]
    unfold f; rw [abs_of_pos hf,abs_of_pos hw]; exact ((mul_le_mul_of_nonneg_left hj (show 0≤r^d from by positivity))).trans_eq (by unfold W T t u resize; rw [mul_pow]; ring))
  refine ⟨k,P,hP,(h.and (show ∀ᶠ r in τ,0<r from self_mem_nhdsWithin)).mono fun r ⟨hh,hr⟩=> ?_⟩
  unfold f at hh; rw [abs_of_pos hr, mul_comm (r^d)] at hh
  exact ((le_div_iff₀ (pow_pos hr _)).mpr hh).trans_eq (by rw [inv_pow]; ring)
end
end YM.FVA2.GradedFar.Horizon
