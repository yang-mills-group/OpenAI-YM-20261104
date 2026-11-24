import YM.Contact.Order
import YM.Contact.Gaps

/-! An auxiliary non-field-local extension on one normalized band of normal positions. No
numerical subtractions here are used to define PT coefficients. The choice of full-extension
norm is controlled simultaneously for every bound `Due` on the same separated function. -/

noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open Set Metric Filter Function MeasureTheory LinearMap
open scoped Topology ContDiff BigOperators NNReal
variable {k:ℕ}

def flat (k m:ℕ) : Submodule ℂ (Trial (Points k)) where
  carrier:={φ|∀i<m,∀ x:(Points k), x∉airborne k → iteratedFDeriv ℝ i φ x=0}
  zero_mem':=by
    intro i _ x _; change iteratedFDeriv ℝ _ (fun _:Points k=> (0:ℂ)) x=0; rw [iteratedFDeriv_fun_zero];rfl
  add_mem':=by rintro φ ψ h hψ i hi x hx
               rw [show ⇑(φ+ψ)=(φ:Points k→ℂ)+ψ from rfl,iteratedFDeriv_add (φ.orders _) (ψ.orders _), Pi.add_apply,h i hi x hx,hψ i hi x hx,add_zero]
  smul_mem':=by intro z v hv i hi x hx
                rw [show ⇑(z • v)= z • (v:Points k→ℂ) from rfl,iteratedFDeriv_const_smul_apply (v.orders _|>.contDiffAt),hv i hi x hx,smul_zero]

set_option quotPrecheck false
local notation "E!"=>Points k

lemma flat_norm {m:ℕ}{φ:Trial (Points k)}(h:φ∈flat _ m){B:ℝ}(hm:Major m φ B) (x:Points k) : ‖φ x‖≤ (gap x)^m * B:=by
  by_cases hv:x∈airborne k
  case neg=> cases m; · simpa only [pow_zero,one_mul] using hm.value x
             have hs := (h 0 (Nat.zero_lt_succ _) x hv)
             rw [show ‖φ x‖=0 from (norm_iteratedFDeriv_zero (𝕜:=ℝ)).symm.trans (congr_arg norm hs|>.trans norm_zero)]
             have hb:=gap_nonneg x
             exact mul_nonneg (pow_nonneg hb _) hm.nonneg
  have _hp:=gap_pos _ hv
  have hP:{p:Fin (k+1) × Fin (k+1)|p.1≠p.2} ⊆ Set.univ:= subset_univ _
  by_cases he:gap x =1
  · simpa only [he,one_pow,one_mul] using hm.value x
  have he:gap x<1:=lt_of_le_of_ne (gap_le_one ..) he
  -- choose a closest pair if gap not capped; named due to `value` being private before
  let val' (i:Option (Fin (k+1)×Fin (k+1))):= i.elim (1:ℝ) fun z=> if z.1=z.2 then 1 else ‖(differences k x) z.1-(differences k x) z.2‖
  obtain ⟨l,_,hl⟩:= Finset.exists_mem_eq_inf' (s:=Finset.univ) Finset.univ_nonempty val'
  change gap x =val' l at hl; cases l with
  | none => linarith only [he,(show gap x=1 from hl)]
  | some p=>
    obtain ⟨i,j⟩:=p; simp only [val',Option.elim_some] at hl; split_ifs at hl with hij
    · exact (he.not_ge hl.ge).elim
    let y:=differences k x
    let a:= PiLp.single 2 (β:=fun _:Fin (k+1)=>E4) i (y j-y i)
    let x':=jacobi k (y+a)
    have h':x'∉airborne k:=by
      intro hc; apply hij; apply (hc:Injective _); apply (sub_eq_zero.mp);rw [show x'=jacobi k _ from rfl,← centered_sub]
      change (y+a) i-(y+a) j = 0
      simp only [PiLp.add_apply,a,PiLp.single_eq_same,PiLp.single_eq_of_ne _ (Ne.symm hij),add_zero]; abel
    have hh:‖x-x'‖≤gap x:=by
      dsimp [x']; rw [jacobi_add, show jacobi k y=x by simpa [gen] using jacobi_gen k (0:E4) x]
      rw [show x-(x+_)= -(jacobi _ a) from by abel,norm_neg]
      exact (norm_relative _ a).trans_eq (PiLp.norm_single ..|>.trans ((norm_sub_rev ..).trans hl.symm))
    cases m; · simpa using hm.value x
    rename_i m; have hf: polynomial m φ x' x=0:= Finset.sum_eq_zero (fun i hi=> by change _ • (iteratedFDeriv ..) _=0; rw [h i (Finset.mem_range.mp hi) _ h']; simp)
    have H:=taylor_est hm x' x; rw [hf,sub_zero] at H
    exact H.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hh _) hm.nonneg)

def band (k:ℕ) := (airborne k) ∩ (norm:Points k→ℝ) ⁻¹' Set.Ioo (1/2:ℝ) 4  -- replace
lemma band_open (k:ℕ): IsOpen (band k):= IsOpen.inter (airborne_open k) ((isOpen_Ioo.preimage continuous_norm))

def Due (f:Points k→ℂ)(m:ℕ)(c:ℝ) : Prop := 0≤c∧ ∀ x∈band k, ‖f x‖≤ c*(gap x)⁻¹^m

lemma exists_fee {f:Points k→ℂ} {m:ℕ}(h:Set.Nonempty {c | Due f m c}):
  ∃ c:ℝ, Due f m c ∧ ∀ c', Due f m c' → c≤2*c':=by
  classical
  set I:= {c | Due f m c}; let c:=sInf I
  have hB:BddBelow I:=⟨0,fun r hr=>hr.1⟩
  have hc:c≥0:= le_csInf h (fun r (hr:Due f m r)=>hr.1) -- bddbelow choose? wrong, replace
  by_cases he:c=0
  · refine ⟨c,⟨hc,?_⟩,fun r hr=>by linarith only [hr.1,he]⟩
    intro x hx; have hh:0 < (gap x)⁻¹^m:= pow_pos (inv_pos.mpr (gap_pos _ hx.1)) _
    rw [he,zero_mul]; apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨r,hr,hd⟩:= exists_lt_of_csInf_lt h (show c<ε*(gap x)^m by rw [he]; exact mul_pos hε (pow_pos (gap_pos _ hx.1) _))
    rw [zero_add]; exact (hr.2 x hx).trans ((mul_le_mul_of_nonneg_right hd.le hh.le).trans_eq (by rw [inv_pow,mul_assoc,mul_inv_cancel₀ (pow_pos (gap_pos _ hx.1) ..).ne',mul_one]))
  · obtain ⟨r,hr,hJ⟩:= exists_lt_of_csInf_lt h (show c<2*c by have hpos:= lt_of_le_of_ne hc (Ne.symm he);linarith)
    exact ⟨r,hr,fun b hb=> le_trans hJ.le (mul_le_mul_of_nonneg_left (csInf_le hB hb) (by norm_num))⟩

def fee (f:Points k→ℂ)(m:ℕ)(h:Set.Nonempty {c | Due f m c}) : ℝ := (exists_fee h).choose
lemma fee_due {f:Points k→ℂ}(m)(h:Set.Nonempty {c | Due f m c}): Due f m (fee f m h) := (exists_fee h).choose_spec.1
lemma fee_le {f:Points k→ℂ}(m)(h:Set.Nonempty {c | Due f m c}) {C:ℝ}(hc:Due f m C): fee f m h ≤2*C:= (exists_fee h).choose_spec.2 _ hc

variable {f:Points k→ℂ} {m:ℕ}
def bandAverage (f:E!→ℂ)(φ:Trial (Points k)) := ∫ x, ((band k).indicator f x)*φ x

def bandMass(k:ℕ):=(volume:Measure (Points k)).real (ball 0 4)

variable (hf:ContinuousOn f (band k)) (h:Set.Nonempty {c | Due f m c}) (φ:Trial (Points k))(hφ:φ∈flat k m)

include hφ hf h
set_option linter.unusedVariables false in
lemma band_integrable {B:ℝ}(hB:Major m φ B):
    Integrable (fun x:E!=> (band k).indicator f x * φ x) ∧ ‖bandAverage f φ‖ ≤ (fee f m h * bandMass k)*B:=by
   set c:=fee f m h; let s:= band k; let g(x:E!):=s.indicator f x*φ x; let b: Set (Points k):=ball 0 4
   have hl:MeasurableSet s:= IsOpen.measurableSet (band_open k)
   have hg:Measurable g:= by
      refine Measurable.mul (measurable_of_restrict_of_restrict_compl hl ?_ ?_) φ.continuous.measurable
      · change Measurable (s.restrict (s.indicator f)); rw [show s.restrict (s.indicator f)=s.restrict f from funext fun x=> indicator_of_mem x.property _]; exact (continuousOn_iff_continuous_restrict.mp hf).measurable
      · change Measurable (sᶜ.restrict (s.indicator f))
        rw [show sᶜ.restrict (s.indicator f)=fun _=>0 from ?_]; exact measurable_const
        exact funext fun x=> indicator_of_notMem x.property _
   have he:g=b.indicator g:=funext (fun x=> (by by_cases hw:x∈b; exact (indicator_of_mem hw g).symm; unfold g; rw [indicator_of_notMem hw, indicator_of_notMem (fun (hy:x∈s)=>hw (by exact mem_ball_zero_iff.mpr hy.2.2)),zero_mul]))
   have ht(x): ‖g x‖ ≤ c*B :=by
      by_cases hx:x∈s
      · unfold g;rw [indicator_of_mem hx,norm_mul]; exact le_trans (mul_le_mul ((fee_due _ _).2 x hx) (flat_norm hφ hB x) (norm_nonneg _) (mul_nonneg ((fee_due ..).1) (pow_nonneg (inv_pos.mpr (gap_pos x hx.1)).le _))) (by change c*((gap x)⁻¹^m)*(_*_) ≤ _; rw [inv_pow,← mul_assoc _ _ B,mul_assoc c, inv_mul_cancel₀ (pow_pos (gap_pos x hx.1) _).ne',mul_one])
      unfold g;rw [indicator_of_notMem hx,zero_mul,norm_zero]; exact mul_nonneg (fee_due ..|>.1) hB.nonneg
   haveI : IsFiniteMeasure (volume.restrict b):= by apply isFiniteMeasure_restrict.mpr; exact measure_ball_lt_top.ne
   have hb:MeasurableSet b:= measurableSet_ball
   have hh:Integrable (b.indicator g):= integrable_indicator_iff hb |>.2 <| Integrable.of_bound hg.aestronglyMeasurable (c*B) (Eventually.of_forall ht)
   refine ⟨hh.congr (Eventually.of_forall fun x=>congr_fun he.symm x),?_⟩; change ‖∫ x,g x‖≤ _; rw [he,integral_indicator hb]
   exact (norm_integral_le_of_norm_le_const (Eventually.of_forall ht)).trans_eq (by dsimp only [bandMass];simp only [measureReal_def,Measure.restrict_apply,MeasurableSet.univ,Set.univ_inter]; linarith)

omit hφ
def bandLM (hf:ContinuousOn f (band k)) (h:Set.Nonempty {c | Due f m c}) : flat k m →ₗ[ℂ] ℂ where
  toFun φ:= bandAverage f φ
  map_add' φ ψ:=by
     unfold bandAverage;change (∫ _,_ * ((φ.val+ψ.val) _))= _
     simp_rw [_root_.add_apply,mul_add]; exact integral_add (band_integrable hf h φ φ.property (Classical.choose_spec (Trial.majorant m φ.val))|>.1) (band_integrable hf h ψ ψ.property (Classical.choose_spec (Trial.majorant m ψ.val))|>.1)
  map_smul' c φ:=by
     unfold bandAverage;change (∫ _,_ * ((c • φ.val) _))= _; simp_rw [_root_.smul_apply,smul_eq_mul,mul_left_comm (_:ℂ) c]; exact integral_const_mul ..

lemma bandLM_bound (v:flat k m): ‖bandLM hf h v‖ ≤ ((fee f m h * bandMass k)*seminorm E! m v):= (band_integrable hf h v v.property (controls_order E! m _)).2
omit hf h in

lemma bandMass_nonneg (k):0≤bandMass k := by unfold bandMass;rw [measureReal_def]; positivity
lemma band_support_hahn :
    ∃ p:Trial E!→ₗ[ℂ] ℂ, (∀ (x : ↥(flat k m)), p x.val=(bandLM hf h) x) ∧ ∀ (x : Trial E!), ‖p x‖ ≤ (fee f m h * bandMass k)*seminorm E! m x:=by
    let c:ℝ≥0:=⟨fee f m h * bandMass k,mul_nonneg (fee_due ..|>.1) (bandMass_nonneg _)⟩
    exact Module.Dual.exists_extension_of_le_seminorm _ (bandLM hf h) (p:= c • (seminorm E! m)) (bandLM_bound hf h)
-- Fix the entire stencil once, including size bound, over the unscaled annular inputs.
def kernelLM (hf:ContinuousOn f (band k)) (h:Set.Nonempty {c | Due f m c}) : Trial E!→ₗ[ℂ] ℂ := (band_support_hahn hf h).choose
lemma kernelLM_flat (hφ:φ∈flat k m) : kernelLM hf h φ = bandAverage f φ := (band_support_hahn hf h).choose_spec.1 ⟨φ,hφ⟩
lemma kernelLM_cost {c:ℝ}(hh:Due f m c) {B}(hb:Major m φ B):‖kernelLM hf h φ‖≤ 2*c*bandMass k*B:= ((band_support_hahn hf h).choose_spec.2 _).trans
       (mul_le_mul (mul_le_mul_of_nonneg_right (fee_le m h hh) (bandMass_nonneg _)) (order_le' E! m hb) (sem_nonneg E! m _) (mul_nonneg (by positivity [hh.1]) (bandMass_nonneg _)))
end YM.Contacts
