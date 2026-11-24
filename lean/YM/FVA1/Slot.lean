import YM.RG05.Cadre.Paint

/-! # Occurrence markers with multilinear test coefficients

Charge the basis/reference output *once* in the sum-of-images norm, i.e.
when substituting a multilinear coefficient which is bounded by the inverse
input toll, use an envelope costing one for the complete image re-expressed
in any actual slot/test coordinates. Constants are independent of the number
of occurrence markers used to present the different multilinear alternatives.
This intermediate alphabet is used only at an exact step, not as a physical
marker horizon.
-/

set_option autoImplicit false
noncomputable section

namespace YM.FVA1
open Finset Marker Extra.Trajectories RG05.Strand
open scoped Topology BigOperators Classical

variable {I V T : Type*} [DecidableEq I] [DecidableEq V] {R : Census V}

/-- The unconstrained alphabet used to record every input occurrence in one scalar run. -/
def FreeCensus (I : Type*) [DecidableEq I] [Fintype I] : Census I where
  choices := univ
  blank := mem_univ _
  solo _ := mem_univ _
  down _ _ _ := mem_univ _

theorem free_all [Fintype I] : Whole (FreeCensus I) := fun _ => mem_univ _

variable (tag : I → R.Mode) (charge : I → ℂ)

def leafName (i : I) : Poly R := Poly.send (tag i) (charge i)

omit [DecidableEq I] in
lemma leafName_sq (h : ∀ i, (tag i).val.Nonempty) (i : I) :
    leafName tag charge i * leafName tag charge i = 0 := by
  by_contra h'
  obtain ⟨z,h₁,_⟩:= merges_of_tagged_mul h'
  obtain ⟨j,hj⟩:= h i
  exact Finset.disjoint_left.mp h₁ hj hj

omit [DecidableEq I] in
lemma leafName_quiet (h : ∀ i, (tag i).val.Nonempty) (i : I) :
    (leafName tag charge i).part R.quiet=0:= by
  rw [leafName,Poly.part_send,if_neg (fun he=> (h i).ne_empty
    (show (tag i).val=∅ from congr_arg Subtype.val he.symm))]

variable [Fintype I]
/-- Substitutes one possibly mixed physical mark (with test coefficient) for each occurrence mark. -/
def decoder : Poly (FreeCensus I) →ₗ[ℂ] Poly R :=
  paints (leafName tag charge) (FreeCensus I)

lemma dec_leaf (i : I) (c : ℂ) :
    decoder tag charge (Poly.send ((FreeCensus I).fire i) c) = c • leafName tag charge i :=
  paint_knot ..

lemma dec_one : decoder tag charge 1 = 1 := paint_one ..
lemma dec_mul (h : ∀ i, (tag i).val.Nonempty) (a b : Poly (FreeCensus I)) :
    decoder tag charge (a*b) = decoder tag charge a * decoder tag charge b :=
  paint_mul _ (leafName_sq tag charge h) free_all ..

lemma dec_pow (h : ∀ i, (tag i).val.Nonempty) (a : Poly (FreeCensus I)) (n : ℕ) :
    decoder tag charge (a^n) = decoder tag charge a ^ n:= by
  induction n with
  | zero => simp [dec_one]
  | succ n ih => rw [pow_succ,pow_succ,dec_mul _ _ h, ih]

def decMode (s : Finset I) : R.Mode → ℂ := fun θ=>
  if hv : Fits tag s then if unionTag tag s hv=θ then ∏ i∈s,charge i else 0 else 0

lemma dec_atom (a : (FreeCensus I).Mode) (v : ℂ)(θ:R.Mode) :
    (decoder tag charge (Poly.send a v)).part θ=v * decMode tag charge a.val θ:= by
  rw [decoder,paint_send,Poly.part_smul]; congr 1
  unfold leafName decMode
  split
  next h=> rw [tagged_prod tag a.val h,Poly.part_send]; simp only [eq_comm]
  next h=>
    have hZ:(∏ i∈a.val, Poly.send (tag i) (charge i))=0:= by
      by_contra h'; exact h (fits_of_tagged_prod tag h')
    rw [hZ,Poly.part_nil]

lemma dec_part (a : Poly (FreeCensus I)) (θ : R.Mode):
    (decoder tag charge a).part θ=
      ∑ i, a.part i * decMode tag charge i.val θ:= by
  conv_lhs => rw [← Poly.studs a,map_sum,Poly.part_sum]
  exact sum_congr rfl fun i _=> dec_atom ..

private lemma not_quiet {θ:R.Mode} (h:θ.val.Nonempty) : θ≠ R.quiet:=
  fun h' => h.ne_empty (congr_arg Subtype.val h')

omit [DecidableEq I] [Fintype I] in
private lemma union_nonempty (h : ∀ i,(tag i).val.Nonempty) (s:Finset I)(hs:s.Nonempty) :
    (s.biUnion fun i=> (tag i).val).Nonempty := by
  obtain ⟨i,hi⟩:=hs
  exact (h i).mono (Finset.subset_biUnion_of_mem _ hi)

lemma dec_quiet (h : ∀ i,(tag i).val.Nonempty) (a : Poly (FreeCensus I)) :
    (decoder tag charge a).part R.quiet=a.part (FreeCensus I).quiet:= by
  rw [dec_part, sum_eq_single (FreeCensus I).quiet];
  · simp only [Census.quiet,decMode,dif_pos (fits_empty tag),unionTag,biUnion_empty,
      ite_true,prod_empty,mul_one]
  · intro b _ hb; rw [decMode]; split
    next hf=> rw [if_neg (not_quiet (union_nonempty tag h b.val (nonempty_iff_ne_empty.mpr fun he=> hb (Subtype.ext he)))),mul_zero]
    next _=> rw [mul_zero]
  simp

omit [DecidableEq I] [Fintype I] in
private lemma pass_at {A: Type*}[DecidableEq A][Fintype A]{P:Census A}(n:ℕ)(hn:Fintype.card A ≤ n)
    (a : Poly P)(ha:a.part P.quiet=0): Poly.pass a=∑ i∈range (n+1),(i.factorial:ℂ)⁻¹ • a^i:= by
  apply sum_subset (range_mono (by omega))
  intro i _ hi; rw [Poly.stops a ha i (by simp only [mem_range,not_lt] at hi; omega),smul_zero]

lemma dec_pass [Fintype V] (h : ∀ i,(tag i).val.Nonempty) (a : Poly (FreeCensus I))
    (ha:a.part (FreeCensus I).quiet=0): decoder tag charge (Poly.pass a)=Poly.pass (decoder tag charge a):=by
  let M:=max (Fintype.card I) (Fintype.card V)
  rw [pass_at M (le_max_left ..) a ha, pass_at M (le_max_right ..) _ ((dec_quiet _ _ h _).trans ha),map_sum]
  simp_rw [map_smul,dec_pow tag charge h]

open Push.GridApprox.Nil

variable (cost : I → ℝ)

def decFee (s : Finset I) : R.Mode → ℝ := fun θ=>
  if hv : Fits tag s then if unionTag tag s hv=θ then ∏ i∈s,cost i else 0 else 0

def decSheet (f : Sheet (FreeCensus I)) : Sheet R := fun θ=>
  ∑ i, f i * decFee tag cost i.val θ

omit [DecidableEq I] [Fintype I] in
lemma fee_pos (h:∀ i,0≤ cost i)(s:Finset I): 0 ≤ decFee tag cost s :=by
  intro i; change 0 ≤ if hv : Fits tag s then _ else _; split
  next h' => split; exact prod_nonneg fun i _=>h i; exact le_rfl
  next _=> exact le_rfl

lemma sheet_pos (h:∀ i,0≤ cost i) {a:Sheet (FreeCensus I)} (ha:0≤a):0 ≤ decSheet tag cost a:=by
  intro i; exact sum_nonneg (fun j _=> mul_nonneg (ha j) (fee_pos tag cost h _ _))

omit [DecidableEq I] [Fintype I] in
lemma fee_cap (h:∀ i,‖charge i‖ ≤ cost i)(s:Finset I)(i:R.Mode):
    ‖decMode tag charge s i‖ ≤ decFee tag cost s i:= by
  unfold decMode decFee
  split_ifs;
  · rw [norm_prod]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> h j)
  all_goals simp

lemma sheet_cap (h:∀ i,‖charge i‖ ≤ cost i)(a:Poly (FreeCensus I)){u:Sheet (FreeCensus I)}
    (ha:∀ i, ‖a.part i‖ ≤ u i) (θ:R.Mode) : ‖(decoder tag charge a).part θ‖ ≤ decSheet tag cost u θ:= by
  unfold decSheet; rw [dec_part]; apply (norm_sum_le ..).trans (sum_le_sum ?_)
  intro i _; rw [norm_mul]
  exact mul_le_mul (ha i) (fee_cap tag charge cost h _ _) (norm_nonneg _) ((norm_nonneg _).trans (ha i))

-- even if only bounded on unit tests, fees can be applied to any arrays on those same unit tests.
omit [DecidableEq I] [Fintype I] in
lemma fee_price (s:Finset I)(ρ:I→ℝ)(w:V→ℝ)(h:∀ i, Poly.toll w (tag i)*cost i ≤ ρ i)
    (hw:∀ i,0<w i)(hc:∀ i,0≤cost i):
    wordsPrice w (decFee tag cost s) ≤ ∏ i∈s,ρ i:=by
  by_cases hp: Fits tag s
  · unfold wordsPrice; rw [sum_eq_single (unionTag tag s hp)]
    · simp_rw [decFee,dif_pos hp, if_true,toll_union tag]; rw [← prod_mul_distrib]; exact prod_le_prod (fun i _=>mul_nonneg (Poly.worth hw _).le (hc i)) (fun i _=> h i)
    · intro i _ hi; simp [decFee,hi.symm,hp]
    simp
  simp_rw [wordsPrice,decFee,dif_neg hp,mul_zero,sum_const_zero]; exact prod_nonneg (fun i _=> (mul_nonneg (Poly.worth hw _).le (hc i)).trans (h i))

lemma sheet_price (a:Sheet (FreeCensus I))(ha:0 ≤ a)(ρ:I→ℝ)(w:V→ℝ)(h:∀ i, Poly.toll w (tag i)*cost i ≤ ρ i)
    (hw:∀ i,0<w i)(hc:∀ i,0≤cost i):
    wordsPrice w (decSheet tag cost a) ≤ wordsPrice ρ a:=by
  unfold wordsPrice decSheet; simp_rw [Finset.mul_sum]; rw [sum_comm]; refine sum_le_sum fun i _=>?_
  have he : (∑ j:R.Mode,Poly.toll w j*(a i*decFee tag cost i.val j))=wordsPrice w (decFee tag cost i.val)*a i:=by
    unfold wordsPrice; rw [sum_mul]; exact sum_congr rfl fun j _=> by ring
  rw [he]; exact mul_le_mul_of_nonneg_right (fee_price tag cost _ ρ w h hw hc) (ha _)

end YM.FVA1
