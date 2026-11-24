import YM.OPE.Short.Currencies

/-!
# Same-shell cost through the whole stress tree on calibrated measurement scales

Direct bud stretches at each vertex of a comparable cluster circuit meet the
zeroth position comparison. They buy its full physical identity transfer; for
intermediate horizons≤3 those are all the unoccupied-budget charges. The exact
recursive estimate on paths gives simultaneous array evaluations in that
restricted geometry, with no lower determinant extrapolation to subpower-sized
relative scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Extraction Sparse.Tracing Nesting.Motion
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(X:Climb.Scaling S) (hG:G.Simple) (H:Pert.FirstExtension U X)
local notation "Q"=>U.sector.derivatives
namespace Currency
open Sparse.Circuit.Children
-- admissible at an arbitrary shell geometry
def Stayed(M η r:ℝ)(t:Nesting.Tree)(z:t.Plot): Prop:=match t with
 | bud => True
 | fork n f=>WithinRoom r M η (skyline z) (anchor z) ∧ WithinRoom r M η (profile z) (anchor z) ∧ ∀ i,Stayed M η r (f i) (childPlace i z)

variable {M η:ℝ}{n:ℕ}{f:Fin n→Nesting.Tree}
local notation "nodes"=> Nesting.Tree.fork n f
lemma Stayed.budBranch {r:ℝ}{z:(fork n f).Plot}(hz:Stayed M η r (fork n f) z) : WithinRoom r M η (skyline z ∘ ((↑):Bare f→Fin n)) (anchor z) :=⟨fun i=>hz.1.span i.val, fun i j hij=> hz.1.spaced i.val j.val <| fun hv=> hij (Subtype.val_injective hv)⟩
lemma Stayed.within {t:Nesting.Tree}{r:ℝ}{z:t.Plot}(hz:Stayed M η r t z)(ht:t≠bud) : WithinRoom r M η (profile z) (anchor z) :=by obtain (_|_) := t; cases (ht rfl); exact hz.2.1

-- Count each leaf's engineering cost *once* at its actual assembly entry
private lemma bare_count (f:Fin n→Nesting.Tree): 4*Fintype.card (fork n f|>.Leaf)=4*Fintype.card (Bare f)+∑ i:Fin n,fee (f:=f) i:=by
     change 4*Fintype.card (Σ i,(f i).Leaf)= _
     rw [Fintype.card_sigma,Finset.mul_sum] -- dangerous rw dependent Fintype
     have he(j:Fin n):4 * Fintype.card (f j|>.Leaf)= (if f j=bud then 1 else 0)*4 + fee (f:=f) j:=by
         cases hj : f j with
         | bud=> unfold fee; split_ifs with H; swap;· contradiction
                 simp [show Nesting.Tree.bud.Leaf=Unit from rfl]
         | fork m g => unfold fee exponent; rw [hj]; simp
     simp_rw [he]; rw [Finset.sum_add_distrib]; congr 1
     rw [← Finset.sum_mul,Finset.sum_boole, bare_card]
     exact Nat.mul_comm _ _
where bare_card : Fintype.card (Bare f)=(Finset.univ.filter (fun i:Fin n=>f i=bud)).card:=(Fintype.card_subtype (fun i:Fin n=>f i=bud))
lemma countermark (f:Fin n→Nesting.Tree)(r:ℝ): r^(levy (fork n f))= r^(exponent (Bare f)) * (∏ i:Fin n,r^(fee (f:=f) i)):=by
    exact pow_count (by convert bare_count f using 1)
where pow_count {a b:ℕ}{g:Fin n→ℕ}(he:a=b+∑ i,g i) : r^a=r^b * ∏ i,r^(g i):=by rw [he,pow_add, Finset.prod_pow_eq_pow_sum]

variable (h:Services C F S)(hM:0≤M)(hη:0<η)
include hG h H hM hη
lemma complete {t:Nesting.Tree}(D:t.Inner→ ℕ)(ab:Picture t.Leaf)(hd:fledged t D): ∃ A:ℝ, 0≤ A ∧ ∀ᶠ k in atTop,∀ z:t.Plot, z∈Kernel.aperture U R t (boundNow t D) D → Stayed M η (X.r k) t z →
        (X.r k)^(if t=bud then 0 else levy t) * ‖flow U R t z (stressTag U ab) D‖ ≤ A:=by induction t with
  | bud=>exact ⟨1,zero_le_one, Eventually.of_forall fun k z _ _=> by rw [if_pos rfl]; simp [flow]⟩
  | fork n f ih=>
     choose A hA hf using fun i:Fin n=> ih i (childAge i D) (childWages i ab) fun v=>hd (.inr ⟨i,v⟩)
     obtain ⟨B,hB,hf'⟩:= budget U R X hG H (displaying ab) hM hη h
     refine ⟨B* ∏ i,A i,mul_nonneg hB (Finset.prod_nonneg (fun i _=>hA i)),?_⟩
     filter_upwards [eventually_all.mpr hf, hf'] with k hi ht z h' hz
     obtain ⟨u,hu,hu'⟩:= payment.unframe (X.positive k) hz.budBranch
     have hzt: orbitMargin R.port 0 (skyline z) (anchor z):=h'.1 (⟨0,Nat.succ_pos _⟩:_)
     simp_rw [if_neg (show fork n f ≠ bud from by intro h; contradiction)]
     rw [countermark, Entries.charge U R X hG ab z D hd hzt, norm_mul, norm_prod]
     let U' (i:Fin n) (p:(f i).Leaf→S.Tag) := flow U R (f i) (childPlace i z) p (childAge i D)
     let w' (i:Fin n):= U' i (childWages i (stressTag U ab))
     let v:= scalar U R (skyline z ∘ ((↑):Bare f→Fin n)) (stressTag U (displaying ab)) (anchor z)
     have he(i:Fin n):True:=by trivial -- for congr eq
     have hp(i:Fin n): (X.r k)^(fee (f:=f) i)*‖w' i‖ ≤ A i:=by
          change (X.r k)^(fee (f:=f) i) * norm (U' i (childWages i (stressTag U ab))) ≤ _
          have htags: childWages i (stressTag U ab)=stressTag U (childWages i ab):=rfl
          rw [htags]; exact hi i (childPlace i z) (h'.2 i) (hz.2.2 i)
     calc _ = ((X.r k)^exponent (Bare f)*‖v‖) * ∏ i:Fin n,(X.r k)^(fee (f:=f) i)*‖w' i‖ := by
                 rw [Finset.prod_mul_distrib]; change _ * ((∏ i,‖w' i‖) * ‖v‖)= _ * _; ring_nf
          _ ≤ _ :=mul_le_mul (by unfold v; rw [← hu']; apply (ht u hu (anchor z)).1) (Finset.prod_le_prod (fun i _=>mul_nonneg (pow_nonneg (X.positive _).le _) (norm_nonneg _)) (fun i _=>hp i)) (Finset.prod_nonneg (fun i _=>mul_nonneg (pow_nonneg (X.positive ..).le _) (norm_nonneg _))) hB

-- remaining root proof separately

section Declare
omit hG h H hM hη


def reset (D:(fork n f|>.Inner)→ℕ)(i: (fork n f|>.Inner)) := match i with |.inl _=>0 | .inr v=>D (.inr v)
lemma reset_value (D:(fork n f).Inner→ℕ)(ab:Picture (Leaf nodes))(z:_):flow U R nodes z (stressTag U ab) D=flow U R nodes z (stressTag U ab) (reset D) :=by
     apply congr_arg (fun w=>scalar U R (skyline z) w (anchor z)) (funext fun i=> by change issue U R _ _ _ = _; exact congr_arg (fun D=>(issue U R (childPlace i z) (childWages i (stressTag U ab)) D)) (funext (fun (j:(f i).Inner)=>rfl)))
lemma ready(D:(fork n f).Inner→ℕ)(z:_):Kernel.aperture U R (Tree.fork n f) 0 D z → Kernel.aperture U R nodes (boundNow nodes (reset D)) (reset D) z:=by
     rintro ⟨he,hz⟩; refine ⟨he,fun j=>?_⟩; exact (congr_arg (fun g=> Kernel.aperture U R (f j) (boundNow (f j) g) g (childPlace j z)) (funext (fun _=>rfl)) ) ▸ hz j
lemma born(D:(fork n f|>.Inner) →ℕ)(h:∀i:Measuring.Tree.Nonroot f,D (Sum.inr i)≤3): fledged nodes (reset D):=fun i=>by rcases i with i|i; exact Nat.zero_le _; exact h i

private lemma sum_unique {j:ℕ} {a b:R.channels j→ℂ}(h:(∑ i:R.channels j,a i • R.actor j i) = ∑ i,b i • R.actor j i):a=b:=by
    have h': (∑ i,a i • R.basis j i) = ∑ i,b i • R.basis j i:=Subtype.ext (by change (R.stratum j).subtype _ = (R.stratum j).subtype _; simp only [map_sum,map_smul]; exact h)
    exact Eq.trans ((R.basis j).repr_sum_self a).symm ((congr_arg (fun v:R.stratum j=>(fun i=>(R.basis j).repr v i)) h').trans ((R.basis j).repr_sum_self b))

lemma nested_zero(c:R.channels 0)(z:(fork n f).Plot)(w:(fork n f).Leaf→S.Tag)(D:(fork n f).Inner→ℕ):Kernel.chord U R z w c D= R.coef 0 c (skyline z) (voices (each U R z w D)) (anchor z) :=congr_fun (sum_unique U R ((chord_vector U R z (voices w) D 0).trans (R.assemble 0 (skyline z) (voices (each U R z w D)) (anchor z)|>.symm))) c
end Declare
lemma nested_term (i:R.channels 0)(D:(fork n f).Inner→ℕ)(ab:Picture (Leaf nodes))(hd:fledged nodes D): ∃ A:ℝ,0 ≤ A ∧∀ᶠ k in atTop,∀ z:(Tree.Plot (fork n f)),(z∈Kernel.aperture U R (fork n f) (boundNow _ D) D)→ Stayed M η (X.r k) _ z→ ‖Kernel.chord U R z (stressTag U ab) i D‖ ≤ A * (X.r k)^(-(levy nodes:ℝ)):=by
    obtain ⟨A,hC,hF⟩:=complete U R X hG H h hM hη D ab hd
    let c:= R.coef 0 i (sole (0:E4)) (sole (S.unit 0):Labels S fun _:Unit=>0) 0
    refine ⟨A*‖c‖,mul_nonneg hC (norm_nonneg _),?_⟩
    filter_upwards [hF] with k hk z hz ha; let w:=stressTag U ab
    calc _ = ‖flow U R nodes z w D‖ * ‖c‖:= (congr_arg norm ((nested_zero U R ..).trans (first_coef U R X hG i (skyline z) (each U R z w D) (anchor z)))).trans (norm_mul ..)
         _ ≤ _:= by rw [Real.rpow_neg (X.positive _).le, Real.rpow_natCast, ← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos (X.positive _) _)).mpr (Eq.trans_le (by ring) (mul_le_mul_of_nonneg_right (by simpa only [reduceCtorEq, if_false] using (hk z hz ha) : X.r k ^ levy nodes * ‖flow U R nodes z w D‖ ≤ A) (norm_nonneg _)))
end Currency
end YM.OPE.Short
