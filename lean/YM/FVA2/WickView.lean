import YM.FVA2.Boson

/-!
# Ordinary Gaussian evaluation embedded as MS.Swirl.View
Physical Taylor extraction here compares Chill(full-price), for arbitrary
positive `Law`; applies in particular to the fixed inversion-even Wilson
saddle in based coordinates. Antighost rows removed previously.
-/
set_option maxHeartbeats 600000
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Boson
open Filter PertExtension Function FormalOPE.RG10 FormalOPE.RG10.MultiGauge GaussianScore
open MeasureTheory
open MeasureTheory.Measure (IsAddHaarMeasure)
open MS MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater Finset PowerSeries PairCoords Paper
open scoped Topology Classical ContDiff
variable {E U A J:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (m: Module.Basis U ℝ E) (Γ: Law E)
abbrev maintain : Slot U J→ E := Sum.elim m (fun _=>0)
omit [FiniteDimensional ℝ E] in
lemma mark (x:Slot U J)(h:φ x=true): maintain m x=0:= by cases x; contradiction; rfl

local notation "Y" => fun p q:U=> (Γ.wick (m.coord p) (m.coord q):ℂ)
local notation "μB" => major (J:=J) (Y)
local notation "INK" => ink (maintain (J:=J) m)
variable (J)[Fintype U][Fintype J]

private lemma basis_law (A B : Module.Dual ℝ E): ∑ i:U,∑ j:U, (Y) i j*((A (m i):ℂ)*(B (m j):ℂ)) = ((Γ.wick A B):ℝ) := by
  let g(i j:U):ℝ:= Γ.wick (m.coord i) (m.coord j); let x:= Γ.inverse A
  have he (v:E)(P:Module.Dual ℝ E): ∑ j:U,(m.coord j v)*P (m j)= P v:= by
       simp_rw [show ∀ j:U,(m.coord j v)*P (m j)=P (m.coord j v • m j) from fun j=> Eq.symm (map_smul ..),← map_sum,show ∑ j:U,m.coord j v • m j=v from m.sum_repr v]
  have hx:A=∑ i:U,A (m i) • m.coord i := LinearMap.ext (fun v=> by rw [LinearMap.sum_apply]; simp only [LinearMap.smul_apply,smul_eq_mul]; nth_rw 1 [← he v A]; exact Finset.sum_congr rfl (fun i _=>mul_comm ..))
  suffices hv : ∑ i:U, ∑ j:U,g i j * (A (m i)*B (m j)) = Γ.wick A B by dsimp only; exact_mod_cast hv
  unfold g Law.wick
  conv_rhs => rw [hx,map_sum,map_sum]
  simp_rw [map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro i _; simp_rw [mul_left_comm _ (A _), ← Finset.mul_sum, he]

omit [Fintype U] [Fintype J] in
private lemma wick_sym : Cog.Sym φ μB:= rule (Y) (fun i j=> by
    have hp:=Γ.turns (Γ.inverse (m.coord i)) (Γ.inverse (m.coord j)); simp_rw [Law.applies] at hp
    exact congr_arg Complex.ofReal hp.symm)

omit [Fintype J] in
private lemma layer_ℓ (ℓ: Module.Dual ℝ E): INK ℓ = ∑ j:U, (ℓ (m j):ℂ) • atLetter (Sum.inl j) := by
    apply ext_D; rw [ drip ]; simp [Finset.sum_apply, atLetter];
    rintro (x|v)
    · rw [map_sum]; simp_rw [map_smul]; rw [ sum_eq_single x ]; rotate_left
      · intro i _ he; rw [unheard (Sum.inl i) (by exact fun h=> he (Sum.inl.inj h).symm),smul_zero]
      · simp
      rw [frameLinear,hear]; ext1 l; cases l <;> simp [coin]
    rw [ ink_off (maintain m) (mark m (Sum.inr v) rfl) _,map_sum]; symm; exact Finset.sum_eq_zero fun i _=> by rw [map_smul, unread v i, smul_zero]
where unread (v:J ⊕ J)(x:U): D (Sum.inr v) (atLetter (Sum.inl x) (R:=ℂ))=0:= unheard (Sum.inl x) (by simp)
variable (a:A) (ℓ:A→ Module.Dual ℝ E)
omit [FiniteDimensional ℝ E] in
private lemma minted_ℓ (s:Finset A): Law.product ℓ s ∈ papers E:= by
    rw [show Law.product ℓ s=∏ i∈s,(ℓ i : E→ℝ) from funext (fun x=> (Finset.prod_apply ..).symm)]; exact (papers _).prod_mem fun i _=> Papers.linear _

omit [Fintype U] [Fintype J] in
private lemma margin_ℓ (s:Finset A)(x:Slot U J): D x (INK (Law.product ℓ s))= ∑ j∈s, (ℓ j (maintain m x):ℂ) • INK (Law.product ℓ (s.erase j)) := by
     rw [Taylor.inktip]; let Q j:E→ℝ:= ℓ j (maintain m x) • Law.product ℓ (s.erase j)
     have hq (v:E): Law.diffSum ℓ s (maintain m x) v=(∑ j∈s,Q j) v := by unfold Law.diffSum; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun j _=> mul_comm ..
     have he (v:E): layer (maintain m x) (Law.product ℓ s) v= Law.diffSum ℓ s (maintain m x) v:= by
          refine HasLineDerivAt.unique ((((paper_hot (minted (minted_ℓ ℓ s))).differentiable (by simp)) v).hasFDerivAt.hasLineDerivAt (maintain m x)) ?_
          letI := borel E; letI : BorelSpace E := ⟨rfl⟩; unfold HasLineDerivAt; simpa using Law.diffSum_on ℓ s (maintain m x) v 0
     rw [funext he, funext hq, Taylor.ink_sum _ _ (fun i _=> (paper_hot (minted ((papers E).smul_mem (minted_ℓ ℓ _) (ℓ i (maintain m x))))).contDiffAt)]
     exact Finset.sum_congr rfl fun j _=> Taylor.ink_smul _ (paper_hot (minted (minted_ℓ ℓ _))).contDiffAt _

private lemma recursionℓ (s:Finset A)(he:a∉s): View μB (INK (Law.product ℓ (insert a s)))= ∑ i∈s, (View μB (INK (Law.product ℓ (s.erase i)))) * (Γ.wick (ℓ a) (ℓ i):ℂ) := by
  -- letter contraction
  let K:=μB; let c (i:A) (x:U):ℂ:= (ℓ i (m x):ℝ); let F i:=INK (Law.product ℓ (s.erase i)); let H:= INK (Law.product ℓ s); have hx : H∈ FeeP φ:= rank_money _ _ (mark m) (minted (minted_ℓ ℓ s)); rcases fee_spec hx with ⟨hx, hv⟩
  have hh (x:U): View μB (product φ (atLetter (Sum.inl x)) H) = ∑ j:U,(Y) x j * ∑ i∈s, c i j * View K (F i) := by
      rw [ ibpV _ (PairCoords.order _) (wick_sym J m Γ) hx hv, Fintype.sum_sum_type ]; unfold H; simp_rw [ margin_ℓ J m ℓ s]
      simp only [map_sum,map_smul, smul_eq_mul, maintain, Sum.elim_inl, Sum.elim_inr,map_zero,Complex.ofReal_zero,zero_mul,mul_zero,Finset.sum_const_zero, add_zero, cost_even]
      rfl
  have h' : Law.product ℓ (insert a s)= (ℓ a) * Law.product ℓ s:= by funext x; simp [Law.product,he]
  rw [ h', Taylor.ink_mul _ (mark m) (paper_hot (minted (Papers.linear (ℓ a)))|>.contDiffAt) (paper_hot (minted (minted_ℓ ℓ s))|>.contDiffAt), layer_ℓ J m (ℓ a), map_sum, LinearMap.sum_apply,map_sum]; change ∑ x:U, View μB (product φ (c a x • atLetter (Sum.inl x)) H)= _; simp_rw [map_smul,LinearMap.smul_apply,map_smul,hh,smul_eq_mul,Finset.mul_sum]
  calc
    _ = ∑ i∈s, ∑ j:U, ∑ p:U, c a j * ((Y) j p * (c i p* View K (F i))) := by
        conv_rhs => rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _=> Finset.sum_comm
    _ = _:= by apply Finset.sum_congr rfl; intro i _; rw [← basis_law m Γ,Finset.mul_sum]; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl fun j _=> (?_); apply Finset.sum_congr rfl; intro k _; unfold K c F; ring

section
variable [MeasurableSpace E][BorelSpace E] (μ: Measure E)[IsAddHaarMeasure μ]
lemma letter_price (s:Finset A): View μB (INK (Law.product ℓ s))= Complex.ofReal (Γ.average μ (Law.product ℓ s)) := by
    induction s using Finset.strongInduction with| H s ih=>
     rcases Finset.eq_empty_or_nonempty s with rfl|⟨a,ha⟩
     · rw [show Law.product ℓ ∅=1 from (by funext x; simp [Law.product]), minView' μB, Law.empty Γ μ, Complex.ofReal_one]
     let t:=s.erase a; have ht : a∉t:=Finset.notMem_erase a s; have hx: insert a t = s:= Finset.insert_erase ha
     calc
       _ = ∑ i∈t, ( View μB (INK (Law.product ℓ (t.erase i)))) * (Γ.wick (ℓ a) (ℓ i):ℂ) := by nth_rw 1 [←hx]; exact recursionℓ J m Γ a ℓ t ht
       _ = Complex.ofReal (Γ.average μ (fun x=> Law.product ℓ t x *ℓ a x)):= by rw [Law.recursion,Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _=> by rw [Complex.ofReal_mul, ih (t.erase i) (lt_of_le_of_lt (Finset.erase_subset _ _) (hx ▸ ssubset_insert ht))]
       _ = _:= by have he: Law.product ℓ s=fun x=> Law.product ℓ t x *ℓ a x:= by nth_rw 1 [← hx]; funext x; simp [Law.product,ht,mul_comm]
                  rw [he]
where minView' (B:Grain (Slot U J)) : View B (INK (1:E→ℝ))=1:= by rw [ (show INK (1:E→ℝ)=_ from Taylor.ink_const (maintain m) (1:ℝ)), minView,Complex.ofReal_one ]

end
-- from monoid closure description. Keep using Normed real polynomial lamps.
omit [FiniteDimensional ℝ E] in
private lemma listP (x:E→ℝ)(h: x∈ Submonoid.closure (Set.range fun a:Module.Dual ℝ E=> (a : E→ℝ))): ∃ l: List (Module.Dual ℝ E), x = (l.map (fun ℓ:Module.Dual ℝ E=> (ℓ:E→ℝ))).prod := by
   induction h using Submonoid.closure_induction with| one=> exact ⟨ [],rfl ⟩| mem x hx=> rcases hx with ⟨ℓ,rfl⟩; exact ⟨ [ℓ], by simp ⟩| mul x y hx hy h k=> rcases h with ⟨l,rfl⟩; rcases k with ⟨t,rfl⟩; exact ⟨ l ++ t,by simp ⟩
omit [FiniteDimensional ℝ E] in
private lemma degP (l:List (Module.Dual ℝ E)): (l.map (fun ℓ:Module.Dual ℝ E=> (ℓ:E→ℝ))).prod= Law.product l.get Finset.univ:= by
   nth_rw 1 [← List.ofFn_get l]; rw [List.map_ofFn, List.prod_ofFn]; funext x; rw [Finset.prod_apply]; rfl

variable [MeasurableSpace E][BorelSpace E] (μ: Measure E)[IsAddHaarMeasure μ]
theorem salary (x:Permit E): View μB (INK x.val)=Complex.ofReal (Papers.opening μ Γ x) := by
  let V:=Submodule.span ℝ ((Submonoid.closure (Set.range fun a:Module.Dual ℝ E=> (a : E→ℝ))) : Set (E→ℝ)); have he : (papers E).toSubmodule=V:=Algebra.adjoin_eq_span ..; have hi(y:E→ℝ)(hp:y∈V): y∈papers E:= show y∈(papers E).toSubmodule from he.symm ▸ hp
  suffices hx: ∀ y:E→ℝ,(h:y∈V)→ View μB (INK y)=Complex.ofReal (Papers.opening μ Γ (minted (hi y h))) by exact hx x.val (he ▸ x.property)
  intro y h; induction h using Submodule.span_induction with
  | mem y hy=> rcases listP y hy with ⟨l,hx⟩; change View μB (INK y)=((Γ.average μ y):ℂ); rw [hx,degP]; exact letter_price J m Γ l.get μ _
  | zero=> change _=Complex.ofReal (Papers.opening μ Γ 0); rw [map_zero, ink_zero,map_zero, Complex.ofReal_zero]
  | add y z hy hz h k=> change View μB (INK (y+z))=Complex.ofReal (Papers.opening μ Γ (minted (hi y hy)+minted (hi z hz))); rw [map_add, Taylor.ink_add _ (paper_hot (minted (hi y hy))|>.contDiffAt) (paper_hot (minted (hi z hz))|>.contDiffAt),Complex.ofReal_add,map_add,h,k]
  | smul r y hy h=> change View μB (INK (r•y))=Complex.ofReal (Papers.opening μ Γ (r • minted (hi y hy))); rw [map_smul,Taylor.ink_smul _ (paper_hot (minted (hi y hy))|>.contDiffAt), smul_eq_mul, Complex.ofReal_mul, map_smul, h ]; rfl

theorem sharp_pay (F:PowerSeries (Permit E))(i:ℕ): ℶV μB (track φ (sharp (maintain m) φ (mark m) F)) i=Complex.ofReal (coeff i (Splice.input Γ μ F)):= by change View _ (track _ _ i) = _; rw [sharp_coe,Splice.input,Splice.throughPrice]; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_mk]; exact salary J m Γ μ _
end YM.FVA2.Boson
