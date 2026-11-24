import YM.FVA1.Film

/-!
All-test sums. Away from unit tests we can allow worse radii. Do **not**
use this operation in claiming a weighted estimate with the inside supremum;
that estimate is already established on the common `Pays` witnesses for unit tests.
-/

noncomputable section
set_option autoImplicit false
namespace YM.FVA1
open MeasureTheory Finset Function Filter Lattice Wilson RG
open Marker Overlay Overlay.GapsLocal Push.GridApprox.Nil MergeProof Accent
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V J T X:Type}[DecidableEq V][AddCommGroup T][Module ℂ T][AddCommGroup X][Module ℂ X]
section pure
lemma SlotLinear.shift (c:ℂ)(s:Finset V)(g:(V→T)→X)(h:SlotLinear s g)(x:V→T):
    g (c • x) = (c^s.card) • g x := by
    let y(t:Finset V)(i:V) := if i∈t then c • x i else x i
    suffices H :∀ (t:Finset V),(t⊆s)→ g (y t)=c^t.card • g x by
      exact (h.reads _ (y s) (fun i hi=>by simp [y,(show i∈s from hi)])).trans (H _ (Subset.refl _))
    intro t hs; induction t using Finset.induction_on with
    | empty => simp [y]
    | insert i t hi ih =>
      have ht:t⊆s:=(subset_insert ..).trans hs
      have he:i∈s:= hs (mem_insert_self ..)
      have hv:y (insert i t) = update (y t) i (c • x i):=by
        ext j; by_cases hh:j=i; subst j; simp [y]
        simp [hh,y]
      rw [hv,h.hom i he,show (update (y t) i (x i))=y t from ?_,ih ht,Finset.card_insert_of_notMem hi,pow_succ',mul_smul]
      ext j; by_cases hh:j=i; subst j; simp [y,hi]
      simp [hh]
end pure

namespace Film
variable [Fintype V] {C:Controls V T}{w w':V→ℝ}{Γ:Census V}
variable {G:Gauge}{n:Side}{P:RG.Rep G n}{D:Film J T Γ P}

-- Controls might not be downward closed; need different scalar per slot. use products
omit [Fintype V] in
lemma private_shift (c:V→ℂ)(s:Finset V)(g:(V→T)→X)(h:SlotLinear s g)(x:V→T):
    g (fun i=> c i • x i) = (∏ i∈s,c i) • g x := by
    let y(t:Finset V)(i:V) := if i∈t then c i • x i else x i
    suffices H :∀ (t:Finset V),(t⊆s)→ g (y t)=(∏ i∈t,c i) • g x by
      exact (h.reads _ (y s) (fun i hi=>by simp [y,(show i∈s from hi)])).trans (H _ (Subset.refl _))
    intro t hs; induction t using Finset.induction_on with
    | empty => simp [y]
    | insert i t hi ih =>
      have ht:t⊆s:=(subset_insert ..).trans hs
      have he:i∈s:= hs (mem_insert_self ..)
      have hv:y (insert i t) = update (y t) i (c i • x i):=by
        ext j; by_cases hh:j=i; subst j; simp [y]
        simp [hh,y]
      rw [hv,h.hom i he,show (update (y t) i (x i))=y t from ?_,ih ht,Finset.prod_insert hi, mul_smul]
      ext j; by_cases hh:j=i; subst j; simp [y,hi]
      simp [hh]

open Next.Foundations
omit [Fintype V] in
lemma adapts {t a b k κ :ℝ}[Countable J][Nonempty V] (h:D.Fit)(hp:D.Pays C w t a b k κ)(x:V→ T):
    ∃ v:V→ℝ,(surface P D.surround D.tape.origin (fun i=>D.header i x) (D.soft x) (D.gas x)).Radial v a b k κ:=by
    choose c y he hy using fun i=> C.absorb i (x i); let v i:= w i/(1+‖c i‖)
    have hv(i):0<v i:= div_pos (hp.basis i) (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _))
    let S:=surface (B:=Γ) P D.surround D.tape.origin
    let Zx:=S (fun i=>D.header i x) (D.soft x) (D.gas x); let Zy:=S (fun i=>D.header i (fun j=>y j)) (D.soft y) (D.gas y)
    have hY:=pay_surface h hp y hy
    change Zy.Radial w a b k κ at hY
    let d (z:Γ.Mode):= ∏ i∈z.val,c i
    have hz {X:Type}[AddCommGroup X][Module ℂ X](z:Γ.Mode)(g:(V→T)→X)(h:SlotLinear z.val g): g x=d z • g y:= by rw [show x=fun i=> c i • y i from funext he]; exact private_shift c z.val g h y
    have hK(z:Γ.Mode): Poly.toll v z*‖d z‖ ≤ Poly.toll w z:=by
      unfold Poly.toll d; rw [norm_prod,← prod_mul_distrib]; apply Finset.prod_le_prod (fun i _=> mul_nonneg (hv i).le (norm_nonneg _)) (fun i _=> ?_); unfold v; rw [div_mul_eq_mul_div,div_le_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _))]; exact mul_le_mul_of_nonneg_left (by linarith) (hp.basis i).le
    -- align at surface H/K and recover witnesses. unfold numbering labels incl pinned/univ presenter. surface helper lemmas (committedE,K) only when pinned; direct cases.
    obtain ⟨e,hF,hR⟩:=hY.bulk; obtain ⟨u,hQ,h'⟩:= hY.hits
    have h1(i):Zx.H i=d (Zy.rays i) • Zy.H i:=by
      -- unfold private send_p? generalize numbering; use definitional `change` after cases.
      unfold Zx Zy S Overlay.GapsLocal.surface
      dsimp only [comp_apply]
      generalize Extra.Iteration.numbering (concern J Γ) i=q
      cases q with
      | inl j=> exact (smul_zero _).symm
      | inr j=> change D.soft x j.1 j.2.val=d j.2.val • D.soft y j.1 j.2.val; funext U; exact hz _ _ (h.beam _ _ _)
    have h2(i j):Zx.entries i j=d (Zy.marks i j) • Zy.entries i j:=by
      unfold Zx Zy S Overlay.GapsLocal.surface
      dsimp only
      generalize Extra.Iteration.numbering (forceLabel Γ) j=q
      funext U
      cases q with
      | inl j=> change (0:ℂ)=(_ : ℂ) • (0:ℂ); simp
      | inr j=> exact hz _ _ (h.beamK _ _ _)
    refine ⟨v,hv,fun i=>?_,hp.marker,⟨fun i=> ‖d (Zy.rays i)‖ * e i,?_,?_⟩,⟨fun i=> ‖d (Zy.marks i.1 i.2)‖*u i,?_,?_⟩⟩
    · have hf:= hK (Γ.fire i); simp only [Poly.toll,d,Census.fire,prod_singleton] at hf
      change v i*‖D.header i x‖≤ a; rw [hz (Γ.fire i) (D.header i) (h.lead i),norm_smul]; simp only [d,Census.fire,prod_singleton,←mul_assoc]
      exact (mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans (hY.localU _)
    · intro i; refine ⟨mul_nonneg (norm_nonneg _) (hF i).1, fun j hj=> ?_⟩
      change P.p.supBounds _ _ (Zx.H i) _; rw [h1]; exact bound_smul _ ((hF i).2 _ hj)
    · intro i; refine budget_mono (hR i) (fun j=>?_) (fun j=>?_)
      · split; next=> apply mul_nonneg (Poly.worth hv _).le; unfold BudgetPoint.mass; have :=(hF j).1; positivity
        next=> exact le_rfl
      change (if _∈(Zy.rays j).val then _ else _)≤_; split
      next hh=> unfold BudgetPoint.mass; change Poly.toll v (Zy.rays j) *(_ *(‖d (Zy.rays j)‖* _)) ≤ _; calc
          _=(Poly.toll v (Zy.rays j)*‖d (Zy.rays j)‖)*(Real.exp _* e j):=by unfold Zy S surface; simp; ring
          _ ≤ _:= mul_le_mul_of_nonneg_right (hK _) (mul_nonneg (Real.exp_pos _).le (hF j).1)
      next _=>exact le_rfl
    · intro i j; refine ⟨mul_nonneg (norm_nonneg _) (hQ i j).1,fun U=>?_⟩; change ‖Zx.entries i j U‖≤_; rw [h2,Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left ((hQ i j).2 U) (norm_nonneg _)
    intro i; refine budget_mono (h' i) (fun j=>?_) (fun j=>?_)
    · split; next=> apply mul_nonneg (Poly.worth hv _).le; unfold BudgetPoint.mass; have :=(hQ j.1 j.2).1; positivity
      next=> exact le_rfl
    change (if _∈(Zy.marks j.1 j.2).val then _ else _)≤_; split
    next hh=> unfold BudgetPoint.mass; change Poly.toll v (Zy.marks j.1 j.2) *(_ *(‖d (Zy.marks j.1 j.2)‖* _)) ≤ _; calc
          _=(Poly.toll v (Zy.marks j.1 j.2)*‖d (Zy.marks j.1 j.2)‖)*(Real.exp _* u j):=by ring
          _ ≤ _:= mul_le_mul_of_nonneg_right (hK _) (mul_nonneg (Real.exp_pos _).le (hQ j.1 j.2).1)
    next _=>exact le_rfl

lemma evaluates_all {t a b k κ :ℝ}[Countable J][Nonempty V] (h:D.Fit)(hp:D.Pays C w t a b k κ)(x:V→ T): (surface P D.surround D.tape.origin (fun i=>D.header i x) (D.soft x) (D.gas x)).density=D.density x:=by
  -- reuse Film.evaluates_surface proof with entrywise weaker Radial via scaling.
  obtain ⟨v,hv⟩:= adapts h hp x
  funext U; unfold Bands.density density
  let hh(i:J)(z:Said Γ) (hh:¬ pinned D.tape.origin (D.surround i) z) : D.soft x i z.val=0:=by
    by_contra H; exact hh (fun j hj=> h.inside x i z.val j hj H (D.tape.mem _))
  rw [atAll P _ _ _ _ _ hh v a b k κ _ (fit_surface h x) hv]
  congr 2
  · unfold extra Mach; apply congrArg Poly.pass; apply congrArg (_+·); refine tsum_congr fun i=> ?_
    let f j:=Poly.send j (masked P.p.threshold (D.surround i) (D.soft x i j) U)
    let L:=univ.filter (fun z:Γ.Mode=> z.val.Nonempty); let ψ:=D.glass x i U
    change (∑ j:Said Γ,f j.val)=ψ
    rw [← Finset.sum_subtype L (by simp [L]) f, Finset.sum_subset (f:=f) (Finset.subset_univ L) ?_]; · exact Poly.studs ψ
    intro j _ hj; have hz:j=Γ.quiet:=Subtype.ext (not_nonempty_iff_eq_empty.mp (fun H=>hj (by simp [L,H])))
    rw [hz]; unfold f; rw [h.mute x i]; simp [masked]
  unfold Bands.cluster
  refine tsum_congr fun i=>?_ ; unfold Bands.packet packet; split
  · exact prod_congr rfl fun j _=>everyK P _ _ _ _ _ (h.native x) U j
  rfl

lemma quiet {t a b k κ δ w' :ℝ}[Countable J][Nonempty V] (h:D.Fit)(hp:D.Pays C w t a b k κ)(H:P.activities.Valid P.p δ w')(x:V→T)(U:Config G n): (D.density x U).part Γ.quiet=(P.eval U:ℂ):=by
  rw [← evaluates_all h hp x]
  obtain ⟨v,hv⟩:=adapts h hp x
  exact Overlay.Bands.same _ (fit_surface h x) hv H U
end Film
end YM.FVA1
