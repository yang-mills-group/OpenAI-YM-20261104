import YM.RG02.Native.Composite
import YM.RG02.Native.Sparse

/-!
# Convenient weaker existential wrappers for quantitative stencils

No assertion constants are uniform except through period. Enough for
construction step algebra. Use full charged with specified schedule rates
when budgeting winding errors etc. `prices` meaningful: still true
exponential rate v. Also combination of derivative supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Native
open Function Filter Finset Lattice RG Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped BigOperators Classical Topology ContDiff
variable {α β γ Z:Type} [Fintype α][Fintype β] [NormedAddCommGroup Z][NormedSpace ℝ Z]
variable {K F : Stencil α β Z} {t r:ℕ}{n:Side}{a:ℝ}

-- explicit μ. origin separate. Through covers and native prices. -/
structure Supplies (t r:ℕ)(a:ℝ)(K:Stencil α β Z) : Prop where
    base_fair : fair t r K
    shares : through t r K
    pays : ∃ f:ℕ→ℝ,(∀ k≤r,0 ≤ f k) ∧ funded t r a K f
lemma Supplies.close {U:Stencil α β ℝ}{F:Stencil β γ Z}[Fintype γ] {b d:ℝ}(h: Supplies t r a U)(ht:Supplies t r b F)(he:origin t U)(hh:d≤a)(hp:d*r≤b)(ha:0≤d) : Supplies t r d (above U F):=by
    obtain ⟨P,hP,hU⟩:= ht.pays; obtain ⟨Q,hQ,hF⟩:=h.pays
    refine ⟨found h.base_fair ht.base_fair he, Native.through.above_works h.base_fair ht.base_fair he h.shares ht.shares,total P Q, fun k hk=> ?_, fun k hk=> Native.budget ha hk (le_trans ?_ hp) hh h.base_fair ht.base_fair he hU hF hQ⟩
    · exact sum_nonneg fun c _=> mul_nonneg (hP c.length (c.length_le.trans hk)) (prod_nonneg fun j _=> hQ _ ((c.partSize_le j).trans hk))
    gcongr
omit [Fintype β] in
lemma Supplies.mono (h:Supplies t r a K) {b:ℝ} (hb:b≤a) {k:ℕ}(hl:k≤r) : Supplies t k b K:=by
   obtain ⟨f,hf,hF⟩:= h.pays
   exact ⟨fun n hn i=> (h.base_fair n hn i).of_le (Nat.cast_le.mpr hl), fun i hi=> h.shares i (hi.trans hl), f, fun i hi=> hf i (hi.trans hl),fun i hi=> charged_mono (hF i (hi.trans hl)) hb le_rfl le_rfl⟩
omit [Fintype β] in
lemma Supplies.add (h:Supplies t r a K)(hp:Supplies t r a F): Supplies t r a (K+F):=by
   obtain ⟨Q,hQ,hX⟩:=h.pays; obtain ⟨P,hP,hZ⟩:=hp.pays
   have hx n (he:t≤(n:Side).val) k (hl:k≤r) i j : shaped (K+F) k n i j=shaped K k n i j+shaped F k n i j:=by
       have hm : ContDiffAt ℝ k (K n i) 0:= (h.base_fair n he i).of_le (Nat.cast_le.mpr hl)
       have hv : ContDiffAt ℝ k (F n i) 0:= (hp.base_fair n he i).of_le (Nat.cast_le.mpr hl)
       unfold shaped shape; simp only [Pi.add_apply, iteratedFDeriv_add_apply hm hv]; rfl
   refine ⟨fun n hn i=> ContDiffAt.add (h.base_fair n hn i) (hp.base_fair n hn i), ?_,Q+P, fun k hk=> add_nonneg (hQ k hk) (hP k hk),fun k hk n hn i=> ?_⟩
   · intro k hk n m l o i v ht; rw [hx n ht k hk, h.shares k hk n m l o i v ht,hp.shares k hk n m l o i v ht,← Finset.sum_add_distrib]; apply sum_congr rfl; intro v _; rw [hx _ (ht.trans (Nat.le_of_dvd m.pos l)) k hk]; split <;> simp
   apply le_trans _ (add_le_add (hX k hk n hn i) (hZ k hk n hn i)); unfold ticket; rw [← Finset.sum_add_distrib]; apply sum_le_sum; intro j _; unfold cost; rw [hx _ hn _ hk, ← mul_add]; apply mul_le_mul_of_nonneg_left (norm_add_le ..) (Real.exp_pos _).le
omit [Fintype β] in
lemma Supplies.scalar {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (h:Supplies t r a K) (L:Z →L[ℝ] E) : Supplies t r a (fun n i=> L ∘ K n i):= by
   let S:Stencil _ _ _:= fun n i=> L ∘ K n i
   obtain ⟨f,hF,h⟩:=h.pays
   have hu n (ht:t≤(n:Side).val) k (hk:k≤r) i x: shaped S k n i x=L (shaped K k n i x):=by
       unfold shaped shape S; rw [L.iteratedFDeriv_comp_left (‹Supplies ..›.base_fair n ht i) (Nat.cast_le.mpr hk)]; rfl
   change Supplies t r a S
   refine ⟨fun n ht i=> L.contDiff.contDiffAt.comp _ (‹Supplies ..›.base_fair n ht i), fun k hk n m l o i j ht=>?_,fun i=>‖L‖*f i, fun k hk=>mul_nonneg (norm_nonneg _) (hF k hk), fun k hk n hn i=>?_⟩
   · rw [hu _ ht _ hk, ‹Supplies ..›.shares k hk n m l o i j ht, map_sum]; apply sum_congr rfl; intro v _; split; rw [hu _ (ht.trans (Nat.le_of_dvd m.pos l)) _ hk]; exact map_zero _
   apply le_trans _ (mul_le_mul_of_nonneg_left (h k hk n hn i) (norm_nonneg L)); unfold ticket; rw [mul_sum]; apply sum_le_sum; intro j _; unfold cost; rw [hu _ hn _ hk,mul_left_comm ‖L‖]; exact mul_le_mul_of_nonneg_left (L.le_opNorm _) (Real.exp_pos _).le
variable [CompleteSpace Z]
lemma Supplies.of_short {d:ℕ}(h:localFields t d K)(hf:fair t r K)(hc: respects t K)(ha:0≤a) : Supplies t r a K:=by
    obtain ⟨w,hp,hQ⟩:= auto_paid K ha hf (Native.shares hc hf) h
    exact ⟨hf, Native.shares hc hf, w,fun k _=> hp k,hQ⟩

-- consumer palette external charges
end YM.RG02.Native
