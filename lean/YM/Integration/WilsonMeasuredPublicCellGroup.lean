import YM.OPE.Cards.Literal

/-! Reflected products in one macrocell with independently dated original tickets at the fine sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicCellGroup
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word Push Next.Phase OPE.Cards
open Push.RelayDifference
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] {G : Gauge} {S : Schedule}
    {N p : ℕ} {n : Side} {β : ℝ}
local notation "R" => S.side N p
variable {W W₀ : Tiling (S.side N p)}

private lemma copy_prod (i : W.Cell) (F : ι → Config G (S.side N p) → ℂ) (U : Config G (S.side N p)) :
    W.copy i (fun x=> ∏ i, F i x) U = ∏ j,W.copy i (F j) U := by
    by_cases h : W.hand i <;> simp [Tiling.copy,h,star_prod]
-- can't use `PaidAt.live` when empty group, ask antecedent

/-- One true Wilson measure hears every reflected copy. Each slot keeps its own booked scale. -/
theorem exterior {k:ι→ℕ} (hw:W₀.kind=.link) (he:W.kind=.link) (hx:W₀.base=W.base)
    (hW:W₀.side.val ∣ W.side.val) (u:ι→Site R) (F:ι → Config G R → ℂ) (A:ι→ℝ) (i:W.Cell)
    (h:∀j,PaidAt S N p (k j) β (A j) (F j))
    (ht:∀j,Cells.span S (h j).live p ∣ W₀.side.val)
    (hf:∀j,W.which (u j)=i) (hM:∀j,Inside W₀ (3*Cells.span S (h j).live p) (u j))
    (hS:∀ i j:ι,i≠j → W₀.side.val < separation (u i) (u j)) (hβ:Seam G R β) :
    ∃ Z:Config G R→ℂ,W.copy i Z=(fun V=>∏ j,(F j ∘ translate (u j)) V) ∧
      Interior (W.chamber 0) Z ∧ W.rootTest β Z ≤ ∏ j,A j := by
    let M (j:ι) := 3 * Cells.span S (h j).live p
    have hg (j:ι) : u j ∈ W.margin i (M j) := by
      rw [← hf j]
      exact shared_inside W W₀ hx hw he hW (M j) _ (hM j)
    choose v b s hv hu ht' hr hI hC using fun j:ι=> (h j).at_cell W false 1 rfl ((ht j).trans hW) (hg j) hβ
    let g j:= RelayDifference.oriented (F j) (b j) (s j) (v j); let Z U:=∏ j,g j U
    let z(x:W.Cell×ι):= W.copyMap x.1 (v x.2); let c (i:W.Cell×ι):= W₀.which (z i)
    have hy (x:W.Cell × ι): Inside W₀ (M x.2) (z x) :=
      (inside_reflected W W₀ hx hW he hw x.1 ..).mpr
        ((inside_reflected W W₀ hx hW he hw i ..).mp (hu x.2|>.symm ▸ hM x.2))
    have hG(x:W.Cell ×ι): W.which (z x)=x.1:= W.which_chamber (W.enumerate _ (show v x.2∈ W.chamber 0 from (hv _).1))
    have hJ: Injective c:= by
       rintro ⟨x,I⟩ ⟨y,J⟩ h; have he:= shared_cell W W₀ hx hW h; rw [hG,hG] at he; obtain rfl:x=y:=he
       congr 1; by_contra he
       have ht:=W₀.extent (hy (x,I)).1 (x := z (x,I)) (y:= z (x,J)) (show z (x,J)∈ W₀.chamber (c (x,I)) from h ▸ (hy (x,J)).1)
       have hh : separation (z (x,I)) (z (x,J))=separation (u I) (u J) := by dsimp only [z]; rw [separation_copy,← separation_copy W i,hu,hu]
       exact (hS I J he).not_ge (hh ▸ ht)
    have ha(x:W.Cell×ι):∃ G':Config G (S.side N p)→ℂ,W.copy x.1 (g x.2) = W₀.copy (c x) G' ∧ Interior (W₀.chamber 0) G' ∧ W₀.rootTest β G' ≤ A x.2:= by
       rcases x with ⟨i,j⟩; unfold g; rw [copied]
       obtain ⟨v,b,s,-,-,-,he,ht⟩:= (h j).at_cell W₀ ((decide (W.hand i)).xor (b j)) (W.omega i * s j) (diag_mul (show diag (W.omega i) from rfl) (ht' _)) (ht j) (hy (i,j)) hβ
       exact ⟨_,he.symm,ht⟩
    choose G' hH ha hb using ha; refine ⟨Z,funext (fun U=> ?_), Interior.combines _ _ (fun i _=>hI i),?_⟩
    · unfold Z; rw [copy_prod]; refine Finset.prod_congr rfl fun j _=>?_ ; unfold g; rw [hr,RelayDifference.oriented,pull_one]; rfl
    have hh : W.fullAt (fun _=> Z) = fun U=>∏ i : W.Cell × ι, W₀.copy (c i) (G' i) U:=by
       funext U; rw [Fintype.prod_prod_type]; unfold Tiling.fullAt Z; refine Finset.prod_congr rfl fun i _=>?_ ; rw [copy_prod]; exact Finset.prod_congr rfl fun j _=> congr_fun (hH (i,j)) U
    apply le_of_pow_le_pow_left₀ W.cells_positive.ne' (Finset.prod_nonneg (fun j _=>(h j).cost))
    rw [W.powering]; change ‖moment β (W.fullAt _)‖ ≤ _; rw [hh]; apply le_trans ((W₀.planted hβ _ hJ G' ha).trans (Finset.prod_le_prod (fun i _=> W₀.root_nonneg ..) (fun i _=> hb i)))
    rw [Fintype.prod_prod_type]; simp

end YM.Integration.WilsonMeasuredPublicCellGroup
