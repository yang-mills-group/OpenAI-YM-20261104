import YM.SignedWilsonExpansion.F9.Pier
/-!
# Input palette (rank leading) on pointStep.

This solves for scalars at the letter entry-level time. It's the genuine
scalar shelf. Never change the operant Wilson epoch at positive order of
these scalar adjustments. Prices at entry-level of *this* boundary solver
can be rebased later on quoting estimates. Contains numerical support and
basic estimate for recovering one entry rank of an occupied rack.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{h p k m c N u e i j l r q:ℕ}{F:Labels.Frame G h}{H:Hol G} {Q:SectionData F}
variable {x B M X Y z:ℝ}{c':ℝ} {U:Type*}{E W:Credit}{R:Realm G (q+1) E}

abbrev SourceP (F:Frame G h):= F.Index→Era G ℝ
abbrev TagN (F:Frame G h)(p:ℕ):= F.Index × Fin (p+1)
abbrev BankP (F:Frame G h)(p:ℕ):= TagN F p→ℝ
abbrev wr (F:Frame G h)(i:F.Index):= (F.grades i).2
abbrev paper (x:BankP F p)(e:ℕ)(v:e≤p)(i:TagIx F r):= x (i.val,⟨e,Nat.lt_succ_of_le v⟩)
def auxiliary (P:SourceP F)(i:TagN F p):= trim (PowerSeries.X^i.2.val) (P i.1)
def rack (F:Frame G h)(P: SourceP F)(x:BankP F p): Era G ℝ:= ∑ i, x i • auxiliary P i
structure Palette (F:Frame G h)(P:SourceP F)(k u p:ℕ)(C:ℝ) : Prop where
    field (i:F.Index): Auth k (P i)
    dark (i:F.Index)(r:ℕ): wr F i<r→ (P i).2 0 r=0
    fee (i:F.Index)(e r:ℕ): e≤p→Fruit 0 1 u ((P i).2 e r) C
    high (r:ℕ)(i j:TagIx F r) : wT F i≤ wT F j→ row F ((P j.val).2 0 r) i=if i=j then 1 else 0
variable {P:SourceP F}
lemma Palette.money (v:Palette F P k u p X)(z:X≤Y): Palette F P k u p Y:=⟨v.field,v.dark,fun i e r w=>(v.fee i e r w).more z,v.high⟩
lemma Palette.mix (f:Palette F P k u p X) (x:BankP F p): Auth k (rack F P x):= Auth.sum (fun i _=> Auth.μ (trim_auth _ (f.field i.1)) (x i))
abbrev plate (e:ℕ)(U:Era G ℝ):= trim (PowerSeries.X^e) U
lemma plated (h:i≤e)(U:Era G ℝ): (plate i U).2 e=U.2 (e-i):=by
    change affix (PowerSeries.X^i) _ e=_; rw [affix, Finset.sum_eq_single_of_mem (i,e-i)]; swap; · exact Finset.mem_antidiagonal.mpr (by omega)
    · rw [(thin i).1,one_smul]
    intro j hj p; rw [coeff_X_pow,if_neg,zero_smul]; have ht:=Finset.mem_antidiagonal.mp hj; intro v; apply p; ext <;> dsimp only <;> omega
lemma Palette.trimmed (v:Palette F P k u p X) (i:TagN F p)(r e:ℕ)(hp:e≤p): Fruit 0 1 u ((auxiliary P i).2 e r) X:=by
    by_cases h:i.2.val≤ e; · rw [show (auxiliary P i).2 e=_ from plated h _]; exact v.fee _ _ _ ((Nat.sub_le ..).trans hp)
    rw [show (auxiliary P i).2 e=0 from (thin i.2.val).zero (by omega) _]; exact Fruit.zero.more (v.fee i.1 0 r (Nat.zero_le _)).C

def part (F:Frame G h)(e v p:ℕ): Finset (TagN F p):= Finset.univ.filter (fun x=> lowerGrade x.2.val (wr F x.1) e v)
abbrev eyeTag (F:Frame G h)(e p:ℕ)(v:e≤p)(i:TagIx F r): TagN F p:= (i.val,⟨e,Nat.lt_succ_of_le v⟩)
def before (F:Frame G h)(P:SourceP F)(x:BankP F p)(e r:ℕ): Era G ℝ:= ∑ i∈ part F e r p, x i • auxiliary P i
def sliceP (F:Frame G h)(P:SourceP F)(x:BankP F p)(e r:ℕ)(he:e≤p): Era G ℝ:= ∑ i:TagIx F r, x (eyeTag F e p he i) • auxiliary P (eyeTag F e p he i)
lemma Palette.slim (v: Palette F P k u p X)(he:e≤p) (x:BankP F p):(rack F P x).2 e r=(before F P x e r).2 e r+(sliceP F P x e r he).2 e r:=by
    let s:=part F e r p; let I:=eyeTag (r:=r) F e p he; let T:= Finset.univ.image I; let V:=s∪T
    have hx(i:TagN F p)(p:i∉V): (auxiliary P i).2 e r=0:=by
       have hp : ¬ lowerGrade i.2.val (wr F i.1) e r:= by intro h; exact p (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
       unfold lowerGrade at hp; by_cases h: e< i.2.val
       · rw [auxiliary,(thin i.2.val).zero h]; rfl
       rw [auxiliary,show i.2.val=e by omega,(thin e).lance]; apply v.dark; by_contra! H; apply p; apply Finset.mem_union_right; apply Finset.mem_image.mpr; exact ⟨⟨i.1,by change wr F i.1=r; omega⟩,Finset.mem_univ _,Prod.ext rfl (Fin.ext (by change e= i.2.val; omega))⟩
    have hr: Disjoint s T:= Finset.disjoint_left.mpr (fun i hi ht=>by obtain ⟨k,-,rfl⟩:= Finset.mem_image.mp ht; have he:= (Finset.mem_filter.mp hi).2; unfold I eyeTag at he; dsimp only at he; unfold wr at he; rw [k.property] at he; unfold lowerGrade at he; omega)
    have hp: Injective I:= fun i j h=> Subtype.ext (congr_arg Prod.fst h)
    simp only [rack,before,sliceP,Prod.snd_sum,Prod.smul_snd,Finset.sum_apply,Pi.smul_apply]; rw [← Finset.sum_subset (Finset.subset_univ V),show V=s∪T from rfl, Finset.sum_union hr, show T=Finset.univ.image I from rfl, Finset.sum_image (fun x _ y _ h=> hp h)] -- V unfold
    intro i _ v; rw [hx i v,smul_zero]
lemma Palette.lacuna (v:Palette F P k u p X)(x:BankP F p): Auth k (before F P x e r):= Auth.sum fun i _=>(trim_auth _ (v.field i.1)).μ _
lemma Palette.slice (v:Palette F P k u p X)(he:e≤p)(x:BankP F p): Auth k (sliceP F P x e r he):= Auth.sum fun i _=>(trim_auth _ (v.field i.val)).μ _

abbrev typus (F:Frame G h)(P:SourceP F)(r): Matrix (TagIx F r) (TagIx F r) ℝ := Matrix.of fun i j=> row F ((P j.val).2 0 r) i
lemma Palette.licensed (v:Palette F P k u p X)(e:Ample h u r): Down (wT F) (typus F P r) (rowCost F u r * X):=
    ⟨fun i=>(le_of_eq ((v.high _ i i le_rfl).trans (if_pos rfl)).symm),fun i j=>row_bound F _ (v.fee _ _ _ (Nat.zero_le p)) e.floor i,fun i j h hh=> (v.high _ i j h).trans (if_neg hh)⟩
lemma Palette.price (v:Palette F P k u p X)(x:BankP F p)(he:e≤p)(i:TagIx F r): row F ((sliceP F P x e r he).2 e r) i=(typus F P r *ᵥ paper x e he) i:=by
    unfold sliceP auxiliary eyeTag; dsimp only; rw [row_summed _ _ (fun j _=>trim_auth (PowerSeries.X^e) (v.field j.val))]; simp_rw [(thin e).lance]; exact Finset.sum_congr rfl (fun i _=> mul_comm ..)

section gate
lemma Palette.charger (p:Palette F P k u q X)(x:BankP F q)(he:e≤q)(v:∀ i∈part F e r q,‖x i‖≤Y)(hp:0≤Y): Fruit 0 1 u ((before F P x e r).2 e r) ((Fintype.card (TagN F q):ℝ)*X*Y):=by
    unfold before; simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply]; let g:= p.fee 0 0 0 (Nat.zero_le _); have h:=g.C
    apply (Fruit.sum (S:= part F e r q) (fun i _=> (p.trimmed i r e he).μ (x i)) zero_le_one).more
    rw [mul_assoc]; refine (Finset.sum_le_sum (fun i hi=> le_trans (mul_le_mul_of_nonneg_right (v i hi) h) (show _≤X*Y from le_of_eq (mul_comm ..)))).trans ?_; rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) (mul_nonneg h hp)
lemma Palette.sliceFee (p:Palette F P k u q X)(x:BankP F q)(he:e≤q)(v:∀ i:TagIx F r,‖x (eyeTag F e q he i)‖≤Y): Fruit 0 1 u ((sliceP F P x e r he).2 e r) ((Fintype.card (TagIx F r):ℝ)*X*Y):=by
    simp only [sliceP,Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply]; let g:= p.fee 0 0 0 (Nat.zero_le _); have h:=g.C
    apply (Fruit.sum (S:= Finset.univ) (fun i _=> (p.trimmed (eyeTag F _ _ he i) r e he).μ (paper x e he i)) zero_le_one).more
    apply (Finset.sum_le_sum (s:=Finset.univ) (fun i _=> (mul_le_mul_of_nonneg_right (v i) h))).trans; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
end gate
end YM.WilsonCoeffUV.Mer.Xa
