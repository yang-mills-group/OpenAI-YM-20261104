import YM.XSpace.Strand
/-! # Disconnect all external contractions after bilocal probe matching -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial
open scoped Topology BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge}

def skim (G:Gauge)(U:Finset E4):= net G+outK G U
variable (U:Finset E4)
local notation "K" => skim G U
local notation "O" => outK G U

lemma nowhere {P:Web G}(hp:Kept U P)(q:Web G): milk O (q*P)=milk O q*P:= by
  obtain ⟨R,hR⟩:= exists_rename_eq_of_vars_subset_range P _ Subtype.val_injective (fun i (hi:i∈P.vars)=>show i ∈ Set.range (Subtype.val (p:=fun i=>i∈P.vars)) from ⟨⟨_,hi⟩,rfl⟩)
  suffices ∀ R:poly P.vars,milk O (q*rename (Subtype.val:_→WebKey G) R)=milk O q*rename Subtype.val R from hR ▸ this R
  intro R
  induction R using MvPolynomial.induction_on with
  | C a=> rw [rename_C,mul_comm,mul_comm (milk O q),drink]
  | add a b ha hb=> rw [map_add,mul_add,mul_add,map_add,ha,hb]
  | mul_X a i ha=>
    let f:=rename (R:=ℂ) (Subtype.val: ↥P.vars→WebKey G);rw [_root_.map_mul (MvPolynomial.rename _),rename_X]; rw [← mul_assoc,mul_comm _ (X _),feeds,ha]
    change X i.val*(milk O q * f a)+slit ((outK G U).cov i.val) _=_; rw [show (outK G U).cov i.val=0 from _root_.funext fun j=> if_neg (not_and_of_not_left _ (not_not.mpr (hp _ i.property))),slit_zero,add_zero, mul_comm (X i.val),mul_assoc]

lemma skim_subs (c:G.ColorIndex){P p:Web G}(hp: Silent U P)(h: Thread G U p): Normal.blend K 0 (p*P)=0:= by
  unfold skim; rw [blend_components, ← warms,nowhere U hp.1]; exact (milk_ext c (Finset.Subset.refl _) h).subs c P hp

lemma slit_kept (L:WebKey G→ℂ) {P:Web G}(hp:Kept U P): Kept U (slit L P):= by
  obtain ⟨R,hR⟩:= exists_rename_eq_of_vars_subset_range P _ Subtype.val_injective (fun i (hi:i∈P.vars)=>show i ∈ Set.range (Subtype.val (p:=fun i=>i∈P.vars)) from ⟨⟨_,hi⟩,rfl⟩)
  suffices ∀ R:poly P.vars, Kept U (slit L (rename (Subtype.val:_→WebKey G) R)) from hR ▸ this R
  intro R; let f:= (Subtype.val: ↥P.vars→WebKey G); rw [labelled, Normal.exchange_slit,← Normal.labelled f]; intro i hi; obtain ⟨j,hj,h⟩:= mem_vars_rename _ _ hi; exact h ▸ hp _ j.property -- inspect

lemma scrape_cut {P:Web G}(h:Kept U P)(x:E4)(p:Flavor 0)(i:G.ColorIndex): Sliq K x p i P=scrape x p i P:= by
  obtain ⟨R,hR⟩:= exists_rename_eq_of_vars_subset_range P _ Subtype.val_injective (fun i (hi:i∈P.vars)=>show i ∈ Set.range (Subtype.val (p:=fun i=>i∈P.vars)) from ⟨⟨_,hi⟩,rfl⟩)
  suffices ∀ R:poly P.vars,Sliq K x p i (rename Subtype.val R)= scrape x p i (rename Subtype.val R) from hR ▸ this R
  intro R
  induction R using MvPolynomial.induction_on with
  | C a=> simp
  | add a b ha hb=> rw [map_add,map_add,map_add,ha,hb]
  | mul_X a j ha=>
    rw [map_mul,rename_X]; unfold Sliq scrape; rw [mul_comm, Normal.slit_prod, Normal.slit_prod]; unfold Sliq scrape at ha; rw [ha]; congr 2
    apply congr_arg; unfold forge form limbs; simp only [map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; apply Finset.sum_congr rfl; intro c _
    unfold skim; congr 1; change (net G).cov _ _+(outK G U).cov _ _= _; rw [show (outK G U).cov _ _=0 from (if_neg (not_and_of_not_right _ (not_not.mpr (h j.val j.property))): (outK G U).cov (x,⟨0,c⟩) j.val=0),add_zero]
lemma scrape_forget {x y:E4}{k:ℕ}(p:Flavor 0)(q:Flavor k)(i j:G.ColorIndex)(hx:x∉U)(hy:y∉U): Sliq K x p i (factors y (flavor k j q))=0:= by
  unfold factors Maxwell.symbol Sliq; simp only [map_sum,C_mul',map_smul,post_X]; refine Finset.sum_eq_zero fun a _=>?_
  rw [(slit _).map_smul, slit_X, forge,limbs,map_sum,Finset.sum_apply]; rw [Finset.sum_eq_zero, map_zero,smul_zero]; intro v _
  rw [Finsupp.linearCombination_single]; simp only [Pi.smul_apply];
  suffices he: (skim G U).cov (x,⟨0,v⟩) (y,⟨k,a⟩)=0 by rw [he,smul_zero]
  change (net G).cov _ _+(outK G U).cov _ _=_; simp [outK,hx,hy]

lemma orth_ext {B:Finset E4}{x:E4}(u:Flavor 0)(i:G.ColorIndex)(p:Web G)(hx:x∉U)(h:U⊆ B)(hp:Thread G B p): Sliq K x u i p=0:= by
  induction hp with
  | one=>simp
  | add H H' ih hh=> rw [map_add,ih h,hh h,zero_add]
  | scale H t ih=> rw [(Sliq K _ _ _).map_smul,ih h,smul_zero]
  | @join B p y z v w he hy hz hP ih=>
    rw [(Sliq K x u i).leibniz,ih (h.trans (fun x hx=> Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))),smul_zero,zero_add,signFor,map_sum]; rw [Finset.sum_eq_zero,smul_zero]; intro j _
    rw [(Sliq K x u i).leibniz]; unfold singleF; rw [scrape_forget _ u w _ j hx (Finset.notMem_mono h hz), scrape_forget _ u v _ j hx (Finset.notMem_mono h hy)]; simp

lemma skim_interior {P:Web G}(h:Kept U P): Normal.blend K 0 P=WW G P:= by
  unfold skim; rw [blend_components,← warms]; rw [show milk O P=P from (by simpa using nowhere U h 1)]; rfl

-- only the source currents remain
lemma insulate (Q:Normal.Symmetric (WebKey G))(x:E4)(p:Flavor 0)(i:G.ColorIndex)(T:Web G): Normal.blend Q 0 (singleF x p i*T)=Normal.blend Q 0 (Sliq Q x p i T):= by unfold singleF; rw [blend_components, strokes,Normal.refresh]; simp only [map_add,map_mul]; rw [show aeval (0:WebKey G→ℂ) (glyph (limbs x (flavor 0 i p)))=0 by simp [limbs],zero_mul,zero_add, Normal.skims];rfl
lemma remote (x y:E4)(p q:Flavor 0)(h₁:x∉U)(h₂:y∉U){F P:Web G}(hF:Thread G (insert x (insert y U)) F)(hP:Kept U P):
    Normal.blend K 0 (signFor x y p q G * F *P)=∑ i:G.ColorIndex, Normal.blend K 0 (F*scrape y q i (scrape x p i P)):= by
  have ht:U⊆ insert x (insert y U):= fun z hz=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
  rw [mul_assoc, signFor,Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro i _
  let f:= singleF x p i; let g:= singleF y q i; let B:= P
  change Normal.blend K 0 ((f*g)*(F*P))=_
  rw [mul_assoc, show f= _ from rfl,insulate]
  let D₁:= Sliq K x p i; let D₂:= Sliq K y q i
  have he : D₁ (g*(F*P)) = g*(F*scrape x p i P):= by rw [D₁.leibniz,D₁.leibniz,orth_ext _ p i _ h₁ ht hF,show D₁ g=0 from scrape_forget _ p q i i h₁ h₂, scrape_cut _ hP]; simp [smul_eq_mul]
  have hh:Kept U (scrape x p i P):= slit_kept U _ hP
  change Normal.blend K 0 (D₁ _)= _; rw [he]; unfold g; rw [insulate,(Sliq K y q i).leibniz, orth_ext _ q i _ h₂ ht hF,scrape_cut _ hh];simp
end YM.XSpace.Stab
