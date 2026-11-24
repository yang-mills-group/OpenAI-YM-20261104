import YM.Comparison.Density.Transport.Left
/-!
# Transport of the translation-aggregated ordinary-potential jet

The hypothesis is available on the true, possibly very large torus only.
This is the translation-summed comparison (not testing a different RG
step on the small reflected period). Hold one leg fixed physically; no
partial-Fourier norm convention. Keeping one leg avoids charging a hidden
factor for the volume. Output any small-period torus with its explicit
finite-cell cost. The stencil footprint below is for SHORT comparison
entries after orienting; requires full supports, no staggering at the
seam. Afterward test nonlinear actual fields in Mirrors, not just flat jets.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Transport
open Function Lattice RG Wilson MeasureTheory Filter WardBin.Lies Finset
open AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n b : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fullLink (r : Side) : Finset (Edge Cover) :=
    ((Lattice.box r.val) ×ˢ (univ:Finset Axis)).filter fun e=> e.1+step e.2∈ Lattice.box r.val
abbrev Handles (r : Side) := ↥(fullLink r)
abbrev Arms (r : Side) (G : Gauge) := Handles r→ G.Color

lemma full_both (r : Side) (e : Edge Cover) :
    e∈fullLink r ↔ e.1∈Lattice.box r.val ∧ e.1+step e.2∈Lattice.box r.val := by simp [fullLink]

def dials (r : Side) (o : Site n) : Directions G n →L[ℝ] Arms r G := ContinuousLinearMap.pi fun e=>
    ContinuousLinearMap.proj (wrap n e.val.1+o,e.val.2)

lemma dials_norm (r : Side) (o : Site n) : ‖dials (G:=G) r o‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm x _
lemma dials_le (r : Side) (o : Site n) (x : Directions G n) : ‖dials r o x‖ ≤ ‖x‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm x _

def attachLinks (r : Side) (x : Handles r→ G.El) : Links ℤ G.El := fun i=>
    if h:i∈fullLink r then x ⟨i,h⟩ else 1

def chart (r : Side) (f : Links ℤ G.El→E) (x : Arms r G) : E := f (attachLinks r (fun e=> G.lieExp (x e)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma chart_exact {f : Links ℤ G.El→ E} (r : Side) (h : LocalOn (Lattice.box r.val) f) (A : Directions G n) (o : Site n) :
    f (expandAt o (increment 1 A))=chart r f (dials r o A) := by
  apply h; intro e h₁ h₂; unfold attachLinks
  rw [dif_pos ((full_both r e).mpr ⟨h₁,h₂⟩)]
  simp only [expandAt,increment,Pi.one_apply,mul_one]; rfl

variable (f : Links ℤ G.El → E)

def total (n : Side) (U : Config G n) : E:= ∑ x : Site n,f (expandAt x U)
def read (n : Side) := total f n ∘ increment 1

omit [NormedSpace ℝ E] in
lemma read_as (r : Side) (h : LocalOn (Lattice.box r.val) f) (n : Side) :
    read f n=∑ x : Site n, (chart r f ∘ dials r x) := by funext A; simp [read,total,chart_exact r h,Finset.sum_apply]

lemma one_entry (n r : Side) (x : Site n) (h : LocalOn (Lattice.box r.val) f) {d t : ℝ}
    {m : ℕ} {A : Directions G n} (ht : ‖A‖ ≤ t) (hp : ∀ y : Arms r G, ‖y‖≤ t → Through m (chart r f) y d) :
    Through m (fun z=> f (expandAt x (increment 1 z))) A d := by
  simp_rw [chart_exact r h]; exact through_pull (dials r x) (dials_norm ..) (hp _ ((dials_le ..).trans ht))

lemma total_entry (n r : Side) (h : LocalOn (Lattice.box r.val) f) {d t : ℝ}
    {m : ℕ} {A : Directions G n} (ht : ‖A‖ ≤ t) (hp : ∀ y : Arms r G, ‖y‖ ≤ t → Through m (chart r f) y d) :
    Through m (read f n) A ((Fintype.card (Site n):ℝ)*d) := by
  rw [read_as f r h]; simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using through_sum (univ:Finset (Site n)) (fun _=>d) _ m A
    (fun i _=> through_pull (dials r i) (dials_norm r i) (hp _ ((dials_le ..).trans ht)))

def held (z : Directions G n) (e : Edge (Site n)) := ∀ j,j≠e → z j=0

lemma lifts (x : Cover) (hx : x∈Lattice.box b.val) (hp : 2*b.val<n.val) : lift (wrap n x)=x := by
  refine lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩; obtain ⟨h,h'⟩:= box_test.mp hx; have hh:= h i; have hv:= h' i; omega

private lemma at_record {j : ℕ} {X : Fin j→Directions G n} {i : Fin j} {a : Edge (Site n)} (r : Side)
    (hP : LocalOn (Lattice.box r.val) f) (hK : ContDiffAt ℝ j (chart r f) 0)
    (h : held (X i) a) (hs : 2*r.val<n.val) :
    iteratedFDeriv ℝ j (read f n) 0 X =
        ∑ z∈Lattice.box r.val, iteratedFDeriv ℝ j (chart r f) 0 (fun i=> dials r (wrap n z+a.1) (X i)) := by
  let J (w : Site n) := iteratedFDeriv ℝ j (chart r f) 0 (fun i=>dials r w (X i))
  rw [read_as f r hP,iteratedFDeriv_sum_apply (fun w _=> ContDiffAt.comp (f:=dials (G:=G) r w) 0
    (g:=chart r f) (by rw [map_zero];exact hK) ((dials r w).contDiff.contDiffAt)),_root_.sum_apply]
  refine (sum_congr rfl (g:=J) (fun w _=>?_)).trans ?_
  · rw [liner (dials r w) (by rw [map_zero]; exact hK),map_zero]; rfl
  let c (x : Cover):= wrap n x + a.1
  have he : Set.InjOn c (Lattice.box r.val) := by
    intro x hx y hy hX
    have hk : wrap n x = wrap n y := add_right_cancel hX
    rw [← lifts x hx hs, hk, lifts y hy hs]
  let V := (Lattice.box r.val).image c
  have hv (x : Site n) (hx:x∉V): dials r x (X i)=0 := by
    funext s; obtain ⟨⟨b,e⟩, hb⟩:=s
    apply h; intro hz
    have hy: b∈Lattice.box r.val:= (full_both ..).1 hb|>.1
    have hl : wrap n b+x=a.1:= congr_arg Prod.fst hz
    apply hx; refine mem_image.mpr ⟨-b,?_,?_⟩
    · simp only [Lattice.box_test, Pi.neg_apply,neg_le_neg_iff] at *
      exact ⟨hy.2,fun i=> by simpa using neg_le_neg (hy.1 i)⟩
    unfold c; rw [map_neg,← hl]; abel
  calc ∑ w,J w =∑ w∈V,J w := by
                  refine (sum_subset (subset_univ _) fun i' _ hi=>?_).symm; unfold J
                  apply ContinuousMultilinearMap.map_coord_zero (i:=i)
                  exact hv _ hi
       _ = _ := sum_image he

/-- Last-leg anchoring in the interface can pick any slot. Parameter order
is ordinary Fréchet order, not ordered `leftDerivs`. Rank zero uses the
per-site scalar estimate. -/
def Ordinary (n : Side) (s : ℕ) (d : ℝ) :=
    (0<s → ∀ x : Site n, ‖f (expandAt x (1:Config G n))‖ ≤ d) ∧
      ∀ j<s, ∀ (X : Fin j→ Directions G n) (u : Edge (Site n)) (i : Fin j), held (X i) u →
        ‖iteratedFDeriv ℝ j (read f n) 0 X‖ ≤ d* ∏ i, ‖X i‖

private lemma box_add {v w : Cover} (r : Side) (hv : v∈ Lattice.box r.val) (hw : w∈ Lattice.box r.val) : v+w∈Lattice.box (2*r.val) := by
  obtain ⟨h,h'⟩ := box_test.mp hv; obtain ⟨g,g'⟩:=box_test.mp hw; apply box_test.mpr
  constructor <;> intro i <;> simp only [Pi.add_apply,Nat.cast_mul,Nat.cast_ofNat] <;> have hi:= h i <;> have hj:=h' i <;> have hk:=g i <;> have hl:=g' i <;> omega

lemma local_transport (r p n : Side) (hp : 4*r.val<p.val) (hn : 4*r.val<n.val)
    {s : ℕ} {d : ℝ} (hL : LocalOn (Lattice.box r.val) f) (hd : 0≤d) (hc : ContDiffAt ℝ s (chart r f) 0)
    (h : Ordinary f n s d) : Ordinary f p s d := by
  refine ⟨fun hs x=>?_,fun j hj X ⟨y,e⟩ i hu=>?_⟩
  · change ‖f 1‖ ≤ _
    exact h.1 hs 0
  let Y (a : Fin j) : Directions G n:= if a=i then Pi.single (0,e) (X i (y,e)) else
        fun c=> X a (wrap p (lift c.1)+y,c.2)
  have hy : held (Y i) (0,e):=fun q hq=> by simp [Y,hq]
  have he:= h.2 j hj Y (0,e) i hy
  have hx := hc.of_le (show (↑j:WithTop ℕ∞)≤(↑s:WithTop ℕ∞) by exact_mod_cast hj.le)
  rw [at_record f _ hL hx hu (by omega)]
  rw [at_record f _ hL hx hy (by omega)] at he
  let b : Side:= ⟨2*r.val, Nat.mul_pos (by decide) r.property⟩
  have hbk (n : Side) (hn:4*r.val<n.val) (x : Cover) (hx:x∈Lattice.box b.val) :
      ((wrap n x)=0) ↔ x=0 := by
    constructor
    · intro h
      rw [← lifts x hx (show 2*b.val<n.val by change 2*(2*r.val)<_; omega),h]
      funext i; exact ZMod.valMinAbs_zero ..
    rintro rfl; rw [map_zero]
  have hi (z) (hz:z∈Lattice.box r.val) (k : Fin j): dials r (wrap p z+y) (X k) = dials r (wrap n z+0) (Y k) := by
    funext l; obtain ⟨⟨v,c⟩,hl⟩:=l
    have hv:= box_add r ((full_both ..).mp hl|>.1) hz
    change X k (wrap p v+_,c) = Y k (wrap n v+_,c)
    simp_rw [←add_assoc,← map_add, add_zero]
    by_cases H:k=i
    · subst k; dsimp only [Y]; rw [if_pos rfl,Pi.single_apply]
      have he' : (wrap n (v+z),c)=((0:Site n),e) ↔ (wrap p (v+z)+y,c)=(y,e):= by
        simp only [Prod.mk.injEq,hbk _ hp _ hv,hbk _ hn _ hv, add_eq_right]
      split
      next h=> rw [he'.1 h]
      next h=> exact hu _ (mt he'.2 h)
    rw [show Y k = _ from if_neg (α:=Directions G n) H]; dsimp only []; rw [lifts _ (show _∈ Lattice.box b.val from hv) (show 2*b.val<n.val by change 2*(2*r.val)<_; omega)]
  apply le_trans ?_ (he.trans (mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=>norm_nonneg _) (fun k _=> show ‖Y k‖ ≤ ‖X k‖ from ?_)) hd))
  · apply le_of_eq; congr 1; apply sum_congr rfl; intro z hz; exact congr_arg _ (funext (hi _ hz))
  unfold Y; split
  next h=>subst k; rw [Pi.norm_single]; exact norm_le_pi_norm (X _) _
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun q=> norm_le_pi_norm (X _) _

lemma ordinary_norm {p : Side} {s : ℕ} {d : ℝ} (h : Ordinary f p s d) (hd : 0≤d) (j : ℕ) (hj : j<s) :
    ‖iteratedFDeriv ℝ j (read f p) 0‖ ≤ (Fintype.card (Edge (Site p)):ℝ)*d := by
  by_cases hz:j=0
  · subst j; rw [norm_iteratedFDeriv_zero]; unfold read; rw [Function.comp_apply,Work.G07.at_zero_increment]; unfold total
    refine (norm_sum_le ..).trans ((sum_le_sum fun w _=> h.1 hj w).trans ?_)
    rw [sum_const,nsmul_eq_mul,card_univ]; gcongr; simp [Edge,Axis]
  let i: Fin j := ⟨0,Nat.pos_of_ne_zero hz⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity); intro X
  let B (e : Edge (Site p)):Directions G p:= Pi.single e (X i e)
  let k(e) := Function.update X i (B e)
  let M:= (iteratedFDeriv ℝ j (read f p) 0)
  have he : ∑ e, B e=X i:= by ext e; simp [B, Finset.sum_apply]
  have ht : M X=∑ e,M (k e) := by
    have H:= M.toMultilinearMap.map_update_sum univ i B X; rw [he,update_eq_self] at H; exact H
  change ‖M X‖ ≤ _; rw [ht]
  have hb e : held (k e i) e := by intro j hj; simp [k,B,hj]
  have hK e k' : ‖k e k'‖ ≤ ‖X k'‖ := by
    by_cases h:k'=i
    · subst k'; rw [show k e i=B e from Function.update_self .., show ‖B e‖=‖X i e‖ from Pi.norm_single _]; exact norm_le_pi_norm ..
    simp [k,h]
  refine (norm_sum_le ..).trans ((sum_le_sum fun w _=> (h.2 j hj (k w) _ i (hb w)).trans
    (mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hK w j)) hd)).trans_eq ?_)
  simp [mul_assoc]
end YM.Comparison.Density.Transport
