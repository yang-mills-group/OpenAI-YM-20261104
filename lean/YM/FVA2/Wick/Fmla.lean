import YM.FVA2.Wick.Jacobi
/-! # Gaussian fermionic identities for the unscaled perturbation letters

All arithmetic at the rank and order given by the symbols. Does not use any spacing or estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Fermion
open Function Set Finset Filter
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open Gem
open Formal (overlay)
open scoped BigOperators Topology ContDiff Matrix
variable {A J E : Type} [FA:Fintype A] [DA:DecidableEq A] [FJ:Fintype J] [DJ:DecidableEq J]
local notation "L" => Index A J
local notation "p" => sector (A:=A) (J:=J)
local infixl:70 " ⋆ " => product p
local infixl:70 " ★ " => overlay p
local notation "R" => Formal.Table L
local notation "Λ" => promote (Wg A J)
local notation "G" => odd A J
local notation "β" => allIndex (Alone p) ℕ
local notation "ι" => Formal.tab
local notation "Φ" => Formal.tab (A:=L) (coin 1)

-- Stronger funding than Mini.
abbrev funded {A:Type} (d : Sector A) := Formal.OK d
omit FA FJ DA DJ in
lemma fund (F:R)(h : F∈funded p)(i:ℕ) : F i∈Mini L := (fee_spec (h i (mem_univ _))).2

omit FA DA FJ DJ in
lemma commute_left (t v:R)(he:v∈β) : v ★ t=t ★ v := Formal.central (Formal.ev.mpr fun i=> alone_pure (he i (Set.mem_univ _))) t

lemma frame_time (x y:R) (he : x∈β)(h:x∈funded p)(H:y∈funded p) : Λ (x ★ y) = x ★ Λ y := by
  funext i; simp only [Formal.coeff_prod,promised,map_sum]; apply Finset.sum_congr rfl; intro j _
  exact Wg_factors (he _ (Set.mem_univ _)) (fund x h _) (fund y H _)

omit FA DA FJ DJ in
lemma der_alone (x : R)(i:L)(hi:p i=true)(h:x ∈ β) : Formal.der i x=0:= funext fun j=> alone_D (h j (Set.mem_univ _)) hi

variable (i j:J)
local notation "k" => (fun i:J=> ι (atLetter (ghost (A:=A) i) («R»:=ℂ)))
local notation "f" => (fun i:J=> ι (atLetter (bar (A:=A) i) («R»:=ℂ)))
local notation "∂" => Formal.der (ghost (A:=A) i)

section
omit FA DA FJ DJ
lemma bar_funded : f i∈funded p:= Formal.tab_good (S:=FeeP p) ⟨speaks_s _,minH (letterN _)⟩
lemma ghost_funded : k i∈funded p:= Formal.tab_good (S:=FeeP p) ⟨speaks_s _, minH (letterN _)⟩
lemma bar_graded : Formal.band p true (f i):= Formal.tab_band (h:=speaks_p (bar i))
lemma ghost_graded : Formal.band p true (k i):= Formal.tab_band (h:=speaks_p (ghost i))
lemma f_as (F:Raw L ℂ) : ι F ★ Φ=ι F := (PermV p).identityR _
lemma d_bar : ∂ (f j)=0:= by unfold Formal.der; rw [Formal.promote_tab, unheard (bar (A:=A) j) (by simp [bar,ghost]), map_zero]
include DJ in
lemma d_ghost : ∂ (k j)= if i=j then Φ else 0 := by
  rw [Formal.der,Formal.promote_tab]; split
  next h=> rw [h, hear]
  next h=> rw [unheard _ (by simpa [ghost] using h), map_zero]
lemma bar_comm : k i ★ f j = -(f j ★ k i):= by rw [Formal.turns (ghost_graded i) (bar_graded j), cross_true, neg_one_smul]
end
lemma trace_bar (F : R)(h:F∈funded p) : Λ (f i ★ F)= Λ (∂ F) := by
  funext u; obtain ⟨h1,h2⟩:=fee_spec (h u (Set.mem_univ _))
  rw [promised, promised, Formal.tab_product, Wg_odd_D (bar i) rfl h1 h2];
  simp [Fintype.sum_sum_type, odd_c, antiBlock,bar, omega, Matrix.one_apply, ite_smul]; rfl

variable (e : A→E) [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "T" => Gem.letter (eased (J:=J) e)
variable (M:E→Matrix J J ℝ)
omit FA DA

def matrixGem (e : A→E) (M:E→Matrix J J ℝ) (i j:J): R := Gem.letter (eased (J:=J) e) (atM M i j) -- section
abbrev minus (i j:J) := (atM M i j)-(fun _=> (1:Matrix J J ℝ) i j)
def exponent (e:A→E) (M:E→Matrix J J ℝ) : R := ∑ i:J,∑ j:J, overlay (sector (A:=A) (J:=J)) (ι (xy i j)) (Gem.letter (eased (J:=J) e) (minus M i j))
variable (hp:M 0=1) (hm: ∀ i j : J, germ (atM M i j))
local notation "c" => exponent e M
local notation "Z" => exp0 p c
local notation "LQ" => Λ Z
include hm
omit FJ in
lemma minus_germ : germ (minus M i j):= (hm i j).sub contDiffAt_const
include hp
omit hm in
lemma exp_first : c 0=0 := by
  unfold exponent; simp_rw [Finset.sum_apply, Formal.coeff_zero, Gem.first, minus, Pi.sub_apply, atM, hp, sub_self, Complex.ofReal_zero, ← (coin_pure _).central]; simp [coin_product]

omit hp
lemma valid : c ∈ funded p := by
  have h i j : xy (A:=A) i j ∈ FeeP p := ⟨xy_s _ _, rankM (xy_deg _ _)⟩
  exact (funded p).sum_mem fun i _=> (funded p).sum_mem fun j _=> Formal.overlay_ok (Formal.tab_good (h i j)) (Gem.good _ (minus_germ i j M hm) (eased_p e))
omit hm in
lemma even : c∈Formal.even p := by
  have h i j : ι (xy (A:=A) i j) ∈ Formal.even p:= Formal.ev.mpr (Formal.tab_band (xy_p _ _))
  exact (Formal.even p).sum_mem fun i _ => (Formal.even p).sum_mem fun j _ => (PermV p).close _ (h i j) _ (Gem.even _ (eased_p e) _)

omit FJ hm in
lemma minus_alone : T (minus M i j) ∈ β := fun _ _ => alone_mask (alone_Inks _ _) _
omit FJ in
lemma Ti : T (minus M i j)∈funded p:= Gem.good _ (minus_germ i j M hm) (eased_p e)
omit FJ DJ hm in
lemma tab_pair (x y:J)(t:R) : Formal.tab (xy x y) ★ t=f x ★ (k y ★ t):= by rw [← Formal.assoc, Formal.tabs]; rfl
omit FJ in
lemma minus_eq (i j:J) : T (minus M i j) = T (atM M i j) - if i=j then Φ else 0:= by
  rw [show T (minus M i j)=_ from Gem.sub _ (hm i j) (g:=fun _=>(1:Matrix J J ℝ) i j) contDiffAt_const]; simp_rw [ Matrix.one_apply ]; split_ifs; · rw [Gem.entire,Complex.ofReal_one]
  congr 1; exact Gem.zero _

omit hm in
lemma exp_input_D : ∂ c = -∑ j, f j ★ T (minus M j i) := by
  have ht a h : ∂ (ι (Wick.xy a h) ★ (T (minus M a h))) = if i=h then - ( f a ★ T (minus M a i)) else 0:= by
    rw [tab_pair, Formal.der_product (bar_graded a), d_bar,
      Formal.der_product (ghost_graded h), der_alone _ (ghost i) rfl (minus_alone a h e M), d_ghost ]
    split; next he=> rw [he]; simp [Formal.tab_left,sector,ghost,cross_true]
    next h=> simp
  unfold exponent; simp_rw [map_sum,ht]; simp
end YM.FVA2.Wick.Fermion
