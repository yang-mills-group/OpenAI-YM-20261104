import YM.MS.Swirl.Sits
import YM.MS.Book.Ell

/-!
# Keeping the physical insertions in the master identity

Exponentiate in the same coupling variable as the coefficientwise QME.
The antibracket here is odd (can't assume it takes values in the commutative
even subalgebra). Everything is formal and truncated coefficientwise, and
nothing is being assumed about analyticity in the parameters. -/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inserted
open Function Set Filter Finset
open MS MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program
open MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Swirl MS.Puff
open MS.Puff.SplitP MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom MS.Puff.Dynamics

variable {A I : Type} {p : Sector A}

abbrev EvenSeries (p : Sector A) (U : SpecB A) := U ∈ (PermV p).guard

local notation "R" => PermV p
local infixl:70 " ⋄ " => Actors.core (PermV p)

lemma even_coeff (f : SpecB A) : EvenSeries p f ↔ ∀ i, Pure p false (f i) :=
  universe0 (Center p)

lemma even_central {F : SpecB A} (hv : EvenSeries p F) (Z : SpecB A) :
    F ⋄ Z = Z ⋄ F := by
  funext n
  change (∑ i∈useN.pieces n, product p (F i.1) (Z i.2)) = ∑ i∈useN.pieces n,_
  rw [useN.also (fun i j=>product p (F i) (Z j))]; exact Finset.sum_congr rfl fun i _ =>
    ((even_coeff _).mp hv _).central _

private lemma even_middle {F : SpecB A} (hv : EvenSeries p F) (Z H : SpecB A) :
    F ⋄ (Z ⋄ H) = Z ⋄ (F ⋄ H) := by rw [← (R).star_a, even_central hv, (R).star_a]

lemma retrace_even {F : SpecB A} (hf : EvenSeries p F) : Pure p false (retrace F) := by
  intro l hl
  apply PowerSeries.ext; intro n
  rw [rback, (even_coeff _|>.mp hf n) l hl, map_zero]

variable [Fintype I] (B : Bonded p I)
local notation "BV" => B.BV
local infixl:85 " ♥ " => pairW (tokenL BV true p)
local notation "ε" => promote BV

lemma sym_even {F U : SpecB A} (hf : EvenSeries p F) (hu : EvenSeries p U) :
    F ♥ U = U ♥ F := by
  apply retrace.injective
  rw [← trips, ← trips]
  exact link_commute _ (retrace_even hf) (retrace_even hu)

lemma bracket_leibniz {F U : SpecB A} (hf : EvenSeries p F) (hu : EvenSeries p U)
    (V : SpecB A) : F ♥ (U ⋄ V) = (F ♥ U) ⋄ V + U ⋄ (F ♥ V) := by
  apply retrace.injective
  have HE : Actors.core (PermV p)=pairW (product p) := rfl
  rw [HE]
  rw [← trips, map_add, ← product_r, ← product_r, ← product_r, ← trips, ← trips]
  exact B.costs.paired (retrace_even hf) (retrace_even hu)

lemma delta_mul {F : SpecB A} (hf : EvenSeries p F) (V : SpecB A) :
    ε (F ⋄ V) = ε F ⋄ V + F ⋄ ε V + F ♥ V := by
  apply retrace.injective
  change retrace (ε (pairW (product p) _ V)) =
    retrace (pairW (product p) _ V + pairW (product p) F _ + _)
  simp_rw [map_add]
  rw [← trips, ← product_r, ← product_r, ← lap_r, ← product_r,
    ← lap_r, ← lap_r, link_even (b:=true) _ (retrace_even hf)]
  abel

lemma modulo_mul {X F : SpecB A} (hx : EvenSeries p X) (hf : EvenSeries p F)
    (V : SpecB A) : modulo B X (F ⋄ V)=
      modulo B X F ⋄ V + F ⋄ modulo B X V + F ♥ V := by
  unfold modulo; simp only [LinearMap.add_apply, map_add]
  rw [delta_mul B hf, bracket_leibniz B hx hf]; abel

lemma bracket_unit {F : SpecB A} (hf : EvenSeries p F) : F ♥ (R).unit = 0 := by
  let u := (R).unit
  have he := bracket_leibniz B hf (show EvenSeries p u from (R).holds) u
  unfold u at he; rw [(R).identityK,(R).identityR,(R).identityK] at he
  exact (by nth_rw 1 [← add_zero (F ♥ (PermV p).unit)] at he; exact (add_left_cancel he).symm)

lemma modulo_unit {X : SpecB A} (hx : EvenSeries p X) : modulo B X (R).unit=0 := by
  unfold modulo; rw [LinearMap.add_apply, bracket_unit B hx,add_zero]; funext n
  change BV (useN.refineV (coin 1) n) = 0
  unfold refineV; split
  · exact B.flat_zero (fun _=>funext fun _=>rfl)
  exact map_zero _

lemma bracket_wages {F X : SpecB A} (hf : EvenSeries p F) (hx : EvenSeries p X) (n : ℕ) :
    F ♥ ((R).wages X (n+1)) = (F ♥ X) ⋄ ((R).wages X n) := by
  induction n with
  | zero => simp only [nextW, firstW, (R).identityR]; simp
  | succ n IH =>
    rw [nextW (n:=n+1), map_smul, bracket_leibniz B hf hx, IH]
    rw [even_middle hx _ _, Dynamics.nextNF, map_smul]
    rw [inv_smul_eq_iff₀ (Dynamics.zeroN' _) ]; push_cast; module

variable {X F : SpecB A}
local notation "L" => modulo B X
local notation "j" => ((1/2:ℂ) • (F ♥ F))
set_option quotPrecheck false
local notation "w" => (PermV p).wages F

lemma modulo_one : L (w (0+1))=L F ⋄ w 0 := by rw [nextW,firstW,(R).identityR,(R).identityR]; simp

lemma modulo_wages (hx : EvenSeries p X) (hf : EvenSeries p F) (n : ℕ) :
    L (w (n+1+1))= L F ⋄ w (n+1) + j ⋄ w n := by
  have he i : (F ♥ F) ⋄ w i=(2:ℂ) • (j ⋄ w i) := by simp only [map_smul, LinearMap.smul_apply, smul_smul]; norm_num
  induction n with
  | zero =>
    rw [nextW (n:=0+1), map_smul, modulo_mul B hx hf, modulo_one, bracket_wages B hf hf,
      he, even_middle hf, Dynamics.nextNF, map_smul]
    norm_num; module
  | succ n IH =>
    rw [nextW (n:=n+1+1), map_smul, modulo_mul B hx hf, IH,
      bracket_wages B hf hf, map_add, even_middle hf _ _, even_middle hf _ _,
      Dynamics.nextNF,Dynamics.nextNF, map_smul, map_smul,he]
    rw [inv_smul_eq_iff₀ (Dynamics.zeroN' _)]
    push_cast; module

local notation "N" => (PermV p).cheers F
lemma modulo_cheers (hx : EvenSeries p X) (hf : EvenSeries p F) (n : ℕ) :
    L (N (n+2))= L F ⋄ N (n+1) + j ⋄ N n := by
  induction n with
  | zero =>
    unfold cheers; simp only [show 0+2=0+1+1 from rfl, sum_range_succ, sum_range_zero, zero_add,
      map_add, modulo_wages B hx hf, modulo_one,firstW, modulo_unit B hx]; abel
  | succ n IH =>
    rw [show N (n+1+2)= N (n+2)+ w (n+1+1+1) from sum_range_succ ..,
      map_add, IH, modulo_wages B hx hf, show N (n+1+1)= N (n+1) + w (n+1+1) from sum_range_succ .., map_add]
    rw [show j ⋄ N (n+1) = j ⋄ N n + j ⋄ w (n+1) from by
          rw [show N (n+1) = _ from sum_range_succ .., map_add]
          rfl]
    abel

private lemma bracket_sum {Z : SpecB A} (hz : EvenSeries p Z) (hf : EvenSeries p F) (n : ℕ) :
    Z ♥ (N (n+1)) = (Z ♥ F) ⋄ N n := by
  unfold cheers
  rw [sum_range_succ',map_add, map_sum,map_sum,firstW,bracket_unit B hz,add_zero];
  exact Finset.sum_congr rfl fun i _ => bracket_wages B hz hf i

-- multiplying by a truncated formal exponent to the same order
private lemma relevant (JJ : Bil (BL A) (BL A) (BL A)) (Z : SpecB A) {i n : ℕ}
    (hn : i ≤ n) (h : F 0=0) : pairW JJ Z (exp0 p F) i = pairW JJ Z (N n) i := by
  rw [paired,paired]
  refine Finset.sum_congr rfl fun x hx => ?_
  change JJ (Z x.1) _ = JJ (Z x.1) _
  obtain hz := Finset.mem_antidiagonal.mp hx
  exact congr_arg (JJ (Z x.1)) ((overbook (actor p) useN F h (show x.2 ≤ n from by omega)).symm)

variable (H : Raw A ℂ)
local notation "Y" => useN.refineV H
lemma head_mod (F : SpecB A) : modulo B (useN.refineV H) F = promote (BV + tokenL BV true p H) F := by
  unfold modulo; rw [LinearMap.add_apply, show pairW (tokenL BV true p) = useN.Lift (tokenL BV true p) from rfl,
    useN.tile]; rfl

lemma modulo_exp (hH : Pure p false H) (hf : EvenSeries p F) (h : F 0=0) :
    modulo B Y (exp0 p F) = (modulo B Y F + j) ⋄ exp0 p F := by
  let LT := modulo B Y
  have HY : EvenSeries p Y := refineπ useN H hH
  funext i; simp only [map_add,LinearMap.add_apply,Pi.add_apply]
  rw [head_mod]
  change ((BV : Op A ℂ) + tokenL BV true p H) (exp0 p F i) =
    pairW (product p) (LT F) (exp0 p F) i + pairW (product p) j (exp0 p F) i
  rw [relevant (JJ:=product p) _ (by omega : i ≤  i+1) h, relevant (JJ:=product p) _ (le_refl i) h]
  conv_lhs => rw [show exp0 p F i = N (i+2) i from
      (overbook (actor p) useN F h (by omega : i ≤ i+2)).symm]
  have ht := congr_fun (modulo_cheers B HY hf i) i; rw [head_mod] at ht
  exact ht

lemma bracket_exp {V : SpecB A} (hv : EvenSeries p V) (hf : EvenSeries p F) (h : F 0=0) :
    V ♥ exp0 p F = (V ♥ F) ⋄ exp0 p F := by
  funext i
  rw [relevant _ _ (by omega : i ≤ i+1) h]
  change _ = pairW (product p) (V ♥ F) (exp0 p F) i
  rw [relevant _ _ (le_refl _) h]; exact congr_fun (bracket_sum B hv hf i) i

lemma even_exp (hf : EvenSeries p F) : EvenSeries p (exp0 p F) :=
  costCheer useN (actor p).holds (actor p).close hf

/-- Key finite algebraic comparison: an insertion can come along for the
ride. Intended for H quadratic, F the interaction part *after* removal of H;
not assumed to commute when paired against an arbitrary odd variation. -/
theorem closed_integrand (hH : Pure p false H) (hf : EvenSeries p F)
    (h : F 0=0) (hq : modulo B Y F+j=0)
    {V : SpecB A} (hv : EvenSeries p V)
    (hp : modulo B (Y + F) V=0) :
    modulo B Y (exp0 p F ⋄ V)=0 := by
  let U := exp0 p F
  have Hf : EvenSeries p U := even_exp hf
  rw [modulo_mul _ (refineπ useN H hH) Hf, modulo_exp B H hH hf h,hq,
    map_zero, LinearMap.zero_apply,map_zero,LinearMap.zero_apply,
    zero_add,sym_even B Hf hv,bracket_exp B hv hf h,sym_even B hv hf,← even_central Hf]
  rw [← map_add]
  have he : modulo B Y V + (F ♥ V)=0 := by
    rw [← hp]
    unfold modulo; simp only [LinearMap.add_apply,map_add]; abel
  rw [he,map_zero]


lemma initial_tok {E : SpecB A} (ht : tokM B E=0) :
    tokM B (useN.refineV (E 0)) = 0 := by
  funext n
  unfold tokM
  simp only [Pi.add_apply,Pi.smul_apply,promised]
  have he : pairW (tokenL BV true p) = useN.Lift (tokenL BV true p) := rfl
  rw [he, useN.tile]; dsimp only;  by_cases hz : n=0
  · subst n
    have hu := congr_fun ht 0
    unfold tokM at hu; simp_rw [Pi.add_apply, Pi.smul_apply,promised, paired, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton] at hu
    rw [show useN.refineV (E 0) 0=E 0 from if_pos rfl]; exact hu
  rw [show useN.refineV (E 0) n=0 from if_neg hz]; simp only [map_zero,smul_zero,add_zero,Pi.zero_apply]

lemma interaction_master {U : SpecB A} (h : tokM B U=0) (hf : EvenSeries p F)
    (hu : U=Y+F) (he : U 0=H) (hv : Pure p false H) : modulo B Y F + j=0 := by
  have ht := initial_tok B h; rw [he] at ht; rw [hu] at h
  unfold tokM at ht h; unfold modulo
  simp only [map_add,LinearMap.add_apply,smul_add] at h
  have hy : EvenSeries p Y := refineπ useN H hv
  rw [sym_even B hf hy] at h
  rw [LinearMap.add_apply]
  linear_combination (norm:=module) h - ht

/-- For multiple insertions carrying no antifields the bracket between them
vanishes. The usual mixed measure polynomial here uses a *shared* vacuum;
multiplying observables doesn't multiply separate vacua. -/
def HasNoDuals (F : SpecB A) := ∀ n (i:I), D (B.dual i) (F n) = 0

omit [Fintype I] in
lemma pair_no_duals (F V : SpecB A) (hf : HasNoDuals B F) (hv : HasNoDuals B V) :
    HasNoDuals B (F ⋄ V) := by
  intro n i
  change D _ (∑ x∈antidiagonal n,product p (F x.1) (V x.2))=0
  simp_rw [map_sum,D_product,hf _ i,hv _ i,map_zero,LinearMap.zero_apply,
    add_zero, Finset.sum_const_zero]

omit [Fintype I] in
lemma unit_no_duals : HasNoDuals B (R).unit := by
  intro n i
  change D _ (useN.refineV (coin 1) n)=0
  unfold SplitP.refineV; split
  · funext k; rfl
  exact map_zero _

lemma prod_zero_bracket {U V : SpecB A} (hf : EvenSeries p U) (hu : HasNoDuals B U) (hv : HasNoDuals B V) :
    U ♥ V=0 := by
  funext n; rw [paired]; refine Finset.sum_eq_zero fun x _ => ?_
  change link BV true p _ _ = 0
  rw [B.by_lap ((even_coeff _).mp hf _)]
  simp_rw [hu _ _,hv _ _,map_zero, LinearMap.zero_apply,add_zero,smul_zero,
    Finset.sum_const_zero]

structure MarkOK (X F : SpecB A) : Prop where
  typeF : EvenSeries p F
  finiteF : Γ F p
  noantifield : HasNoDuals B F
  closed : modulo B X F=0

namespace MarkOK
variable {B}
lemma mul {U V : SpecB A} (hu : MarkOK B X U) (hv : MarkOK B X V)
    (hx : EvenSeries p X) : MarkOK B X (U ⋄ V) := by
  refine ⟨(R).close _ hu.typeF _ hv.typeF, ΤΓ_pair hu.finiteF hv.finiteF,
    pair_no_duals _ _ _ hu.noantifield hv.noantifield,?_⟩
  rw [modulo_mul B hx hu.typeF,prod_zero_bracket B hu.typeF hu.noantifield hv.noantifield, hu.closed,
    hv.closed,map_zero,map_zero,LinearMap.zero_apply,zero_add,add_zero]
lemma unit (hx : EvenSeries p X) : MarkOK B X (R).unit :=
  ⟨(R).holds,refineπ useN (actor p).unit feeUnit,unit_no_duals B,modulo_unit _ hx⟩

variable {W : Type} [LinearOrder W] (P : Finset W → SpecB A)
  (hw : ∀ (v:W), MarkOK B X (P {v}))(hp : ∀ s : Finset W, s.card ≠ 1 → P s=0)
include hp hw
omit [LinearOrder W] in
lemma tokens (s : Finset W) : EvenSeries p (P s) := by
  by_cases hz:s.card=1
  · obtain ⟨u,rfl⟩:=Finset.card_eq_one.mp hz
    exact (hw u).typeF
  rw [hp _ hz]; exact (R).guard.zero_mem

lemma products (hx : EvenSeries p X) (s : Finset W) : MarkOK B X (Font p P s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show Font p P ∅ = (PermV p).unit from Stencil.simple_E _ _ _ (hp ∅ (by simp))] -- add parens
    exact unit hx
  | @insert v s hv IH =>
    have ht := Stencil.cheers (R) (tokens P hw hp) hp s v hv
    unfold Font at *; rw [ht]; exact (hw v).mul IH hx
end MarkOK

end YM.FVA2.Inserted
