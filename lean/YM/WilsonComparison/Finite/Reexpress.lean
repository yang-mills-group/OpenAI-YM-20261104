import YM.WilsonComparison.Finite.Landau
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Change t and form columns (not a change in the Wilson vacuum for each field)

Re-express single canonical t as in the supplied `Program.shift` (depends on log scale
and common team, **not** the columns or markers). We do this on formal series, not
truncating the Burnt handouts. Then mix insertion columns with arbitrary series, using
one expression in the bare coupling and independent field-placement dictionary. Columns
and normalization in physical units tied up at the removal endpoint later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Finset Precision Lattice
open MS MS.Landau MS.Swirl MS.Swirl.Near MS.Orbit MS.Orbit.Cog Orbit.LogReal MS.Native
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors
open MS.Book.Convolve MS.Book.Program MS.Native.Wilsonian
open MSBar Barr Bric Inlay Odom
open PowerSeries (coeff)
open scoped BigOperators Classical
variable {G:Gauge} {χ:ChartRatio G} {m n:Side}
variable {A E Q I W:Type} {p:A→Bool} [AddCommGroup E][Module ℂ E][AddCommGroup Q][Module ℂ Q]
variable {a : PowerSeries ℂ} (ha:Rooted a)

section Substitute
variable (M:Actors E)
lemma stack_rule (x y : T E) : (M.stack useN).core x y=pairW M.core x y:= rfl
lemma skin (F:E) (a:PowerSeries ℂ) : substitute a (useN.refineV F) = useN.refineV F := by
  funext i; rw [rules,Finset.sum_eq_single_of_mem 0 (by simp)];
  · unfold refineV; rw [show useN.origin=0 from rfl,if_pos rfl]; unfold MS.Book.Program.cut; rw [pow_zero,PowerSeries.coeff_one]; split <;> simp
  intro b _ hb; unfold refineV; rw [if_neg (show b≠ useN.origin from hb),smul_zero]
include ha
lemma perm_hom : Tether (substitute a) (M.stack useN) (M.stack useN) := ⟨skin _ _,fun x y=> (substitute_pair ha x y M.core).symm⟩
lemma keep_cheer (V:T E) (h:Happy useN V) : substitute a (Actors.Cheer M useN V)=Actors.Cheer M useN (substitute a V):= by
  let P:=M.stack useN; funext i
  have H0 : Happy useN (substitute a V):=(pay0 a V).trans h
  rw [← overbook M useN _ H0 (n:=i) le_rfl]
  change _= P.cheers _ _ i
  rw [ ← (perm_hom ha M).cheersV i V,rules,rules]; exact sum_congr rfl fun b hb=> (congr_arg (_ • ·) (overbook M useN _ h (n:=i) (mem_Iic.mp hb))).symm
omit ha in
lemma keep_guard {V:T E} (h: V∈(M.stack useN).guard) : substitute a V ∈ (M.stack useN).guard:= by
  intro i _; rw [rules]; exact M.guard.sum_mem fun j _=> M.guard.smul_mem (Book.Program.cut a _ i) (h j (Set.mem_univ _))
variable [Fintype A] {K:Grain A} {V q:SpecB A} {Y:T ℂ}
lemma move_End (h:Endμ K p q V Y) (ht:q 0=0) : Endμ K p (substitute a q) (substitute a V) (substitute a Y):= by
  unfold Endμ exp0; rw [ ← keep_cheer ha (actor p) q ht,← (perm_hom ha (actor p)).craft]
  rw [show ℶV K=promote (View K) from rfl,MS.Book.Program.comm, MS.Book.Program.comm, ← (perm_hom ha Toy).craft]; exact congr_arg (substitute a (P:=ℂ)) h
end Substitute

section Real
-- Public identities, for use with PowerSeries-based APIs.
/-- Real change, t(N minimum-valuation action) ↔ MS formal at cutoff.
  Evaluation at log-scale y fixed. -/
def toBare (φ:Team) (y:ℝ) : PowerSeries ℝ := PowerSeries.mk fun k=> if k=0 then 0 else if k=1 then 1 else (φ k).coupling.eval y
lemma shift_toBare (φ:Team)(y:ℝ) : PowerSeries.map Complex.ofRealHom (toBare φ y)=shift φ y:= by
  ext i; rw [shift,PowerSeries.coeff_map,toBare, PowerSeries.coeff_mk, PowerSeries.coeff_mk]; split_ifs <;> simp
include ha in
lemma reexpr_unique (V:PowerSeries ℂ) : substitute a (fun i=> coeff i V) = fun i=> coeff i (PowerSeries.subst a V):= by
  funext i; rw [rules,PowerSeries.coeff_subst']
  swap; · exact PowerSeries.HasSubst.of_constantCoeff_zero (by change PowerSeries.constantCoeff a=0; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact ha)
  rw [finsum_eq_sum_of_support_subset _ ?s];
  · exact sum_congr rfl fun j _=> by simp [Book.Program.cut,mul_comm]
  case s=> intro j hj; by_contra hx; change _ ≠0 at hj; apply hj;
            dsimp only; rw [ show coeff i (a^j)=0 from blocked ha (by simp at hx; omega) ]; simp
end Real

-- billing with sequence weights. works noncomm at product via actor
section Change
variable (V : E →ₗ[ℂ] Q) (M:Actors E) (x y:T E) (f:T ℂ)
abbrev rates (E:Type) [AddCommGroup E][Module ℂ E] := pairW (LinearMap.lsmul ℂ E)
lemma pass_rate : pointL ℕ V (rates E f x)=rates Q f (pointL ℕ V x):= by
  funext i; change V _=_; rw [rates,paired,map_sum]; exact sum_congr rfl fun _ _=> map_smul V _ _
lemma left_rate : (M.stack useN).core (rates E f x) y = rates E f ((M.stack useN).core x y) := by
  funext i; rw [stack_rule,paired]; unfold rates; simp only [stack_rule,paired, map_sum, LinearMap.sum_apply]
  simp_rw [LinearMap.lsmul_apply,map_smul, LinearMap.smul_apply]; exact (associate (fun i j k=> f i • M.core (x j) (y k)) _).symm
lemma right_rate : (M.stack useN).core y (rates E f x) = rates E f ((M.stack useN).core y x) := by
  funext i; rw [stack_rule,paired]; unfold rates; simp_rw [paired,map_sum, LinearMap.lsmul_apply,map_smul,stack_rule,paired,Finset.smul_sum]; exact rewrap useN E (fun k j i=> f j • M.core (y k) (x i)) _ -- rhs rotated
lemma rate_ok {x:T E} (h:x∈(M.stack useN).guard) : rates E f x ∈ (M.stack useN).guard:= by
  intro i _; rw [rates,paired]; exact M.guard.sum_mem (t:=antidiagonal i) fun j _=> M.guard.smul_mem (f j.1) (h j.2 (Set.mem_univ _))
variable [Fintype A] {K:Grain A} {V₁ V₂ q:SpecB A} {Y Y':T ℂ}
lemma zeroEnd : Endμ K p q 0 0 := by unfold Endμ; rw [map_zero,map_zero,map_zero]
lemma sumEnd (h:Endμ K p q V₁ Y) (h':Endμ K p q V₂ Y'):
    Endμ K p q (V₁+V₂) (Y+Y'):= by unfold Endμ; rw [map_add,map_add,map_add,h,h']
lemma payEnd (h:Endμ K p q V₁ Y): Endμ K p q (rates _ f V₁) (Trunk.core f Y) := by
  unfold Endμ; rw [right_rate (M:=actor p),ℶV,pass_rate];
  change rates ℂ f (ℶV K ((PermV p).core (exp0 p q) _))= (Toy.stack useN).core _ (rates ℂ f Y)
  rw [h,right_rate (M:=Toy)]
end Change
end YM.WilsonComparison.Finite
