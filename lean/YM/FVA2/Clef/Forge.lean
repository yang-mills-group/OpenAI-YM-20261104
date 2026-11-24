import YM.FVA2.Clef.Ticks
/-!
# Recursive proof of uniqueness for the generator criterion

At a fixed field horizon. Uses absence of the lower-grade part in the
hypothesis `Native` (see in `Winds`); starts from the leading forms in
`Base` and inducts. Not an assertion about finite-coupling generators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
private abbrev Frame (G:Gauge)(d:ℕ):= Guard G d
local notation "𝒯" => (Frame G d)
local notation "C₀" => (0: Guard G d)
section induction
variable {S T D₀: Guard G d}
-- leading terms of a formal matrix product
private lemma attain_r (h:coeff 0 T=0)(hz:Base S)(he:∀ i,0 < i → i < n → coeff i S=0): coeff n ( T*S )=coeff n T:= by
    rw [ PowerSeries.coeff_mul, Finset.sum_eq_single (n,0), hz.zero,mul_one ]; intro a hA ha; obtain ⟨i,j⟩:=a; have hs : i+j=n:= by simpa using hA
    by_cases h':i=0; simp [h',h]; have he': j≠0:= by intro h; subst j; simp_all -- contradictions
    change coeff i T * coeff j S=_; rw [ he j (by omega) ( by omega ),mul_zero ]
    simp
private lemma attain_l (h:coeff 0 T=0)(hz:Base S)(he:∀ i,0 < i → i < n → coeff i S=0): coeff n ( S*T )= coeff n T:= by
    rw [ PowerSeries.coeff_mul, Finset.sum_eq_single (0,n),hz.zero,one_mul ]; intro a hA ha; obtain ⟨j,i⟩:=a; have hs:j+i=n:=by simpa using hA
    by_cases h':i=0; simp [h',h]; have he': j≠0:= by intro h; subst j; simp_all
    change coeff j S * coeff i T=_; rw [ he j (by omega) ( by omega ),zero_mul ]
    simp
private lemma spinR (q:Cn) (h:Rooted q)(hv:PowerSeries.coeff 1 q=0)(he:∀ i,0 < i → i < n → coeff i S=0): coeff n ( Generator.Drive.central q (D S) )=0:= by
    unfold Generator.Drive.central; rw [coeff_mk ]; apply Finset.sum_eq_zero; intro ⟨i,j⟩ h'; have hh:i+j=n:=by simpa using h'
    rcases eq_or_ne i 0 with h0|h0; subst i; rw [h,zero_smul]; rcases eq_or_ne i 1 with h1|h1; subst i; rw [hv,zero_smul]; change (coeff i q) • (coeff j (Generator.Drive.D S))=0; rw [Generator.Drive.D,coeff_mk,he _ (by omega) (by omega),smul_zero,smul_zero] -- may Prod.F
private lemma erase_s (h:Native T)(he:Native D₀) : Native (T-D₀):= by intro i; unfold Graded; rw [_root_.map_sub, map_sub (Level.diag (G:=G) (d:=d)),h,he]
local notation "wgt"=> weight
/-- Recursive justification of grading-forcing step
   $T=Γ(X), D₀=Γ(N), S$ strict relative matrix. No `b` formula needed.
 -/
lemma recur (q:Cn)(hq:Rooted q)(he:PowerSeries.coeff 1 q=0)(hp:Base S)(hs:Scale.remainder S)
    (ht:Native T)(hu:Native D₀)(hT: coeff 0 T=0)(hU:coeff 0 D₀=0)
    (H:T*S + Generator.Drive.central q (D S) = wgt S + S * D₀): S=1:= by
    ext1 i;
    induction i using Nat.strong_induction_on with
    | _ i ih=> by_cases hx:i=0; subst i; rw [hp.zero,coeff_zero_eq_constantCoeff_apply,map_one];
               replace ih: ∀ j,0 < j → j < i → coeff j S=0:=by intro j hj h; rw [ ih j h,coeff_one,if_neg (by omega) ]; -- readability
               have hv:= congr_arg (coeff i) H; rw [ map_add,map_add, attain_r hT hp ih,attain_l hU hp ih,spinR q hq he ih,add_zero ] at hv; rw [coeff_one, if_neg hx ]; apply height; · rw [← show coeff i ( Scale.diagonal S )=_ from (coeff_mk ..),hs, coeff_one,if_neg hx]
               rw [ show coeff i ( weight S )= coeff i (T-D₀) from (by rw [ map_sub,hv ]; abel) ]; exact erase_s ht hu i
end induction
end YM.FVA2.Clef
