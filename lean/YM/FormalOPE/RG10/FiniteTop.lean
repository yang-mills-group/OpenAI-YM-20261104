import YM.FormalOPE.RG10.Restriction
import YM.FormalOPE.RG10.Stamps
import YM.FormalOPE.RG10.Linear

/-! # The multi-insertion prescription at the finite-regulator end

No convergence of perturbative or OPE series. Estimates like `Series.Tested.Aspiration` at
ONE fixed finite size in the *auxiliary* regulator, not claiming a derivative or an actual
correlation comparison. Allows equal labels and positions, overlapping stencils, unmarked rank
zero outputs etc.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionTop
open Lattice PertExtension PertExtension.Chart PertExtension.Orb Wilson PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open Marker Extra.Trajectories RG10.Word Function
open scoped BigOperators Topology ContDiff Classical

variable {G : Gauge} {n : Side} (hn : Even n.val)
local notation "P" => tray G
local notation "F" => feed (G:=G) hn
local notation "W" => vertices G n
variable {I : Type*} {t : Finset I} (O : I → Stamp G n)

namespace Stamp

/-- all subproducts may occur in the log. -/
abbrev factors := fun i => (O i).couplingMark

def shafts (s : Finset I) := ∏ i∈s, (O i).stencil

def degrees (s : Finset I) := ∑ i∈s, (O i).slots

lemma pre_all (s : Finset I) : PreTest (shafts O s) := by
  unfold shafts
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]; exact ⟨fun _ _ _ => rfl, one_test, continuous_const⟩
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact Uses.pre_mul (O i).test ih

lemma uses_all (s : Finset I) :
    Uses.AtCoupling (shafts O s) (degrees O s) (∏ i∈s, factors O i) := by
  induction s using Finset.induction_on with
  | empty =>
    unfold shafts degrees; rw [Finset.sum_empty, Finset.prod_empty, Finset.prod_empty];
    unfold Uses.AtCoupling; rw [delay_zero]; exact raw_one.symm
  | insert i s hi ih =>
    unfold shafts degrees; rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact Uses.combine (O i).test (pre_all O s) (O i).atCoupling ih

lemma pre_formula (s : Finset I) :
    Aspiration (fun g : ℝ => (g⁻¹)^(degrees O s) * preExpectation (shafts O s) g)
      (fun i => (coeff i ((F).ordinary W s (factors O))).re) :=
  Uses.inversionFormula hn (pre_all ..) (uses_all ..)

/-- Extend the Taylor slot prescription coefficientwise through every occurrence, consistently
across subsets. Working with actual products before taking the logarithm. -/
theorem orbit_coeff (s : Finset I) : (F).ordinary W s (factors O) =
    lower (degrees O s) (into (PowerSeries.mk (diag (restrictedO (shafts O s))))) := by
  rw [Uses.advance hn (pre_all ..) (uses_all O s), lower_delay]; rfl

theorem integrals (s : Finset I) : (F).Funded ((W).weight * ∏ i∈s, factors O i) :=
  Uses.paid hn (pre_all O s) (uses_all O s)

section
variable [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
variable (c : (i : I) → J i → RG10.Series) (A : (i : I) → J i → Stamp G n)

theorem combine_stamps :
    let f := FlatFeed.combined c (fun i j => (A i j).couplingMark)
    (F).Funded ((W).weight * ∏ i, f i) ∧
    (F).step W (∏ i, f i) =
      ∑ s : (i : I) → J i, (∏ i,c i (s i)) * (lower (degrees (fun i => A i (s i)) Finset.univ)
        <| into (PowerSeries.mk (diag (restrictedO (shafts (fun i => A i (s i)) Finset.univ))))) := by
  intro f
  obtain ⟨h,he⟩ := FlatFeed.combination c (fun i j => (A i j).couplingMark) (fun s =>
    integrals hn (fun i => A i (s i)) Finset.univ)
  refine ⟨h,he.trans ?_⟩; apply Finset.sum_congr rfl; intro s _;
  rw [← orbit_coeff hn]

omit [Fintype I] in
/-- Evaluation at any allowed mode of the original census (honest subset, not all source labels
need to be read together). -/
theorem combine_at (t : Finset I) :
    let f := FlatFeed.combined c (fun i j => (A i j).couplingMark)
    (F).Funded ((W).weight * ∏ i∈t, f i) ∧
    (F).step W (∏ i∈t, f i) =
      ∑ s : (i : ↥t) → J i.val, (∏ i : ↥t,c i.val (s i)) *
        (lower (degrees (fun i : ↥t => A i.val (s i)) Finset.univ) <| into
          (PowerSeries.mk (diag (restrictedO (shafts (fun i : ↥t => A i.val (s i)) Finset.univ))))) := by
  intro f
  rw [← Finset.prod_attach, show t.attach = Finset.univ from by ext; simp]
  convert! combine_stamps hn (fun i : ↥t => c i.val) (fun i : ↥t => A i.val) using 1
  congr! 3
end
end Stamp

section allMarks
variable {V U : Type} [DecidableEq V] [DecidableEq U] [Fintype V] [Fintype U]
    (R : Census V) (A : V → Stamp G n)

/-- Concrete marked pre-log representative, all finite horizons (retain the stamps/dim
announcements, so enlarging the allowed census cannot change a stamp). -/
abbrev publish := fun x => emit R (fun i => (A i).couplingMark x)

theorem ordinaryOrbit : (F).close W (publish R A) = RG10.Word.package (R:=R) fun s =>
    lower (Stamp.degrees A s.val) (into (PowerSeries.mk (diag (restrictedO (Stamp.shafts A s.val))))) := by
  apply RG10.Word.observe_ext; intro m; rw [RG10.Word.see_package]
  exact ((F).closing_emission W R (Stamp.factors A) m).trans (Stamp.orbit_coeff ..)

theorem markedOrbit :
    (F).markedFunded W (publish R A) ∧
    vac R ((F).contraction W (publish R A)) = 0 ∧
    RG10.Word.expMark ((F).contraction W (publish R A)) = (F).close W (publish R A) := by
  have hx : RG10.Word.read R.quiet (publish R A)=1:= funext (fun x => RG10.Word.emit_unit ..)
  refine ⟨?_,vac_log _ (FlatFeed.preserve_one F W hx), FlatFeed.reclosure F W hx⟩
  intro s; rw [FlatFeed.totalize_read, RG10.Word.read_emitted]; exact Stamp.integrals hn A s.val

theorem existing_subset (r : ℕ) (S : Census U) (u : Names S R) :
    let c := (F).contraction W (publish R A)
    let c' := (F).contraction W (publish S (fun i => A (u.e i)))
    trunc (r+1) c' = trunc (r+1) (eraseMarks u c) ∧
    trunc (r+1) (expMark c') = trunc (r+1) (eraseMarks u (expMark c)) :=
  FlatFeed.compatible F ⟨fun _ => Through.refl _, fun _ => Through.refl _⟩ u
    (funext (fun _ => emit_unit ..)) (funext (fun _ => emit_unit ..))
    (fun x => (FlatFeed.identical_input u (f:=fun i => (A (u.e i)).couplingMark)
      (g:=fun i => (A i).couplingMark) (fun _ => rfl) x).symm ▸ Through.refl _)
end allMarks
end YM.FormalOPE.RG10.InversionTop
