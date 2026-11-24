import YM.FVA2.Handoff.Closure

/-!
# XSpace diagram predictions from the epoch prescription

The final formal comparison is `Main.wilson_to_MS` in `YM/FVA2/Main.lean`.
No hypotheses from continuum MS comparison or from UV-uniform
asymptotics are required for the following results.
In particular these claims are not about convergence of the physical theory (the word
prediction refers to diagram predictions). We give here some helpful explicit identities for
applications which will want to compute (or compare to) precisely these quantities, before
applying `Main.wilson_to_MS`.

A horizon here is a horizon of *engineering dimensions* of the physical polynomial Maxwell-Wick
labels of `YM/XSpace`. Perturbative expansion is in one common `g` (keeping normalization & Laurent
conventions of that library). Native words in top lattice units; here we also provide the
conversion to common length-one units as used for the center scans etc. It's *exactly* the answer from
the epoch `N.serial`, at each regulator and test placement -- we don't truncate correlators to selected
momenta, rank, or estimate-geometries.

* use `Arrival.Episodic.candle` at that epoch, or `Folio.coefficients`, to compute the Wilson
  expectations entering this PT comparison & to use from the analytic task, for an arbitrary
  list of Folio stencils (choose *all*
  W pieces `Arrival.Birth.scan` on the physical insertion). We don't require any
  UV estimate hypotheses for these fields. `YM/FVA2/Handoff/Closure` also allows using
  `Fk` specifically to do that reconstruction, with the **full** field-dependent conditional
  denominator. In fact `Directory.from_fk` and
  `lit_exact` below reconstruct the *entire* initial
  point and batch arrays for any mark placements (via `point_fk`)
  and profiles directly from the `Fk` open evaluations
  (also linking the position solve/detector inputs to that formulation). Need only through
  the requested order on `D : Directory`, for a concrete `budget` even independent of profiles
  (this is about shift in **order**, not an analytic estimate!).
* `α` here gives the exact physical-units point arrays on the `Toon` basis, `sweep` is the XSpace
  smearing. Here's how to use that: use `batch_exact` below to get the exact **initial report
  batches** from these epochs, ordinary correlation arrays on **all** physical labels & arities.
  This is *before* applying any `realm` change of field basis even with mesh-dependent coefficients,
  before the position solve and before coupling conversion. (In particular it's before that
  D-renormalization of the bare fields at problematic sizes, not defining from MS!)
  Coupling is top Wilson expansion variable, taken at any finite cutoff on `N.run`. Once specializing to the
  calibrated X position predictions, apply the same detector and Store, and read `Store.opens` etc.
  exactly as in `Main.lean` and there use *those* predictions, still with the stencil and prescription
  here. These identities apply also on samples for which the meaningful estimate geometries aren't met.
  Take care to require the geometry then; this isn't an assertion that the estimates hold generally.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Handoff

open Lattice Function Set Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Cirrus XSpace.Structure1
open Register Arrival
open scoped Classical BigOperators Topology

variable {G : Gauge} (N : WilsonPrescription G) (i n d : ℕ)
local notation "Y" => WilsonPrescription.scheme N
set_option quotPrecheck false
local notation "m" => N.run.step i
local notation "T" => N.scheme.tree (N.run.step i).p
local notation "W" => Fin n

section Pure
variable {d : Fin n → ℕ} (t : (j : Fin n) → Dframe.Toon G (d j))
abbrev grade : W→ℕ := fun j => (t j).size
local notation "r" => grade n t
variable (x : Fin n → Cover)
abbrev wordSymbols : List (Arrival.Birth G) := Finset.univ.toList.map fun j:W =>
    ⟨ d j,t j,x j ⟩
/-- A particular tuple of components in the through-size basis (each is the sum with all W pieces
assembled).
Each field uses its own homogeneous
`XSpace.On.Grade` dimension component. Multipliers `spacing ^(..)` even factor through vacuum-normalized epoch. -/
def α : PowerSeries ℂ :=
    Dframe.Csum m r • PowerSeries.map Complex.ofRealHom (N.serial i (wordSymbols n t x))

lemma pointExact : α N i n t x =
    N.scheme.atTuple m r (wrap (N.run.step i).p.side ∘ x) (fun j=> Arrival.Birth.theory (t j)) := by
    unfold α WilsonPrescription.serial
    rw [Arrival.Episodic.sum_world]
    let A (j:W) := XSpace.On.stencil N.scheme.hol (N.scheme.surveys (r j)) (N.run.step i).p T
        ((wrap (N.run.step i).p.side ∘ x) j) (Arrival.Birth.theory (t j))
    have he : XSpace.Bare.normalized T G (∏ j:W,A j) =
        PowerSeries.map Complex.ofRealHom (Birth.words Y (N.run.step i).p.side (wordSymbols n t x)) :=
      Birth.compact_labels Y T Finset.univ x d t
    rw [← he, ← map_smul, Initialize.atTuple_eq]
    apply congr_arg
    suffices ∀ e : Finset W, (∏ j∈e, Dframe.Ufee m (r j)) • (∏ j∈e,A j) =
        ∏ j∈e,N.scheme.atSite m (r j) ((wrap (N.run.step i).p.side ∘ x) j) (Arrival.Birth.theory (t j))
        from this Finset.univ
    intro e; induction e using Finset.induction_on with
    | empty => simp
    | insert j e hj ih=>
        symm; rw [Finset.prod_insert hj,Finset.prod_insert hj,Finset.prod_insert hj, ← ih]
        rw [Initialize.atSite, LinearMap.smul_apply, ← inv_pow, mul_smul, smul_mul_assoc, mul_smul_comm]

variable (a : Test n)
def sweep : PowerSeries ℂ :=
    (((N.run.step i).spacing:ℂ)^(4*n)) • ∑ x : Fin n→(N.run.step i).Sites,
      (N.run.step i).smear (Lattice.lift ∘ x) a • α N i n t (Lattice.lift ∘ x)
lemma sweepExact : sweep N i n t a = N.scheme.report m r a (fun j=>Arrival.Birth.theory (t j)) := by
    unfold sweep; rw [Initialize.report_formula]; simp_rw [pointExact]
    apply congr_arg (((N.run.step i).spacing:ℂ)^(4*n) • ·); refine Finset.sum_congr rfl (fun x _=>?_)
    rw [show (wrap (N.run.step i).p.side ∘ (Lattice.lift ∘ x))=x from funext (fun q=>Lattice.wrap_lift _)]
end Pure

variable (p : Tags G d n) (a : Test n)

/-- Exact initial XSpace `batch`. This, with the point arrays, is used in evaluating the
physical coupling detector and columns.
All expansion orders, and parameters from only the *independent* epoch prescription. -/
theorem batch_exact (k : ℕ) : batch Y m d k n a p =
    ∑ t : Fin n → Dframe.Toon G d,
     (Dframe.each t p) * PowerSeries.coeff k (sweep N i n (d:=fun _=>d) t a) := by
    rw [Dframe.stencil_he ( batch Y m d k n a ) p]
    apply Finset.sum_congr rfl; intro t _; rw [sweepExact]
    congr 1
    exact ( indicated Y m (L:=fun j=>⟨(t j).size,Nat.lt_add_one_iff.mpr (Dframe.size_le (t j))⟩)
        (fun j=>Arrival.Birth.theory (t j)) a k)

namespace Directory
open FormalOPE.RG10

variable {i N} {M : ℕ} (D : Directory N i M) (t : Fin n → Dframe.Toon G d)
def budget (G : Gauge) (n d : ℕ) := n * (Finset.univ.sup (fun v : Dframe.Toon G d => v.grade))
lemma cost (x : Fin n → Cover) : requested (wordSymbols n (d:=fun _=>d) t x) ≤ budget G n d := by
    unfold wordSymbols requested budget; rw [List.map_map, Finset.sum_map_toList]
    let f := Finset.univ.sup (fun v : Dframe.Toon G d => v.grade)
    have he : ∑ _ : Fin n, f = n * f := by simp
    rw [← he]
    exact Finset.sum_le_sum (fun j _=>
        Finset.le_sup (f:=fun v : Dframe.Toon G d=>v.grade) (Finset.mem_univ (t j)))

/-- Reconstruct the unpositioned correlator from the open conditional results.
Use `M` to determine allowed `k` (vary `x` and **all** the mark labels, keep `n,d` within budget).
Not a limit construction. -/
def point_fk (x : Fin n → Cover) : PowerSeries ℂ :=
    Dframe.Csum m (grade n (d:=fun _=>d) t) •
      PowerSeries.map Complex.ofRealHom (D.product (wordSymbols n (d:=fun _=>d) t x))

lemma point_construct (x : Fin n → Cover) (U : ℕ) (h : budget G n d + U ≤ M) :
    Through U (D.point_fk n d t x) (α N i n (d:=fun _=>d) t x) := by
    intro j hj
    rw [point_fk, α, map_smul,map_smul,PowerSeries.coeff_map,PowerSeries.coeff_map]
    exact congr_arg (_ • ·) (congr_arg Complex.ofRealHom
        (D.scan_construct _ U ((Nat.add_le_add_right (cost n d t x) U).trans h) j hj))

lemma lit_exact (x : Fin n → Cover) (k : ℕ) (h : budget G n d + k ≤ M) :
    litP Y d m (wrap (N.run.step i).p.side ∘ x) k p =
      ∑ t : Fin n → Dframe.Toon G d,
        Dframe.each t p * PowerSeries.coeff k (D.point_fk n d t x) := by
    let v : Sample n := ⟨m,x,0⟩
    have hp (t : Fin n → Dframe.Toon G d) : live Y d v k (Dframe.fill t) =
        PowerSeries.coeff k (α N i n (d:=fun _=>d) t x) := by
      rw [pointExact]
      exact (lives Y d v (j:=grade n (d:=fun _=>d) t) (fun i=>Arrival.Birth.theory (t i)) (fun i=>Dframe.size_le (t i)) k)
    change live Y d v k p=_
    rw [Dframe.stencil_he (live Y d v k) p]
    exact Finset.sum_congr rfl (fun t _=>by rw [hp, D.point_construct n d t x k h k le_rfl])

def sweep_fk : PowerSeries ℂ :=
    (((N.run.step i).spacing:ℂ)^(4*n)) • ∑ x : Fin n→(N.run.step i).Sites,
      (N.run.step i).smear (Lattice.lift ∘ x) a • D.point_fk n d t (Lattice.lift ∘ x)

theorem from_fk (k : ℕ) (h : budget G n d + k ≤ M) : batch Y m d k n a p =
    ∑ t : Fin n → Dframe.Toon G d,
     (Dframe.each t p) * PowerSeries.coeff k (D.sweep_fk n d a t) := by
    rw [batch_exact N i n d]; apply Finset.sum_congr rfl; intro t _
    rw [sweep_fk, sweep]; simp only [map_smul, map_sum]
    simp_rw [show ∀ x:Fin n → Cover,PowerSeries.coeff k (D.point_fk n d t x)=_
        from fun x=> D.point_construct n d t x k h k le_rfl]

end Directory

end YM.FVA2.Handoff
