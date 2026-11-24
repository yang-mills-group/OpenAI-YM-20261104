import YM.Integration.WilsonOriginalOccupiedDegree
import YM.Integration.WilsonOriginalOccupiedStencil
import YM.Integration.WilsonSeparatedPrefixCanonicalZeroPost

/-! The genuine canonical finite gas, including all its disjoint owners, is a polynomial
of degree at most the number of names on the tested ordinary face. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalPolynomial
open Finset Lattice RG Wilson Marker QuadraticLocal Fusion Fusion.Attached Polynomial
open MergeProof MergeProof.Accent Extra.Histories
open WilsonOriginalOccupiedDegree
open scoped BigOperators Classical
variable {V:Type} [DecidableEq V] {J:Census V}
private theorem plus {f g:ℂ → Poly J}(a:Rendered f)(b:Rendered g):Rendered (fun z=>f z+g z):=by
  intro s
  obtain ⟨p,pc,hp⟩:=a s
  obtain ⟨q,qc,hq⟩:=b s
  exact ⟨p+q,(natDegree_add_le p q).trans (max_le pc qc),fun z=>by rw [eval_add,hp,hq,Poly.part_plus]⟩
private theorem sum {I:Type} (S:Finset I) {f:I → ℂ → Poly J}
    (terms:∀v,Rendered (f v)):Rendered (fun z=>∑v∈S,f v z):=by
  induction S using Finset.induction_on with
  | empty=>simpa only [sum_empty] using constant (0:Poly J)
  | @insert v S fresh ih=>simpa only [sum_insert fresh] using plus (terms v) ih
private theorem power {f:ℂ → Poly J}(ok:Rendered f)(r:ℕ):Rendered (fun z=>f z^r):=by
  induction r with
  | zero=>simpa only [pow_zero] using constant (1:Poly J)
  | succ r ih=>simpa only [pow_succ] using product ih ok
private theorem multiplier {f:ℂ → Poly J}(ok:Rendered f)(c:ℂ):Rendered (fun z=>c • f z):=by
  intro s
  obtain ⟨p,deg,eq⟩:=ok s
  exact ⟨C c*p,natDegree_mul_le.trans (by simpa using deg),fun z=>by simp [eq,Poly.part_smul]⟩
private theorem affine_zero (p:Poly J)(zero:p.part J.quiet=0):Rendered (fun z=>z • p):=by
  have same (z:ℂ) : WilsonOriginalOccupiedTap.paint z p=z • p:=by
    ext s
    change WilsonOriginalOccupiedTap.amount z s*p.part s=z*p.part s
    by_cases h:s=J.quiet
    · rw [h,zero,mul_zero,mul_zero]
    · simp [WilsonOriginalOccupiedTap.amount,h]
  exact fun s=>by simpa only [same] using (affine p s)
private theorem exponential [Fintype V] {f:ℂ → Poly J}(r:Rendered f):Rendered (fun z=>Poly.pass (f z)):=by
  exact sum (range (Fintype.card V+1)) (fun i=>multiplier (power r i) _)

variable [Fintype V] {G:Gauge} {n:Side} (P:Rep G n)
  (H₀ H₁:Support n → Config G n → Poly J)(K₀ K₁:Box n → Config G n → Poly J)
def source (z:ℂ) (U:Config G n):Poly J:=
  restore P (fun (_:V) _=>0) (fun (_:V) _ _=>0)
    (fun Z U=>H₀ Z U+z • H₁ Z U) (fun b U=>K₀ b U+z • K₁ b U) U

theorem original (zeroH:∀Z U,(H₁ Z U).part J.quiet=0)(zeroK:∀b U,(K₁ b U).part J.quiet=0)
    (U:Config G n):Rendered (fun z=>source P H₀ H₁ K₀ K₁ z U):=by
  let marked (b:Box n)(z:ℂ):=bar P.activities J U b + Mach J (fun _=>0) + (K₀ b U+z • K₁ b U)
  have core(b:Box n):Rendered (marked b):=plus (constant _) (plus (constant _) (affine_zero _ (zeroK b U)))
  have box(l:Finset (Box n)):Rendered (fun z=>grid (fun b=>marked b z) (flags P.p.threshold U) l):=by
    by_cases h:Pattern (flags P.p.threshold U) l
    · simpa only [grid,if_pos h] using finite l marked core
    · simpa only [grid,if_neg h] using (constant (0:Poly J))
  have gas:=sum univ box
  have exp:=exponential (plus (constant (Mach J (fun _=>0)))
      (sum univ (fun Z=>plus (constant (H₀ Z U)) (affine_zero _ (zeroH Z U)))))
  exact multiplier (product exp gas) _

theorem taps (zeroH:∀Z U,(H₁ Z U).part J.quiet=0)(zeroK:∀b U,(K₁ b U).part J.quiet=0)
    (s:J.Mode) (n:ℕ)(size:s.val.card≤n)(T q:ℂ)(inv:T*q=1)(U):
    (source P H₀ H₁ K₀ K₁ 1 U).part s-(source P H₀ H₁ K₀ K₁ 0 U).part s=
      ∑j:Fin (n+1),WilsonOriginalOccupiedStencil.weight q j*
        (source P H₀ H₁ K₀ K₁ (T*WilsonOriginalOccupiedStencil.node j) U).part s := by
  obtain ⟨pol,degree,eq⟩:=original P H₀ H₁ K₀ K₁ zeroH zeroK U s
  simpa only [eq] using WilsonOriginalOccupiedStencil.original pol (degree.trans size) T q inv

end YM.Integration.WilsonSeparatedPrefixCanonicalPolynomial
end
