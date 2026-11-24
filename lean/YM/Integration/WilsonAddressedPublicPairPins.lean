import YM.Integration.WilsonAddressedPublicPairFilm
import YM.Integration.WilsonAddressedPublicPairGeometry
import YM.Integration.WilsonOriginalPublicRelativeGramPins

/-! The original reflected matrix on the two genuine reporting grids. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.Integration.WilsonAddressedPublicPairPins
open Function Filter Finset Lattice RG Wilson Source Labels Cells OPE Extraction Spec
open Table PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee width)
open WilsonAddressedPublicOpticalPair (length)
open WilsonOriginalPublicRelativeGramPins (cutoff)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Bool→ℝ}(B:∀t,Book F (l:=l) H z D T (r t))
    {I:Type}(d:Fin (D+1))(v:Bool→I→S.Field d.val)(b:Bool→I→Bool)
local notation "C" => R.family
local notation "A" => R.family.path.levels

def name (t:Bool)(w:ℕ×ℕ)(i:I): (C).label d.val:=
  (((B t).rows d).arm (b t i) (v t i)).source w

def whenFiled (t:Bool)(i:I):ℕ:=width F (B t) d (v t i) (b t i)
def size (t:Bool)(i:I):ℝ:=length F (B t) (b t i)
def cost (t:Bool)(i:I):ℝ:=fee F (B t) d (v t i) (b t i)

variable [Fintype I]
theorem original (cash:Trace.Terrace.PostT (A))(simple:G.Simple)(house:∀t,Housed F (B t)):
    ∀ᶠ k:ℕ in atTop,∀t:Bool,∀i j:I,
    let w₀:=whenFiled R F B d v b false i
    let w₁:=whenFiled R F B d v b t j
    let wall:=max (size R F B b false i) (size R F B b t j)
    w₀ ≤ k → w₁ ≤ k → 0 < min w₀ w₁ → ∀site:ℕ,∀(L:Type)[Fintype L]
      (x:L→Fin 2→ Cover)(μ:L→ℂ),
    (∀t,‖(C).S.gridPoint site (x t 0-x t 1)‖ ≤ 1) →
    (∀t,2*(A).clock.monitor k*wall < ‖(C).S.gridPoint site (x t 0)-(C).S.gridPoint site (x t 1)‖) →
    ∀ᶠ w:ℕ×ℕ in f.fuse,∀a:Axis,‖cutoff R a (fun _:I=>d.val) site x μ
      (name R F B d v b) t w i j‖ ≤ (∑t,‖μ t‖)*(cost R F B d v b false i*cost R F B d v b t j):=by
  classical
  refine eventually_all.mpr (fun t=>eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>?_)))
  let which:Fin 2→Bool:=Fin.cons false (fun _=>t)
  let books:=fun h:Fin 2=>B (which h)
  let vec:Fin 2→S.Field d.val:=Fin.cons (v false i) (fun _=>v t j)
  let branch:Fin 2→Bool:=Fin.cons (b false i) (fun _=>b t j)
  obtain ⟨J,register⟩:=WilsonAddressedPublicPairFilm.original R F books (fun _=>d) vec branch
    cash simple (fun h=>house (which h))
  filter_upwards [eventually_ge_atTop J] with k late
  intro k₀ k₁ wall paid₀ paid₁ pos site L _ x μ compact apart
  have reach:∀ᶠ w:ℕ×ℕ in f.fuse,site ≤ w.1:=by
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop site
  have floor:∀h:Fin 2,width F (books h) d (vec h) (branch h) ≤ k:=by
    intro h
    fin_cases h
    · exact paid₀
    · exact paid₁
  filter_upwards [register k late floor pos,reach] with w received mature
  intro a
  let o:=fun h q=>Cells.location (C).S site w.1 w.2 (x h q)
  have inside(h:L):(A).clock.monitor k*wall < (C).S.a w.1*(separation (o h 0) (o h 1):ℝ):=by
    have dist:=WilsonAddressedPublicPairGeometry.gap (C) (p:=w.2) mature (x h 0) (x h 1) (compact h)
    have far:=(apart h).trans_le dist
    dsimp only [o]
    linarith only [far]
  have spaced:∀i i':Fin 2,∀h:L,i≠i' → (A).clock.monitor k*wall <
      (C).S.a w.1*(separation (o h i) (o h i'):ℝ):=by
    intro h₀ h₁ s ne
    fin_cases h₀ <;> fin_cases h₁
    · exact (ne rfl).elim
    · exact inside s
    · rw [separation_comm];exact inside s
    · exact (ne rfl).elim
  have measured:=received a L o μ spaced
  rw [Fin.prod_univ_two] at measured
  exact measured

end YM.Integration.WilsonAddressedPublicPairPins
end
