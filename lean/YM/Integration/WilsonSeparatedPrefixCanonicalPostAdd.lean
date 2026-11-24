import YM.Integration.WilsonSeparatedPrefixCanonicalCarton
import YM.Integration.WilsonOriginalGalleryTwinBoard

/-! Adding two transactions at the same original barcode, before the
compatible gas is formed. Either transaction can own the same failed key. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalPostAdd
open Finset Function MeasureTheory Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal
open MergeProof MergeProof.Accent Extra.Histories Lodestar
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {J:Census V} {o:V → Site n} {t:ℝ}

private theorem any_add {A:Type} [AddMonoid A] {a b:A} {C:Prop} (f:a≠0 → C) (g:b≠0 → C)
    (h:a+b≠0) : C := by
  by_cases pa:a=0
  · exact g (fun pb=>h (by rw [pa,pb,zero_add]))
  exact f pa

private theorem borne {S:Support n}{f g:Config G n → Poly J}
    (a:Borne o S f t) (b:Borne o S g t):Borne o S (fun U=>f U+g U) t := by
  refine ⟨fun U D h kt=>congrArg₂ (·+·) (a.home U D h kt) (b.home U D h kt),
    fun h U=>congrArg₂ (·+·) (a.turns h U) (b.turns h U),?_,?_⟩
  · intro i
    exact (a.me i).add (b.me i)
  · intro U i h
    rw [Poly.part_plus,a.scope U i h,b.scope U i h,zero_add]

private theorem rise {x y:Poly J}(a:rises x)(b:rises y) : rises (x+y) := by
  intro i h
  exact any_add (a i) (b i) h

theorem cartons {H H':Support n → Config G n → Poly J} {K K':Box n → Config G n → Poly J}
    (one:Carton o H K t) (other:Carton o H' K' t) :
    Carton o (fun S U=>H S U+H' S U) (fun k U=>K k U+K' k U) t := by
  constructor
  · intro S
    rcases one.exp S with ⟨a,r⟩
    rcases other.exp S with ⟨b,s⟩
    refine ⟨⟨borne a.toBorne b.toBorne,fun U=>any_add (a.permits U) (b.permits U),?_⟩,fun U=>rise (r U) (s U)⟩
    intro U
    rw [Poly.part_plus,a.sil U,b.sil U,zero_add]
  · intro k
    rcases one.flag k with ⟨a,r⟩
    rcases other.flag k with ⟨b,s⟩
    exact ⟨⟨borne a.toBorne b.toBorne,fun U=>any_add (a.permits U) (b.permits U)⟩,fun U=>rise (r U) (s U)⟩

theorem twin [Fintype V] {H:Support n → Config G n → Poly (Marks V)} {K:Box n → Config G n → Poly (Marks V)}
    (paid:Carton o H K t):
    Carton (o ∘ Prod.fst) (fun Z=>duplicate V ∘ H Z) (fun b=>duplicate V ∘ K b) t := by
  refine ⟨fun Z=>burns_duplicate (paid.exp Z).1,fun b=>⟨flow_duplicate (paid.flag b).1,fun U=>large_duplicate ?_⟩⟩
  by_contra h
  have size := (paid.flag b).2 U (Marks V).quiet h
  simp [Marker.Census.quiet] at size

end YM.Integration.WilsonSeparatedPrefixCanonicalPostAdd
end
