import YM.Integration.WilsonMeasuredPublicCopies
import YM.Integration.WilsonMeasuredPublicCellGroup

/-! All reflected copies of the actual public source product and additional billed local probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicRough
open Function Filter Set Cells Lattice Wilson RG Spec Table Extraction OPE Cards
open PhysicalNext.Repeat.Legato WilsonMeasuredPublicSlots WilsonMeasuredPublicCopies
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  {F : Final R.family f S} {l : Ultrafilter (ℕ×ℕ)} {I : Type} [Fintype I]
  {d : I → ℕ} {v : ∀ i,S.Field (d i)} {s B : I → ℝ}
  (L : ∀i,Slot F l (d i) (v i) (s i) (B i))
local notation "wage" => amount (F:=F) (B:=B) (s:=s) (v:=v)

/-- Both lanes are in the same Wilson measure. Each rough probe must carry its own card. -/
def Offers (q : ℕ×ℕ) : Prop :=
  ∀ (E : Type) [Fintype E] (k : E → ℕ) (w : E → ℝ) (P : E → Config G (R.family.side q.1 q.2) → ℂ),
  (∀e,Cards.PaidAt R.family.S q.1 q.2 (k e) (R.family.beta q.1 q.2) (w e) (P e)) →
  ∀ (u : I⊕E → Site (R.family.side q.1 q.2)) (W₀ W : Tiling (R.family.side q.1 q.2)) (c : W.Cell),
  W₀.kind=.link → W.kind=.link → W₀.base=W.base → W₀.side.val ∣ W.side.val →
  ∀ live : ∀a,(Sum.elim (fun i=>(L i).m) k) a ≤ q.1,
  (∀a,Cells.span R.family.S (live a) q.2 ∣ W₀.side.val) → (∀a,W.which (u a)=c) →
  (∀a,Next.Phase.Inside W₀ (3*Cells.span R.family.S (live a) q.2) (u a)) →
  (∀ a b,a≠b → W₀.side.val < separation (u a) (u b)) →
  ∃ Y : Config G (R.family.side q.1 q.2) → ℂ,
    W.copy c Y=(fun U=>(∏ i,field L q i (u (.inl i)) U)*(∏ e,P e (translate (u (.inr e)) U))) ∧
    Interior (W.chamber 0) Y ∧ W.rootTest (R.family.beta q.1 q.2) Y ≤ (∏ i,wage i)*(∏ e,w e) ∧
    ‖moment (R.family.beta q.1 q.2) (W.fullAt (fun _=>Y))‖ ≤ ((∏ i,wage i)*(∏ e,w e))^Fintype.card W.Cell

theorem original : ∀ᶠ q : ℕ×ℕ in f.fuse, Offers L q := by
  filter_upwards [eventually_all.mpr fun i=>(L i).reflected] with q h
  intro E _ k w P marked u W₀ W c hw he base nested live divide chamber inside separated
  let A : I⊕E → ℝ := Sum.elim wage w
  let funcs : I⊕E → Config G (R.family.side q.1 q.2) → ℂ :=
    Sum.elim (fun i=>R.family.O q.1 q.2 ((L i).arm.source q) 0) P
  have bought (a:I⊕E) : Cards.PaidAt R.family.S q.1 q.2 (Sum.elim (fun i=>(L i).m) k a)
      (R.family.beta q.1 q.2) (A a) (funcs a) := by
    cases a with
    | inl i => exact h i
    | inr e => exact marked e
  obtain ⟨Y,ident,held,price⟩ := WilsonMeasuredPublicCellGroup.exterior hw he base nested u funcs A c
    bought divide chamber inside separated (Cells.seamless F.room.cutoff q.1 q.2)
  have fits : ∏ a,A a=(∏ i,wage i)*(∏ e,w e) := by rw [Fintype.prod_sum_type]; rfl
  rw [fits] at price
  refine ⟨Y,?_,held,price,?_⟩
  · rw [ident]
    funext U
    rw [Fintype.prod_sum_type]
    congr 1
    exact Finset.prod_congr rfl fun i _=>by
      change R.family.O q.1 q.2 ((L i).arm.source q) 0 (translate (u (.inl i)) U)=_
      rw [at_site L,(L i).actual]
      rfl
  · change W.rootPower (R.family.beta q.1 q.2) (fun _=>Y) ≤ _
    rw [← W.powering]
    exact pow_le_pow_left₀ (W.root_nonneg ..) price _

end YM.Integration.WilsonMeasuredPublicRough
