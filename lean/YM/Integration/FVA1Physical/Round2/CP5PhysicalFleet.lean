import YM.Integration.FVA1Physical.Round2.CP5NativeRow
import YM.Integration.FVA1Physical.Round2.CP5StencilPassport
import YM.Integration.FVA1Physical.Round2.CP5FieldAtoms
import YM.QuadraticLocal.Germ.Annual

/-! A unit-priced CP5 analytic input for all calibrated fields, with
independent real-linear tested amplitudes. The price and ranks precede the
period and positions; the exact original field sum is retained on all links.
The exported kernel is the kernel of the actual chosen test functional. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Function Finset Lattice YM.Wilson RG Source Labels Marker QuadraticLocal.Earn QuadraticLocal.Affinity Push.AbsoluteSums
open Next.Foundations YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {d:ℕ}
variable {E:I→Type} [∀ i,AddCommGroup (E i)] [∀ i,Module ℝ (E i)]

omit [Fintype I] in
theorem fleet_enlarge {n:Side} {α Z:Type} {R:Census I} {P:Passport n I}
    {X:Z→Row P R G α} {w:I→ℝ} {η:I→ℕ} {σ:ℝ}
    {p r h p' r' h':ℕ} (funds:Scene.Armada X w η σ 1 p r h)
    (order:p≤p') (load:r≤r') (names:h≤h') : Scene.Armada X w η σ 1 p' r' h' :=
  ⟨⟨fun s=>(funds.quota s).trans load,fun s=>(funds.crew s).trans names⟩,
    funds.positive,funds.suggests,⟨funds.purchases.spend,
    fun x=>⟨((funds.purchases.usable x).1).trans order,(funds.purchases.usable x).2⟩⟩,
    funds.honor⟩

def fieldCount (a:CoverLabel G d) : ℕ := (physical_field_atoms (G:=G) a.1.val a.2).choose
def fieldAtlas (a:CoverLabel G d) : Fin (fieldCount a) → FieldAtom G :=
  (physical_field_atoms (G:=G) a.1.val a.2).choose_spec.choose
def fieldHorizon (a:I → CoverLabel G d) : ℕ := ∑ i,∑ j,(fieldAtlas (a i) j).rank

omit [Fintype I] in
private theorem coordinate_attn (test:∀ i,E i→ₗ[ℝ]ℂ) (A:∀ i,Set (E i)) (i:I) :
    Attn (fun j=>(test j).ker) A {i} (fun t=>test i (t i).val) := by
  refine ⟨fun s t h=>congrArg (fun x:A i => test i x.val) (h i (mem_singleton_self i)),?_,?_⟩
  · intro j hj t x y z a b h
    obtain rfl : j=i := mem_singleton.mp hj
    simp only [Function.update_self,h,map_add,map_smul]
  · intro j hj t h
    obtain rfl : j=i := mem_singleton.mp hj
    exact h

theorem physical_analytic_fleet (R:Census I) (a:I → CoverLabel G d) (σ:ℝ)
    (test:∀ i,E i→ₗ[ℝ]ℂ) (A:∀ i,Set (E i)) (bounded:∀ i x,x∈A i→‖test i x‖≤1) :
    ∃ w:ℝ, 0<w ∧
      ∀ (n:Side) (o:I→Site n), ∃ X:(Σ i,Fin (fieldCount (a i)))→Row (stencilPassport a o) R G (Wallet A),
      Scene.Armada X (fun _=>w) (fun _=>1) σ 1 (fieldHorizon a) (Fintype.card I) (Fintype.card I) ∧
      Tableau (fun i=>(test i).ker) A X ∧
      (∀ i t g (U:Config G n),(test i (t i).val)*(localSection G (a i).1.val).places (Pi.single (a i).2 1) (o i) U =
        ∑ j:Fin (fieldCount (a i)),(X ⟨i,j⟩).nominal g t U) ∧
      (∀ p, (X p).mode=R.fire p.1 ∧ (((frames G).level (a p.1).1.val).grades (a p.1).2).2 ≤ (X p).lamp.r ∧
        (X p).lamp.e=(X p).lamp.r) := by
  let count (i:I) := fieldCount (a i)
  let atoms (i:I) := fieldAtlas (a i)
  have law (i:I) := (physical_field_atoms (G:=G) (a i).1.val (a i).2).choose_spec.choose_spec
  let fee (i:I) (j:Fin (count i)) := (1+‖(atoms i j).factor‖*reserve (atoms i j).atom σ)*
    Real.exp (σ*((stencilHeight (a i)+(atoms i j).atom.length:ℕ):ℝ))
  have positive (i:I) (j:Fin (count i)) : 0≤fee i j := by
    unfold fee
    exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg (norm_nonneg _) (reserve_pos _ _).le)) (Real.exp_pos _).le
  let total := ∑ p:(Σ i,Fin (count i)),fee p.1 p.2
  have ht : 0 < 1+total := by have : 0≤total := sum_nonneg fun _ _=>positive ..; linarith
  let w := (1+total)⁻¹
  have hw:0<w := inv_pos.mpr ht
  refine ⟨w,hw,?_⟩
  intro n o
  let P := stencilPassport a o
  let amp (i:I) (y:Wallet A) := test i (y i).val
  let X (p:Σ i,Fin (count i)) := unitRow P R p.1 (atoms p.1 p.2).atom (atoms p.1 p.2).invariant
    σ (atoms p.1 p.2).factor (amp p.1)
  have admitted (p:Σ i,Fin (count i)) := unitRow_eligible P R p.1 (atoms p.1 p.2).atom (atoms p.1 p.2).invariant
    σ (atoms p.1 p.2).factor (amp p.1) (fun y=>bounded _ _ (y _).property)
  have height (p:Σ i,Fin (count i)) : (X p).height σ=fee p.1 p.2 := by
    unfold Row.height
    rw [(admitted p).2.2.2]
    rfl
  have solo (p:Σ i,Fin (count i)) : (X p).mode=R.fire p.1 := rfl
  refine ⟨X,?_,?_,?_,fun p=>⟨solo p,(law p.1).1 p.2,rfl⟩⟩
  · refine ⟨⟨fun p=>Finset.card_le_univ p.val,fun p=>by simpa using Finset.card_le_univ p.val⟩,
       fun _=>hw,?_,⟨fun p=>(admitted p).1,?_⟩,fun p=>(admitted p).2.2.1⟩
    · intro x
      have charge (p:Σ i,Fin (count i)) : Poly.toll (fun _=>w) (X p).mode*(X p).height σ=w*fee p.1 p.2 := by
        rw [solo,height]
        simp [Poly.toll,Census.fire]
      apply budget_finite
      · intro p; split <;> first | simpa only [charge] using mul_nonneg hw.le (positive p.1 p.2) | exact le_rfl
      calc
        _ ≤ ∑ p:(Σ i,Fin (count i)),w*fee p.1 p.2 := sum_le_sum fun p _=>by
          split <;> first | exact (charge p).le | exact mul_nonneg hw.le (positive p.1 p.2)
        _ = w*total := (mul_sum ..).symm
        _ ≤ 1 := by change (1+total)⁻¹*total≤1; rw [mul_comm,←div_eq_mul_inv,div_le_one ht]; linarith
    · intro p
      refine ⟨?_,(admitted p).2.1.2⟩
      exact (single_le_sum (s:=univ) (fun j _=>Nat.zero_le (atoms p.1 j).rank) (mem_univ p.2)).trans
        (single_le_sum (s:=univ) (fun i _=>Nat.zero_le (∑ j,(atoms i j).rank)) (mem_univ p.1))
  · refine ⟨fun p=>?_⟩
    exact (coordinate_attn test A p.1).cs ((atoms p.1 p.2).factor*(reserve (atoms p.1 p.2).atom σ:ℂ))
  · intro i t g U
    rw [(law i).2.2 n (o i) U,Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    rw [unitRow_read]
    change amp i t * ((atoms i j).factor * ((atoms i j).atom.unmasked U (o i):ℂ)) =
      (atoms i j).factor * amp i t * ((atoms i j).atom.unmasked U (o i):ℂ)
    ring

end YM.Integration.FVA1Physical.Round2.CP5
