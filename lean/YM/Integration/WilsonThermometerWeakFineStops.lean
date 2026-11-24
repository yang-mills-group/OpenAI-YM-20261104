import YM.Frontier6.Pair.Packing
import YM.Integration.WilsonThermometerWeakMixedCells

/-! The two weak reflected cells can share a genuine fine-lattice translation
before either regulator. Rounding uses the extra original block date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFineStops
open Function Filter Set Lattice Cells Frontier6.Platform
open scoped Topology Classical BigOperators

private theorem rounded (S:Schedule) (N:ℕ) (t:E4) :
    ∃a:Cover,∀ j:Axis, |S.gridPoint N a j-t j|≤S.a N:=by
  let a:Cover:=fun j=>⌊t j/S.a N⌋
  refine ⟨a,fun j=>?_⟩
  have low:=Int.floor_le (t j/S.a N)
  have upper:=Int.lt_floor_add_one (t j/S.a N)
  have h₀: (a j:ℝ)*S.a N≤t j:=(le_div_iff₀ (S.a_pos N)).mp low
  have h₁: t j<((a j:ℝ)+1)*S.a N:=(div_lt_iff₀ (S.a_pos N)).mp upper
  change |S.a N*(a j:ℝ)-t j|≤S.a N
  rw [abs_of_nonpos (by linarith only [h₀])]
  linarith only [h₁]

private theorem three (S:Schedule) (j:ℕ):3*S.a (j+1)≤S.a j:=by
  have h:(3:ℝ)≤(S.block j).val:=by exact_mod_cast S.block_large j
  rw [S.a_step,mul_div_assoc']
  exact (div_le_iff₀ (by positivity [((S.block j).property)])).mpr (by nlinarith [S.a_pos j])

theorem original (S:Schedule) : ∃e:ℕ,∀ (m N p:ℕ) (r:Fin 2→ℕ)
    (gap:∀i,m+e+1≤r i) (live:∀i,r i≤N) (x:Fin 2 → Cover),
    let T:=center S p (by have h:=gap 0;have h':=live 0;omega : m≤N) 0
    ∃ (a:Cover) (u:Fin 2 → Cover),
      (∀i,atStop S m (u i) (3*S.a (r i)) (S.gridPoint N (x i+a))) ∧
      ∀i,Cells.location S N N p (x i+a)∈T.margin (wrap (S.side m p) (u i)) (3*Cells.span S (live i) p):=by
  obtain ⟨e,fit⟩:=fit_chart S 2
  refine ⟨e,?_⟩
  intro m N p r gap live x T
  obtain ⟨t,u,clear⟩:=fit m (points (fun i=>S.gridPoint N (x i)))
  obtain ⟨a,rounding⟩:=rounded S N t
  have stops (i:Fin 2):atStop S m (u i) (3*S.a (r i)) (S.gridPoint N (x i+a)):=by
    intro j
    have old:=clear i j
    change |S.gridPoint N (x i) j+t j-S.gridPoint m (u i) j|<_ at old
    have plus:S.gridPoint N (x i+a) j=S.gridPoint N (x i) j+S.gridPoint N a j:=by
      change S.a N*((x i j+a j:ℤ):ℝ)=_;rw [Int.cast_add,mul_add];rfl
    have eq:S.gridPoint N (x i+a) j-S.gridPoint m (u i) j=
        (S.gridPoint N (x i) j+t j-S.gridPoint m (u i) j)+(S.gridPoint N a j-t j):=by rw [plus];ring
    rw [eq]
    apply (abs_add_le ..).trans_lt
    have hN:=S.strictAnti.antitone (live i)
    have hr:=S.strictAnti.antitone (gap i)
    have h:=three S (m+e)
    linarith only [old,rounding j,hN,hr,h,S.a_pos (m+e)]
  refine ⟨a,u,stops,fun i=>?_⟩
  exact at_margin S p (u i) (x i+a) (by have h:=gap i;have h':=live i;omega) le_rfl (live i) (stops i)

end YM.Integration.WilsonThermometerWeakFineStops
end
