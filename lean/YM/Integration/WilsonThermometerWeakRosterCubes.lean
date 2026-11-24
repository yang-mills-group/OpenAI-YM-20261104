import YM.Integration.WilsonThermometerWeakSeparatedStops
import YM.Frontier6.Pair.Packing
import YM.Integration.WilsonThermometerWeakMixedCells

/-! The two weak reflected cells can share a genuine fine-lattice translation
before either regulator. Rounding uses the extra original block date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakRosterCubes
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

private theorem location (S:Schedule) (N p:ℕ) (a:Cover) :
    Cells.location S N N p a=wrap (S.side N p) a:=by
  unfold Cells.location
  rw [dif_pos le_rfl]
  unfold Ratio.embed Schedule.toDepth
  simp only [tsub_self,Schedule.steps]
  rw [show ((1:Side).val:ℕ)=1 from rfl,one_smul,wrap_lift]


theorem original (S:Schedule) (I:Type) [Fintype I] : ∃e:ℕ,∀(j m N p:ℕ)(mn:m≤N)(start:j+e+1 ≤ m)
    (r:I→ℕ)(_deep:∀i,j+e+1≤r i)(paid:∀i,r i≤N)(x:I → Cover),
    (∀i i',i≠i'→∃l:Axis,S.a j≤|S.gridPoint N (x i) l-S.gridPoint N (x i') l|) →
    (∀i i' (l:Axis),2*(|S.gridPoint N (x i) l-S.gridPoint N (x i') l|+S.a j)<(S.side j p).val*S.a j) →
    let T:=center S p (by omega:j≤N) 0
    ∃(a:Site (S.side m p))(v:I→Site (S.side j p)),Injective v ∧
      ∀i,wrap (S.side N p) (x i)+(S.toDepth mn p).embed a∈T.margin (v i) (3*span S (paid i) p):=by
  classical
  let E:=Fintype.equivFin I
  obtain ⟨e,fit⟩:=fit_chart S (Fintype.card I)
  refine ⟨e,?_⟩
  intro j m N p mn start r deep paid x gap period T
  have jm:j ≤ m:=by omega
  let D:=S.toDepth mn p
  obtain ⟨t,u,clear⟩:=fit j (points (fun i=>S.gridPoint N (x (E.symm i))))
  obtain ⟨a,rounding⟩:=rounded S m t
  let g:Cover:=D.count.val • a
  have lifted (l:Axis):S.gridPoint N g l=S.gridPoint m a l:=by
    have scale:S.a N*D.count.val=S.a m:=S.embeds_scale D
    change S.a N*(((D.count.val • a) l:ℤ):ℝ)=S.a m*(a l:ℝ)
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←mul_assoc,scale]
  let v (i:I):Cover:=u (E i)
  have stops (i:I):atStop S j (v i) (3*S.a (r i)) (S.gridPoint N (x i+g)):=by
    intro l
    have old:=clear (E i) l
    change |S.gridPoint N (x (E.symm (E i))) l+t l-S.gridPoint j (v i) l|<_ at old
    rw [E.symm_apply_apply] at old
    have plus:S.gridPoint N (x i+g) l=S.gridPoint N (x i) l+S.gridPoint N g l:=by
      change S.a N*((x i l+g l:ℤ):ℝ)=_;rw [Int.cast_add,mul_add];rfl
    have eq:S.gridPoint N (x i+g) l-S.gridPoint j (v i) l=
      (S.gridPoint N (x i) l+t l-S.gridPoint j (v i) l)+(S.gridPoint m a l-t l):=by rw [plus,lifted];ring
    rw [eq]
    apply (abs_add_le ..).trans_lt
    have hm:=S.strictAnti.antitone start
    have hr:=S.strictAnti.antitone (deep i)
    have decay:=three S (j+e)
    linarith only [old,rounding l,hm,hr,decay,S.a_pos (j+e)]
  refine ⟨wrap _ a,fun i=>wrap _ (v i),?_,?_⟩
  · intro i i' equal
    by_contra differs
    let P:Fin 2→I:=![i,i']
    have disjoint:=WilsonThermometerWeakSeparatedStops.separated S j N p (r ∘ P) (x ∘ P) (v ∘ P) g
      (fun i=>stops (P i)) (gap i i' differs) (period i i')
    exact disjoint equal
  · intro i
    have entered:=at_margin S p (v i) (x i+g) (jm.trans mn) le_rfl (paid i) (stops i)
    rw [location] at entered
    rw [D.embed_wrap a]
    simpa only [g,map_add] using entered

end YM.Integration.WilsonThermometerWeakRosterCubes
end
