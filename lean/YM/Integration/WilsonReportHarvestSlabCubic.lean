import YM.Integration.WilsonReportHarvestSlabShiftLabels
import YM.MergeProof.South.Loft

/-! On the same three-mark Wilson board the difference of two fields with
matching vacuum and singletons is affine in all three centering constants. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCubic
open Function Finset MeasureTheory Lattice RG Source Marker RG05Readout RG05Readout.Many
open Wilson Labels Address MergeProof Accent Menu Ribbons Ribbons.ManyCopies
open scoped Classical BigOperators
set_option quotPrecheck false
local notation "S" => Stock.census (Fin 3)
local notation "C₁" => Stock.census (Unit×Fin 3)
local notation "Z" => Stock.census (Unit×Unit)

open WilsonReportHarvestSlabLabels

open WilsonReportHarvestSlabShiftLabels Push.GridApprox.Birth Extra.Trajectories

private def bucket (l:Finset (Fin 3)):(Stock.census (Fin 3)).Mode:=⟨l,Finset.mem_univ _⟩

private theorem formula (A:Poly S)(v:Fin 3→ℂ):
    (translated v A).part entire=∑l∈(Finset.univ:Finset (Fin 3)).powerset,
      A.part (bucket (Finset.univ\l))*∏i∈l,v i := by
  have showPass:Poly.pass (Mach S v)=∏i,(1+Poly.send ((S).fire i) (v i)):=by
    unfold Mach
    rw [pass_sum]
    intro i _
    exact singleton_nonempty _
  unfold translated
  rw [showPass,mul_comm]
  exact array_read A Finset.univ v

private theorem short (A:Poly S) (q:A.part (S).quiet=0) (s:∀i,A.part ((S).fire i)=0)
    (v:Fin 3→ℂ):
    (translated v A).part entire=A.part entire+
      ∑i:Fin 3,A.part (bucket (Finset.univ\{i}))*v i := by
  let e:Fin 3↪Finset (Fin 3):=⟨fun i=>{i},fun _ _ h=>Finset.singleton_injective h⟩
  let small:=insert (∅:Finset (Fin 3)) (Finset.univ.map e)
  let term (l:Finset (Fin 3)):=A.part (bucket (Finset.univ\l))*∏i∈l,v i
  have sub:small⊆(Finset.univ:Finset (Fin 3)).powerset:=fun _ _=>Finset.mem_powerset.mpr (Finset.subset_univ _)
  have none:∅∉Finset.univ.map e:=by
    intro stop
    obtain ⟨i,_,eq⟩:=Finset.mem_map.mp stop
    exact Finset.singleton_ne_empty i eq
  have kill (l:Finset (Fin 3)) (_hl:l∈(Finset.univ:Finset (Fin 3)).powerset) (old:l∉small):term l=0:=by
    have non:l.Nonempty:=Finset.nonempty_iff_ne_empty.mpr fun h=>old (h ▸ Finset.mem_insert_self ..)
    have rank:2≤l.card:=by
      by_contra! shifted
      have card:l.card=1:=by have hp:=non.card_pos;omega
      obtain ⟨i,rfl⟩:=Finset.card_eq_one.mp card
      exact old (Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have left:((Finset.univ:Finset (Fin 3))\l).card≤1:=by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
      omega
    have passive:A.part (bucket (Finset.univ\l))=0:=by
      rcases Finset.eq_empty_or_nonempty (Finset.univ\l) with h|h
      · rw [h];exact q
      · have card:((Finset.univ:Finset (Fin 3))\l).card=1:=by have pos:=h.card_pos;omega
        obtain ⟨i,hi⟩:=Finset.card_eq_one.mp card
        rw [hi];exact s i
    exact mul_eq_zero_of_left passive _
  rw [formula,←Finset.sum_subset sub kill]
  change (∑l∈insert ∅ (Finset.univ.map e),term l)=_
  rw [Finset.sum_insert none,Finset.sum_map]
  simp only [term,Finset.sdiff_empty,Finset.prod_empty,mul_one,Function.Embedding.coeFn_mk,Finset.prod_singleton,e]
  rfl

theorem raised (A:Poly S) (quiet:A.part (S).quiet=0) (single:∀i,A.part ((S).fire i)=0)
    (v:Fin 3→ℂ):
    (translated v A).part entire=(translated 0 A).part entire+
      ∑i:Fin 3,v i*((translated (Pi.single i 1) A).part entire-(translated 0 A).part entire) := by
  have line:=short A quiet single
  have zero:(translated 0 A).part entire=A.part entire:=by simp only [line,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]
  have leg(i:Fin 3):(translated (Pi.single i 1) A).part entire-(translated 0 A).part entire=
      A.part (bucket (Finset.univ\{i})):=by
    rw [line,zero,Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same,mul_one,add_sub_cancel_left]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj,mul_zero]
    · simp
  simp_rw [leg]
  rw [line v,zero]
  exact congrArg (A.part entire+·) (Finset.sum_congr rfl fun _ _=>mul_comm ..)

end YM.Integration.WilsonReportHarvestSlabCubic
