import YangMills.WilsonProof.NativeSupport.JointProjection

/-! Replant each incoming native sheet with precisely one active owner
per nonempty monomial. The inflated input earns only one old multiplier,
regardless of how many dated blocking bonds that monomial contains. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Painted
open Finset Marker Packet
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def wear (S : Finset V) : Finset (Ink V) :=
  if h:S.Nonempty then S.map (paint h.choose true false) else ∅

omit [Fintype V] in
theorem wear_image (S : Finset V) : (wear S).image Prod.fst=S := by
  by_cases h : S.Nonempty
  · rw [wear,dif_pos h]
    ext i
    constructor
    · intro hi
      obtain ⟨p,hp,rfl⟩:=mem_image.mp hi
      obtain ⟨v,hv,rfl⟩:=mem_map.mp hp
      exact hv
    · intro hi
      exact mem_image.mpr ⟨_,mem_map_of_mem _ hi,rfl⟩
  · rw [wear,dif_neg h,Finset.image_empty,Finset.not_nonempty_iff_eq_empty.mp h]

omit [Fintype V] in
theorem wear_kept (S : Finset V) : faithful (wear S) := by
  by_cases h : S.Nonempty
  · intro u hu v hv same
    rw [wear,dif_pos h] at hu hv
    obtain ⟨a,_,rfl⟩:=mem_map.mp hu
    obtain ⟨b,_,rfl⟩:=mem_map.mp hv
    exact congrArg (paint h.choose true false) (show a=b from same)
  · rw [wear,dif_neg h]
    simp [faithful]

omit [Fintype V] in
theorem wear_active (S : Finset V) (h : S.Nonempty) :
    ((wear S).filter (fun i=>i.2.1)).card=1 := by
  let q := paint h.choose true false
  have on (v:V) : (q v).2.1=true ↔ v=h.choose := by
    dsimp [q,paint]; split <;> simp_all
  have only : (wear S).filter (fun i=>i.2.1)={q h.choose} := by
    rw [wear,dif_pos h]
    ext x
    constructor
    · intro hit
      obtain ⟨u,_,rfl⟩:=mem_map.mp (mem_filter.mp hit).1
      exact mem_singleton.mpr (congrArg q ((on u).mp (mem_filter.mp hit).2))
    · intro hit
      rw [mem_singleton.mp hit]
      exact mem_filter.mpr ⟨mem_map_of_mem _ h.choose_spec,(on _).mpr rfl⟩
  rw [only,card_singleton]

theorem wear_toll (w : V → ℝ) (A D : ℝ) (fresh : Finset V) (S : Finset V)
    (h : S.Nonempty) (old : Disjoint S fresh) :
    Poly.toll (weight w A D fresh) (tag (wear S))=A*Poly.toll w (tag S) := by
  let q := paint h.choose true false
  change (∏ i∈wear S,weight w A D fresh i)=_
  rw [wear,dif_pos h,prod_map]
  have price (v:V) (hv:v∈S) : weight w A D fresh (q v)=w v*(if v=h.choose then A else 1) := by
    have free : v∉fresh := fun bad=>disjoint_left.mp old hv bad
    have chooseFree : h.choose∉fresh := fun bad=>disjoint_left.mp old h.choose_spec bad
    by_cases atRoot : v=h.choose <;> simp [q,weight,paint,free,chooseFree,atRoot]
  calc _ = ∏ v∈S,w v*(if v=h.choose then A else 1) := prod_congr rfl price
       _ = _ := by rw [prod_mul_distrib,prod_ite_eq',if_pos h.choose_spec]; exact mul_comm _ _

def repaint (P : Poly (YM.Stock.census V)) : Poly (YM.Stock.census (Ink V)) :=
  ∑ S : Finset V,Poly.send (tag (wear S)) (P.part (tag S))

theorem repaint_part (P : Poly (YM.Stock.census V)) (D : Finset (Ink V)) :
    (repaint P).part (tag D)=
      if D=wear (D.image Prod.fst) then P.part (tag (D.image Prod.fst)) else 0 := by
  rw [repaint,Poly.part_sum]
  by_cases same : D=wear (D.image Prod.fst)
  · rw [if_pos same,sum_eq_single (D.image Prod.fst)]
    · rw [Poly.part_send,if_pos (congrArg tag same)]
    · intro S _ other
      rw [Poly.part_send,if_neg (fun eq=>other (by
        have he:= congrArg (fun t=>t.val.image Prod.fst) eq
        simpa only [wear_image] using he.symm))]
    · simp
  · rw [if_neg same]
    apply sum_eq_zero
    intro S _
    rw [Poly.part_send,if_neg (fun eq=>same (by
      have es : D=wear S := congrArg Subtype.val eq
      rw [es,wear_image]))]

theorem project_repaint (P : Poly (YM.Stock.census V)) : project (repaint P)=P := by
  rw [repaint,map_sum]
  simp_rw [project_send _ (wear_kept _) _,wear_image]
  ext s
  rw [Poly.part_sum,sum_eq_single s.val,Poly.part_send,if_pos rfl]
  · intro T _ ne
    exact (Poly.part_send ..).trans (if_neg (fun e=>ne (congrArg Subtype.val e).symm))
  · simp

end YM.Integration.InletSusceptibility.Painted
