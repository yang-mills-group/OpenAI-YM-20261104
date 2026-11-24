import YM.RG11Proof.Rigidity.Brush

/-!
# Crossing all colors at play
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd
open scoped BigOperators Classical

variable {G : Gauge}

def fire (p : Prayer × Prayer) : Spindle G := (hears p.1,hears p.2)

theorem field_blank (c : G.ColorIndex) {S : Finset E4} {W : Crowd G} (h : Blind S W) (V : List (Prayer×Prayer)) :
    stainL W (V.map fire)=0 := by
  suffices hm : ∀ L : List Panel, Journey Prod.snd S L → stainL W (V.map fire++L.map turnPanel)=0 by
    simpa using hm [] ⟨List.nodup_nil,by simp [stroll]⟩
  intro l hl; induction V generalizing l with
  | nil=> rw [List.map_nil,List.nil_append]; exact loom h l hl
  | cons p V ih =>
    let U := S∪(stroll (X:=E4) Prod.snd l).toFinset
    change stainL W ((hears p.1,hears p.2)::(V.map fire++l.map turnPanel))=0
    refine first_fixed c U _ _ _ (fun v y hy=> ?_) _
    rw [stains_perm]
    refine first_fixed c (insert y U) _ _ _ (fun a z hz=> ?_) _
    let i : Panel := ((a,z),v,y)
    have he : Journey Prod.snd S (i::l) := by
      apply legJourney .. |>.mpr
      have hq : z∉U := fun hi=> hz (Finset.mem_insert_of_mem hi)
      have hr : z≠y := fun he=> hz (by rw [he]; exact Finset.mem_insert_self ..)
      refine ⟨hr,fun hS=> hq (Finset.mem_union_left _ hS),fun hS=> hy (Finset.mem_union_left _ hS),hl.nodup,fun t ht hs=> ?_⟩
      have hk : t∈U:= Finset.mem_union_right _ (List.mem_toFinset.mpr ht)
      rcases Finset.mem_insert.mp hs with he|he
      · exact hy (by rw [← show t=y from he]; exact hk)
      rcases Finset.mem_insert.mp he with he|he
      · exact hq (by rw [← show t=z from he]; exact hk)
      exact hl.safe t ht he
    refine Eq.trans (chairs W (l:=turnPanel i::_) (t:=V.map fire++List.map turnPanel (i::l)) ?_) (ih _ he)
    rw [List.map_cons]; exact List.perm_middle.symm

end YM.RG11.Rigidity
