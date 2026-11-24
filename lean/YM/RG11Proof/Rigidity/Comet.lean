import YM.RG11Proof.Rigidity.Petals

/-!
# Use superpositions of on shell endpoints on the fixed finite word horizon
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd Function Submodule
open scoped BigOperators Classical

variable {G : Gauge}

-- Jet value allowed to depend on the known anchor in S.
abbrev Stream := E4 → (j : ℕ) → Sheet j

def conduit (q : Stream) : Bristle G := fun c a=>
   if a.dart.tone=c then a.dart.mode (q a.origin a.dart.degree) else 0

lemma conduit_fixed (W : Crowd G) (p : List (Spindle G)) (b : Bristle G)
    (h : ∀ (a : Prayer), stainL W ((hears a,b)::p)=0) (v : Stream) : stainL W ((conduit v,b)::p)=0 := by
  classical
  let T:=(W.flatMap fun i=> i.2).toFinset
  let key : Pig G→ E4×ℕ:=fun i=> (i.origin,i.dart.degree)
  let U := T.image key
  let C : Bristle G→ₗ[ℝ] ℝ:=
    { toFun u:=stainL W ((u,b)::p)
      map_add' u s:=stains_add ..
      map_smul' c u:=stains_scale .. }
  let μ (t : E4×ℕ) : Bristle G:= hears ⟨t.1,t.2,v t.1 t.2⟩
  apply (stains_quote W p (conduit v) (∑ t∈U, μ t) b ?_).trans
  · change C (∑ t∈U,μ t)=0
    rw [_root_.map_sum]; exact Finset.sum_eq_zero fun i _=>h _
  intro w hw i hi d
  have he : key i∈U:=Finset.mem_image_of_mem _ (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨_,hw,hi⟩))
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single_of_mem (key i) he]
  · simp [conduit,μ,hears,cabin,key]
  intro a _ ha
  change (if h : i.origin=a.1 ∧ i.dart.tone=_ ∧ i.dart.degree=a.2 then _ else 0)=0
  rw [dif_neg]; intro ht; exact ha (Prod.ext ht.1.symm ht.2.2.symm)

theorem cosmic (c : G.ColorIndex) {S : Finset E4} {W : Crowd G} (h : Blind S W) (V : List (Stream×Stream)) :
    stainL W (V.map (byColor conduit))=0 := by
  suffices hm : ∀ L : List (Prayer×Prayer),stainL W (V.map (byColor conduit)++L.map fire)=0 by simpa using hm []
  intro L; induction V generalizing L with
  | nil=> simpa using field_blank c h L
  | cons p V ih=>
    change stainL W ((conduit p.1,conduit p.2)::(V.map (byColor conduit)++L.map fire))=0
    refine conduit_fixed _ _ _ (fun i=> ?_) _
    rw [stains_perm]; refine conduit_fixed _ _ _ (fun j=> ?_) _
    let t := (j,i)
    refine (chairs W (l:=fire t::_) ?_).trans (ih (t::L))
    rw [List.map_cons]; exact List.perm_middle.symm

end YM.RG11.Rigidity
