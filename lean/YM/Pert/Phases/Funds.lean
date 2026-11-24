import YM.Pert.Flow.End
/-! Preparing the corrected-detector Funds with the actual phase ensemble. Note the restriction to one- and two-slot diagnostic rows of the upstream weak output. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Pert.PhaseControl
open Function Filter Topology Set MeasureTheory Analysis Extraction Retain Table Maxwell Cells Bid Org OS
open scoped BigOperators Classical Topology
variable {G:Gauge} {C:Family G} {F:Order} {S:Table C.book} (B:Spec.Final C F S)
variable {d:ℕ} {X:Columns C S d} (Y:X.Trials) (Q:Y.Valid F)

lemma fundsSupplied (h:MergeProof.Ribbons.Materials C) :
      Funds Y Q B.α.unselected := by
    obtain ⟨r,D,u,ψ,W,hv,hs⟩:=h.room
    have hg := MergeProof.Accent.grilled C h.makes hs h.opens B.room.copies
    let V:=B.α.room; let A:=B.α.unselected
    let X:=B.sector
    let D:=X.derivatives
    let hn :=B.room.kernel
    have hSteady := B.phase.phase.still
    have H := Work.B03.answer hn D V A hSteady B.phase.phase.lengths
    refine episode Work.B15.answer Work.B16.answer Work.B17.answer Work.B18.answer B.room A H hSteady ?_ Y Q
    exact Work.B05.answer Work.B04.answer B.room hg X B.phase.transport V A hSteady H

abbrev members:= B.α.space.X

abbrev phase (v:members B) : Table C.book:= B.α.ensemble v

def observed (k) (v:members B) (i:Fin X.amount) (c:Fin (X.dim+1)) :=
    (probe' (D:=phase B v) Y k i ((phase B v).project d (Y.later k c)):ℂ)

include Q
private lemma one_ident (i c k) (h : (X.row i).extra = 0) (v:members B) :
      observed B Y k v i c = (phase B v).expect [plant Y k i c 0] ∧
        (standard C).useAt (standard C) (Y.tested k i) (testFns (X:=X) i c)=Y.singleton k i c 0 := by
    let T:= phase B v
    have hc : Y.realPlace k i ∈ conf _:= generic_conf _ (Q.generic _ _)
    have he {D : Type} (f: Fin ((X.row i).extra+1)→ D) : List.ofFn f=[f 0] := by
      rw [List.ofFn_succ]; congr; simp [h]
    have ht : observed B Y k v i c = _ := ready Y k _ _ (B.phase.phase.states v).laws.toSymmetric hc
    rw [←T.readAt] at ht -- T alias maybe
    change _ = (phase B v).expect (List.ofFn fun s => plant Y k i c s) at ht
    rw [he] at ht
    refine ⟨ht,?_⟩
    let R:=standard C
    have hy := (R.readAt (fun s=> Ward.expose (testFns (X:=X) i c s)) (Y.tested k i)).symm
    unfold Word.realize at hy
    rw [he] at hy
    exact hy.trans (R.readAt (fun _ : Fin 1 => Ward.expose (testFns (X := X) i c 0)) (points (fun _=>Y.tested k i 0)))

private lemma pair_ident (i c k) (h : (X.row i).extra = 1) (s : Fin ((X.row i).extra+1)) (hs:0<s) (v:members B) :
      observed B Y k v i c = (phase B v).expect [plant Y k i c 0,plant Y k i c s] ∧
        (standard C).useAt (standard C) (Y.tested k i) (testFns (X:=X) i c)= free2 Y k i c 0 s := by
    let T:= phase B v
    have hc : Y.realPlace k i ∈ conf _:= generic_conf _ (Q.generic _ _)
    have he {D : Type} {n:ℕ} (f: Fin (n+1)→ D) {t:Fin (n+1)} (h:n=1) (ht:0<t) : List.ofFn f=[f 0,f t] := by
      subst n; fin_cases t
      · exact (ht.ne rfl).elim
      rfl
    have ht : observed B Y k v i c = _ := ready Y k _ _ (B.phase.phase.states v).laws.toSymmetric hc
    rw [←T.readAt] at ht
    change _ = (phase B v).expect (List.ofFn fun s => plant Y k i c s) at ht
    rw [he _ h hs] at ht
    refine ⟨ht,?_⟩
    let R:=standard C
    have hy := (R.readAt (fun s=> Ward.expose (testFns (X:=X) i c s)) (Y.tested k i)).symm
    unfold Word.realize at hy
    rw [he _ h hs] at hy
    have ht' := R.readAt (fun j => Ward.expose (![testFns (X:=X) i c 0, testFns (X:=X) i c s] j)) (points ![Y.tested k i 0,Y.tested k i s])
    refine hy.trans (ht'.trans ?_)
    rw [free2,Columns.Trials.cumulant,sub_add_cancel]
    rfl

include Q 
lemma singletonGone (i c s) : ∃ x, Tendsto (fun k=> Y.singleton k i c s) atTop (𝓝 x) := by
    let T (x : Points ((X.row i).extra+1)) := points fun _ : Fin 1 => x s
    have hv : Continuous T := by unfold T points; fun_prop
    let E := T (X.row i).expected
    have hm : E ∈ conf _ := fun _ _ _ => @Subsingleton.elim (Fin 1) _ _ _
    let R:=standard C
    exact ⟨_,(((R.class_smooth R (Maxwell.table_smooth _) (fun _ : Fin 1 => testFns (X := X) i c s)).continuousOn.continuousAt
      ((conf_open _).mem_nhds hm)).tendsto.comp (hv.continuousAt.tendsto.comp (Q.tuned i)))⟩

lemma lowCharge (s:ℕ→members B) (i c) (hf:Funds Y Q B.α.unselected) (k) (h : (X.row i).extra = 0) :
      ‖observed B Y k (s k) i c - (standard C).useAt (standard C) (Y.tested k i) (testFns (X:=X) i c)‖ ≤ Y.gap k := by
    let v:=s k
    obtain ⟨hD,hS⟩:=one_ident B Y (Q:=Q) i c k h v -- Q explicit?
    change ‖observed B Y k v .. - _‖ ≤ _
    rw [hD,hS]
    exact Retain.one_near Y Q _ _ hf B.phase.phase.decomposition (B.phase.phase.chosen v) _ _ _ _
lemma highCharge (s:ℕ→members B) (i c) (hf:Funds Y Q B.α.unselected) (k) (t : Fin ((X.row i).extra+1)) (ht:0<t) :
      ‖observed B Y k (s k) i c - (standard C).useAt (standard C) (Y.tested k i) (testFns (X:=X) i c)‖ ≤
        Y.gap k+(‖Y.singleton k i c 0‖+‖Y.singleton k i c t‖)*Y.gap k := by
   have hN: t.val ≤ (X.row i).extra := Nat.lt_succ_iff.1 t.isLt
   have h₀ : 0 < t.val:=ht
   have hD : (X.row i).extra=1 := le_antisymm (X.row i).cap ((show 1 ≤ t.val from h₀).trans hN)
   obtain ⟨hP,hM⟩:=pair_ident B Y (Q:=Q) i c k hD t ht (s k)
   rw [hP,hM]
   exact pair_near Y Q _ _ hf B.phase.phase.decomposition (B.phase.phase.chosen (s k)) k i c 0 t ht
end YM.Pert.PhaseControl
