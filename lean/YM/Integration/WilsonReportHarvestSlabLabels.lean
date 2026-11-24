import YM.Integration.WilsonReportHarvestSlabPantry

/-! The sole authentic copy carries three distinct original names. Regrouping
them into one new name reads their full signed raw moment at each gauge field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabLabels
open Function Finset MeasureTheory Lattice RG Source Marker RG05Readout RG05Readout.Many
open Wilson Labels Address MergeProof Accent Menu Ribbons Ribbons.ManyCopies
open scoped Classical BigOperators
set_option quotPrecheck false
local notation "S" => Stock.census (Fin 3)
local notation "C₁" => Stock.census (Unit×Fin 3)
local notation "Z" => Stock.census (Unit×Unit)

def named (i:Fin 3):Unit×Fin 3:=((),i)
private theorem injective : Function.Injective named:=fun _ _ h=>congrArg Prod.snd h
private theorem licensed : License C₁ S named:=fun i _=>by
  change i∈(_root_.Finset.univ:Finset (Fin 3)).powerset
  exact mem_powerset.mpr (subset_univ _)

def filed := feed (fun _:Fin 3=>(1:ℂ)) licensed
def cohort : Fibers (Fin 3) Unit:=⟨fun _=>(),fun _=>0,fun _=>rfl⟩
theorem policy : Pantry.Policy cohort C₁ Z:=fun i=>Pantry.all_le _ C₁ (by
  change _∈(_root_.Finset.univ:Finset (Unit×Fin 3)).powerset
  exact mem_powerset.mpr (subset_univ _))
def entire : (Stock.census (Fin 3)).Mode:=⟨_root_.Finset.univ,by
  change _∈(_root_.Finset.univ:Finset (Fin 3)).powerset
  exact mem_powerset.mpr (subset_univ _)⟩

theorem original (row:Poly S) :
    (Pantry.pilot cohort policy (filed row)).part ((Z).fire ((),()))=row.part entire := by
  let mode:(C₁).Mode:=⟨_,policy ((Z).fire ((),()))⟩
  have active (i:Unit×Fin 3):i∈mode.val:=by
    apply ((partialGroup Unit cohort).reaped _ i).2
    change (i.1,())∈{((),())}
    exact mem_singleton.mpr (Subsingleton.elim _ _)
  have lit (i:(S).Mode):Lit C₁ named i.val:=⟨by
    change _∈(_root_.Finset.univ:Finset (Unit×Fin 3)).powerset
    exact mem_powerset.mpr (subset_univ _),injective.injOn⟩
  have only (i:(S).Mode) (same:(lit i).climb=mode): i=entire:=by
    apply Subtype.ext
    apply eq_univ_of_forall
    intro j
    have mem: named j∈(lit i).climb.val:=same ▸ active _
    obtain ⟨v,hv,e⟩:=mem_image.mp mem
    exact injective e ▸ hv
  have all:(lit entire).climb=mode:=by
    apply Subtype.ext
    ext j
    exact ⟨fun _=>active j,fun _=>mem_image.mpr ⟨j.2,mem_univ _,Prod.ext (Subsingleton.elim _ _) rfl⟩⟩
  change (feed _ licensed row).part mode=row.part entire
  rw [parts_of_feed,sum_eq_single entire]
  · rw [move,dif_pos (lit entire),Poly.part_send,if_pos all.symm,prod_const_one,one_mul]
  · intro i _ hi
    rw [move,dif_pos (lit i),Poly.part_send,if_neg (fun h=>hi (only i h.symm))]
  · simp

theorem cold {G:Gauge} {n:Side} (A:Config G n→Poly C₁) (U:Config G n):
    spice C₁ (fun _=>0) A U=A U:=by
  unfold spice Mach
  simp only [Poly.send_zero,Finset.sum_const_zero,Push.GridApprox.Nil.pass_zero,one_mul]

theorem copy {G:Gauge} {n:Side} {X:Rep G n} {P:Fin 3→Three G n}
    {F:Config G n→Poly S} {o:Fin 3→Site n} {w t e c α β b y z:ℝ}
    (ha:Alcove X P F o (fun _=>w) t e c) (physical:X.Lawful α β b y z)
    (live:Integrable F (prior G n)) (hw:0<w) (he:0≤e) (hc:0≤c) :
    Integrable (fun U=>filed (F U)) (prior G n) ∧
    Alcove X (P∘Prod.snd) (fun U=>filed (F U)) (o∘Prod.snd) (fun _=>w) t e c := by
  refine ⟨(filed.toLinearMap.toContinuousLinearMap.restrictScalars ℝ).integrable_comp live,?_⟩
  have names:combine named (fun _=>1) P=P∘Prod.snd:=by
    funext j
    unfold combine
    rw [sum_eq_single j.2]
    · rw [if_pos (show named j.2=j from Prod.ext (Subsingleton.elim _ _) rfl),one_smul]
      rfl
    · intro i _ hi
      rw [if_neg (fun h=>hi (congrArg Prod.snd h)),zero_smul]
    · simp
  have cap (j:Unit×Fin 3):(_root_.Finset.univ.filter (fun i:Fin 3=>named i=j)).card≤1:=by
    apply card_le_one.mpr
    intro i hi k hk
    exact injective ((mem_filter.mp hi).2.trans (mem_filter.mp hk).2.symm)
  have grouped:=ha.group (δ:=named) (h:=licensed) (q:=o∘Prod.snd) (w':=fun _=>w)
    (N:=1) (fun _=>(1:ℂ)) physical live rfl (by decide) he hc (fun _=>hw) (fun _=>hw)
    (fun _=>by simp) cap
  rw [names] at grouped
  exact grouped

end YM.Integration.WilsonReportHarvestSlabLabels
