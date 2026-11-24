import YM.Integration.WilsonOrdinaryNestedMSVertex

/-! Each of the finitely many local signed measurements may have its own
constant and small-radius threshold. The thresholds are fixed before any
placement of the nested tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedLocal
open Function Filter Set Spec Table PhysMS Climb RG17 PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom OPE.Nesting.Tree OPE.Nesting.Composite
open Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousFrame WilsonCenteredNestedProgram WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open WilsonOrdinaryNestedMSVertex
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
variable (g:ℝ→ℝ) (L η:ℝ) (P q:ℕ)

def Seen {n:ℕ} (m:ℕ) (c:Q.channels m) (v:Fin n→S.Tag) : Prop :=
  ∃ C:ℝ,0≤C ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ (x:Fin n→E4) (o:E4),
   (∀i,‖x i-o‖≤L*r) → (∀i l,i≠l→η*r≤‖x i-x l‖) →
   ‖residual F Q J Z M ν m c q r (g r) x o v‖≤C*|g r|^P

def Receipts : (t:Tree) → (t.Leaf→S.Tag) → (t.Inner→ℕ) → ℕ → Prop
 | bud,_,_,_=>True
 | fork _ arm,v,D,H=>
    (∀ (sel:Branches F Q (f:=arm) (rollCaps D)) (m:Fin (H+1)) (c:Q.channels m),
      Seen F Q J Z M ν g L η P q m c (echoTags F Q v sel)) ∧
    ∀i,Receipts (arm i) (childWages i v) (childAge i D) (rollCaps D i)

theorem original (t:Tree) (v:t.Leaf→S.Tag) (D:t.Inner→ℕ) (H:ℕ)
    (rows:Receipts F Q J Z M ν g L η P q t v D H) :
    ∃ C:ℝ,0≤C ∧ ∀K:ℝ,C≤K →
      WilsonCenteredNestedSigned.Signed F Q (program F Q J Z M ν q) g L η P 0 K t v D H := by
  induction t generalizing H with
  | bud => exact ⟨0,le_rfl,fun _ _=>trivial⟩
  | fork n arm ih =>
    let α := (Branches F Q (f:=arm) (rollCaps D)) × (Σ m:Fin (H+1),Q.channels m)
    have seen (a:α) := rows.1 a.1 a.2.1 a.2.2
    choose B bn observe using seen
    have children (i:Fin n) := ih i (childWages i v) (childAge i D) (rollCaps D i) (rows.2 i)
    choose C cn next using children
    let b:=∑a:α,B a
    let c:=∑i,C i
    have bp:0≤b:=Finset.sum_nonneg fun a _=>bn a
    have cp:0≤c:=Finset.sum_nonneg fun i _=>cn i
    refine ⟨b+c,add_nonneg bp cp,fun K cap=>⟨?_,?_⟩⟩
    · intro sel m a
      let u:α:=⟨sel,⟨m,a⟩⟩
      have mini : B u≤b:=Finset.single_le_sum (f:=B) (fun i _=>bn i) (Finset.mem_univ u)
      have large : B u≤K:=mini.trans ((le_add_of_nonneg_right cp).trans cap)
      filter_upwards [observe u,(show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r paid rp
      intro x o near sep
      let leg:=echoTags F Q v sel
      have now:=paid x o near sep
      change ‖residual F Q J Z M ν m a q r (g r) x o leg‖≤B u*|g r|^P at now
      change ‖express Q m a x leg o-program F Q J Z M ν q n m a r (g r) x leg o‖ ≤ _
      rw [relative F Q J Z M ν _ _ _ _ _ rp]
      have diff:=now.trans (mul_le_mul_of_nonneg_right large (pow_nonneg (abs_nonneg _) _))
      have eng : 0≤r^m.val/∏ i,r^(leg i).1:=
        div_nonneg (pow_nonneg rp.le _) (Finset.prod_nonneg fun _ _=>pow_nonneg rp.le _)
      simpa [wage,mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left diff eng
    · intro i
      have mini : C i≤c:=Finset.single_le_sum (f:=C) (fun k _=>cn k) (Finset.mem_univ i)
      exact next i K (mini.trans ((le_add_of_nonneg_left bp).trans cap))

end YM.Integration.WilsonOrdinaryNestedLocal
