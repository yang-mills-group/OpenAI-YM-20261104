import YM.Integration.WilsonCenteredNestedEdge

/-! A complete enrolled comparable packet, at every physical position and
rotation, with both its separate grade-specific gross fees and its deep
through-cap signed comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRawRows
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRealOrbit WilsonCenteredNestedEdge
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {n : ℕ}
def degree (v : Fin n→S.Tag) : ℕ := ∑i,(v i).1
def face (P : Prescription F.sector.derivatives) (H m : ℕ) (c : Q.channels m)
    (x : Fin n→E4) (v : Fin n→S.Tag) (o:E4) (k:Ortho) (b:Bool) : ℂ :=
  WilsonCenteredNestedProjectedShadow.read F Q m H c (restored F P H x (voices v) o k b)

def Quoted (P : Prescription F.sector.derivatives) (v : Fin n→S.Tag) (H : ℕ) (M η : ℝ)
    (j : ℕ) (A : ℝ) :=
  ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:Fin n→E4)(o:E4),WithinRoom r M η x o → ∀(k:Ortho)(b:Bool)(i:Fin (H+1))(c:Q.channels i.val),
    ‖face F Q P H i.val c x v o k b - express Q i.val c x v o‖ ≤ wage j A r * WilsonCenteredNestedEdge.port r (H+1) (degree v) ∧
    ‖express Q i.val c x v o‖ ≤ wage j A r * WilsonCenteredNestedEdge.port r i.val (degree v) ∧
    ‖face F Q P H i.val c x v o k b‖ ≤ wage j A r * WilsonCenteredNestedEdge.port r i.val (degree v)

theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent) (fac : Facilities C f S)
    (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (v : Fin n→S.Tag) (H : ℕ)
    {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ (j : ℕ) (A : ℝ),0 ≤ A ∧ Quoted F Q P v H M η j A := by
  let T := Σ i:Fin (H+1),Q.channels i.val
  let holds (t:T) (j:ℕ) (A:ℝ) := ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:Fin n→E4)(o:E4),WithinRoom r M η x o →
    ‖express Q t.1.val t.2 x v o‖ ≤ wage j A r * WilsonCenteredNestedEdge.port r t.1.val (degree v)
  have expand (t:T) (j:ℕ) (A:ℝ) (l:ℕ) (B:ℝ) (jl:j≤l) (An:0≤A) (AB:A≤B) (old:holds t j A) : holds t l B := by
    filter_upwards [old,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r row rp x o fit
    exact (row x o fit).trans (mul_le_mul_of_nonneg_right (wage_le jl An AB) (by unfold WilsonCenteredNestedEdge.port;positivity))
  have offered (t:T) : ∃j A,0≤A ∧ holds t j A := by
    obtain ⟨j,A,An,earn⟩ := WilsonCenteredNestedLoggedRow.original F Q fac.toServices (first_log F fac lo ticket Q.spans) v t.1 t.2 Mn ηp
    refine ⟨j,A,An,?_⟩
    filter_upwards [earn] with r row x o fit
    simpa only [wage,WilsonCenteredNestedEdge.port,degree,Finset.prod_pow_eq_pow_sum] using row x o fit.span fit.spaced
  obtain ⟨j,A,An,gross⟩ := pool holds expand offered
  obtain ⟨l,B,Bn,signed⟩ := WilsonCenteredNestedProjectedShadow.original F Q hp fac foundation lo ticket H (voices v) Mn ηp
  let N := max j l
  refine ⟨N,A+B,add_nonneg An Bn,?_⟩
  filter_upwards [eventually_all.mpr gross,signed,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin),
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r rows diff rp r1 x o fit k b i c
  have power : r^((H:ℝ)+1-weight (degrees v)) = WilsonCenteredNestedEdge.port r (H+1) (degree v) := by
    rw [Real.rpow_sub rp]
    unfold WilsonCenteredNestedEdge.port degree
    congr 1
    · rw [←Nat.cast_one (R:=ℝ),←Nat.cast_add,Real.rpow_natCast]
    · rw [show weight (degrees v) = (↑(∑i:Fin n,(v i).1):ℝ) by simp [weight,degrees],Real.rpow_natCast]
  let X := face F Q P H i.val c x v o k b
  let Y := express Q i.val c x v o
  have deep : ‖X-Y‖ ≤ wage N B r * WilsonCenteredNestedEdge.port r (H+1) (degree v) := by
    have miss := diff x o fit k b i c
    rw [power] at miss
    exact miss.trans (mul_le_mul_of_nonneg_right (wage_le (le_max_right ..) Bn le_rfl) (by unfold WilsonCenteredNestedEdge.port;positivity))
  have ordinary : ‖Y‖ ≤ wage N A r * WilsonCenteredNestedEdge.port r i.val (degree v) :=
    (rows ⟨i,c⟩ x o fit).trans (mul_le_mul_of_nonneg_right (wage_le (le_max_left ..) An le_rfl) (by unfold WilsonCenteredNestedEdge.port;positivity))
  have cheaper : WilsonCenteredNestedEdge.port r (H+1) (degree v) ≤ WilsonCenteredNestedEdge.port r i.val (degree v) :=
    div_le_div_of_nonneg_right (pow_le_pow_of_le_one rp.le r1 i.isLt.le) (pow_nonneg rp.le _)
  have wn : 0 ≤ wage N B r := mul_nonneg Bn (pow_nonneg ((zero_le_one.trans (shell_one r))) _)
  refine ⟨deep.trans (mul_le_mul_of_nonneg_right (wage_le le_rfl Bn (le_add_of_nonneg_left An)) (by unfold WilsonCenteredNestedEdge.port;positivity)),
    ordinary.trans (mul_le_mul_of_nonneg_right (wage_le le_rfl An (le_add_of_nonneg_right Bn)) (by unfold WilsonCenteredNestedEdge.port;positivity)),?_⟩
  calc
    ‖X‖ = ‖(X-Y)+Y‖ := by congr 1;abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ wage N B r * WilsonCenteredNestedEdge.port r i.val (degree v) + wage N A r * WilsonCenteredNestedEdge.port r i.val (degree v) :=
      add_le_add (deep.trans (mul_le_mul_of_nonneg_left cheaper wn)) ordinary
    _ = _ := by unfold wage;ring

end YM.Integration.WilsonCenteredNestedRawRows
