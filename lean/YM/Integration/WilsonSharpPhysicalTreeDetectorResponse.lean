import YM.Integration.WilsonSharpPhysicalTreeDetectorKernel

/-! Physical basis responses on the compact rotation group, and the exact
identification of the full finite detector with the elected through-grade packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorResponse
open Function Filter Set MeasureTheory Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription WilsonCenteredNestedShadowBasis WilsonSharpPhysicalTreeDetectorKernel
open scoped Classical Topology BigOperators ContDiff
attribute [local instance] Orbits.measO Orbits.borelO Orbits.hμ YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I J : Type} [Fintype I] [Fintype J] {d : I→ℕ} {g : J→ℕ}

abbrev Site (h : ℕ) := Σ n : Fin (h+1), Σ i : ↥(bands F.sector.derivatives n.val), ↥(Q.port.sheet i.val).support

def Good (h : ℕ) (x : I→E4) (o : E4) : Prop :=
  ∀ a : Site F Q h, ∀ k : Ortho, Injective (beside x (swung a.2.2.val k o))

lemma centerGood (h : ℕ) (o : E4) : Good F Q h (sole o) o := by
  intro a k
  let e := a.2.2.val
  have eq : beside (sole o) (swung e k o) = (fun z => o + Ortho.move k z) ∘ beside (sole (0:E4)) (bearing e) := by
    funext u
    cases u with
    | inl j => change o = o + Ortho.motion k 0; rw [map_zero,add_zero]
    | inr j => rfl
  change Injective (beside (sole o) (swung e k o))
  rw [eq]
  exact ((add_right_injective o).comp (Ortho.move_injective k)).comp (bearing_clear e)

omit [Fintype I] in
lemma margin {h : ℕ} {x : I→E4} {o : E4} (ok : Good F Q h x o) (n : Fin (h+1)) :
    orbitMargin Q.port n.val x o := by
  intro i hi k e he
  let move := fun z : E4 => Ortho.move k (z-o)
  have eq : beside (away (Ortho.move k ∘ x) (Ortho.move k o)) (bearing e) = move ∘ beside x (swung e k⁻¹ o) := by
    funext u
    cases u with
    | inl j => exact ((Ortho.motion k).map_sub (x j) o).symm
    | inr j => change bearing e j = Ortho.move k ((o + Ortho.move k⁻¹ (bearing e j)) - o)
               rw [add_sub_cancel_left,Ortho.move_inv]
  rw [eq]
  exact ((Ortho.move_injective k).comp (fun _ _ heq => sub_left_inj.mp heq)).comp
    (ok ⟨n,⟨i,hi⟩,⟨e,he⟩⟩ k⁻¹)

include F in
private lemma continuous_at_port (x : I→E4) (v : Labels S d) (o : E4) (e : Exterior C.book)
    (w : Labels S (expo e)) (ok : ∀ k, Injective (beside x (swung e k o))) :
    Continuous (fun k => whole S x v (swung e k o) w) := by
  let place : Ortho → Loc I (Fin e.n) := fun k => (x,o,swung e k o)
  have motion : Continuous (fun k => swung e k o) := continuous_pi fun j =>
    continuous_const.add (orbCont.comp (continuous_const.prodMk continuous_id))
  have cont : Continuous place := continuous_const.prodMk (continuous_const.prodMk motion)
  exact continuous_iff_continuousAt.mpr fun k =>
    (whole_cont_at v w S F.room.kernel (x:=place k) (ok k)).comp cont.continuousAt

/-- Each input is a true physical correlation on one fixed basis exterior. -/
def response (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) : Signals F Q h :=
  fun a => ContinuousMap.mkD
    (fun k => whole S x v (swung a.2.2.1.val k o) (axis S (expo a.2.2.1.val) a.2.2.2)) 0

lemma response_apply (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) (ok : Good F Q h x o)
    (a : Probe F Q h) (k : Ortho) : response F Q h x v o a k =
      whole S x v (swung a.2.2.1.val k o) (axis S (expo a.2.2.1.val) a.2.2.2) :=
  ContinuousMap.mkD_apply_of_continuous (continuous_at_port F x v o _ _ (ok ⟨a.1,a.2.1,a.2.2.1⟩))

include F in
private lemma expand_exterior (x : I→E4) (v : Labels S d) (y : J→E4) (w : Labels S g)
    (hx : Injective (beside x y)) : whole S x v y w =
      ∑ t : Slot S g, coeff w t * whole S x v y (axis S g t) := by
  let L : MultilinearMap ℂ (fun j=>S.Field (g j)) ℂ := sectionLabels v (moment S (d:=Sum.elim g d) (beside y x))
  have turn (z : Labels S g) : L z = whole S x v y z := by
    change sectionLabels v (moment S (d:=Sum.elim g d) (beside y x)) z = _
    rw [sectionLabels_apply]
    exact whole_flip v z x y F.room.kernel hx
  rw [←turn w,expand L w]
  exact Finset.sum_congr rfl fun t _ => congrArg (coeff w t * ·) (turn (axis S g t))

private lemma spin_formula (n : ℕ) (x : I→E4) (v : Labels S d) (o : E4) (k : Ortho)
    (hm : orbitMargin Q.port n x o) :
    spinning Q.port F.sector.turns n x o k v = ∑ i∈bands F.sector.derivatives n,
      ∑ e∈(Q.port.sheet i).support, ((Q.port.sheet i) e * whole S x v (swung e k o) (turnsPort F.sector.turns k e)) •
        F.sector.turns.act n k (Q.port.loaded i n) := by
  have eq := discrepancy_spin (k:=k) Q.port Q.law Q.continuum F.phase.transport.motion v (0:S.Field 0) hm
  rw [Nesting.Sensor.zero_spin F Q,sub_zero] at eq
  simpa only [discrepancy,map_zero,sub_zero,Finset.sum_smul] using eq

private lemma spin_eval (h : ℕ) (n : Fin (h+1)) (tint : Bool) (u : Signals F Q h) (k : Ortho) :
    spinReader F Q h n tint u k = ∑ i : ↥(bands F.sector.derivatives n.val), ∑ e : ↥(Q.port.sheet i.val).support,
      ∑ t : Slot S (expo e.val), (if tint then star (u ⟨n,i,e,t⟩ k) else u ⟨n,i,e,t⟩ k) •
        kernel F Q n.val i.val e.val t tint k := by
  cases tint <;> simp only [spinReader,_root_.sum_apply,ContinuousMap.sum_apply,ContinuousLinearMap.comp_apply,
    Bool.false_eq_true,if_false,if_true,ContinuousLinearMap.id_apply,ContinuousLinearMap.proj_apply] <;> rfl

private lemma spin_response (h : ℕ) (n : Fin (h+1)) (tint : Bool) (x : I→E4) (v : Labels S d)
    (o : E4) (ok : Good F Q h x o) (k : Ortho) : spinReader F Q h n tint (response F Q h x v o) k =
      spinning Q.port F.sector.turns n.val x o k (if tint then bar F.room.kernel.spin v else v) := by
  rw [spin_eval,spin_formula F Q _ _ _ _ _ (margin F Q ok n)]
  rw [← Finset.sum_coe_sort (bands F.sector.derivatives n.val)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort (Q.port.sheet i.val).support]
  refine Finset.sum_congr rfl fun e _ => ?_
  let y := swung e.val k o
  let w := turnsPort F.sector.turns k e.val
  have hx : Injective (beside x y) := ok ⟨n,i,e⟩ k
  let a := (Q.port.sheet i.val) e.val
  let z := F.sector.turns.act n.val k (Q.port.loaded i.val n.val)
  cases tint with
  | false =>
    change _ = (a * whole S x v y w) • z
    rw [expand_exterior F x v y w hx,Finset.mul_sum,Finset.sum_smul]
    refine Finset.sum_congr (by ext t; simp) fun t _ => ?_
    rw [response_apply F Q _ _ _ _ ok]
    change (whole S x v y (axis S _ t)) • ((a * coeff w t) • z) = _
    rw [smul_smul]; apply congrArg (· • z); ring
  | true =>
    change _ = (a * whole S x (bar F.room.kernel.spin v) y w) • z
    have reality := whole_bar (v:=v) (w:=bar F.room.kernel.spin w) F.room.kernel.spin F.room.kernel hx
    rw [bar_bar] at reality
    rw [reality,expand_exterior F x v y _ hx,star_sum,Finset.mul_sum,Finset.sum_smul]
    refine Finset.sum_congr (by ext t; simp) fun t _ => ?_
    rw [response_apply F Q _ _ _ _ ok]
    change star (whole S x v y (axis S _ t)) • ((a * star (coeff (bar F.room.kernel.spin w) t)) • z) = _
    rw [smul_smul,star_mul]; apply congrArg (· • z); ring

theorem packet (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) (ok : Good F Q h x o) :
    reader F Q h (response F Q h x v o) = Q.packet h x v o := by
  have avg (n : Fin (h+1)) (b : Bool) : haarReader (spinReader F Q h n b (response F Q h x v o)) =
      averageV Q.port F.sector.turns n.val x o (if b then bar F.room.kernel.spin v else v) := by
    rw [averageV,if_pos (margin F Q ok n)]
    apply integral_congr_ae
    exact Eventually.of_forall (spin_response F Q h n b x v o ok)
  unfold reader Reader.packet
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Q.fresh_eq,checkValue]
  apply congrArg (F.sector.derivatives.rise (d:=n.val) (Nat.le_of_lt_succ n.isLt))
  apply congrArg (Q.knife n.val)
  change (2:ℝ)⁻¹ • (haarReader _ + S.conj F.room.kernel.spin n.val (haarReader _)) = _
  exact congrArg ((2:ℝ)⁻¹ • ·) (congrArg₂ (· + ·) (avg n false) (congrArg (S.conj F.room.kernel.spin n.val) (avg n true)))

abbrev insertion (h : ℕ) (o : E4) (b : S.Field h) : Signals F Q h :=
  response F Q h (sole o) (sole b : Labels S (fun _:Unit => h)) o

theorem retract (h : ℕ) (o : E4) (b : S.Field h) : reader F Q h (insertion F Q h o b) = b := by
  rw [insertion,packet F Q _ _ _ _ (centerGood F Q h o)]
  let v : Labels S (fun _:Unit => h) := sole b
  have carry : Q.packet h (sole o) v o = Q.packet h (sole 0) v 0 := by
    unfold Reader.packet
    refine Finset.sum_congr rfl fun n _ => congrArg _ ?_
    have shift : (fun j : Unit => sole (0:E4) j + o) = sole o := funext fun _ => zero_add o
    have got := Q.fresh_transport n.val (sole (0:E4)) 0 v o
    rw [shift,zero_add] at got
    exact got
  rw [carry,Q.packet_single h h le_rfl b]
  exact F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts b

theorem error (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) (b : S.Field h) (ok : Good F Q h x o) :
    Q.packet h x v o - b = reader F Q h (response F Q h x v o - insertion F Q h o b) := by
  rw [map_sub,packet F Q h x v o ok,retract]

end YM.Integration.WilsonSharpPhysicalTreeDetectorResponse
