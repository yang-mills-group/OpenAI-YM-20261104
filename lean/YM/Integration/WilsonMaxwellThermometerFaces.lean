import YM.XSpace.Carnation

/-! Continuum Maxwell faces on the separated position thermometer. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMaxwellThermometerFaces
open Function Set Filter MeasureTheory XSpace XSpace.Graph3
open XSpace.Cirrus XSpace.Normalize XSpace.Rose XSpace.Tornado XSpace.Structure1
open scoped Topology Classical BigOperators

variable {G : Gauge} (W : Initialize G) (g : G.Simple)

def faces (x : Points 3) (p : Tags G 6 3) (s : Badge) : ℂ :=
  scene x 6 (missing p s)

/-- The constant coefficient of the native connected polynomial on the full
seven faces of the Maxwell reading. -/
def connected (x : Points 3) (p : Tags G 6 3) : ℂ :=
  PowerSeries.constantCoeff (b3 (fun s => PowerSeries.C (faces x p s)))

theorem opposite_parity (x : Points 3) (hx : x ∈ conf 3) (p q t : Sec G 6)
    (hp : hinge 6 p = -p) (hq : hinge 6 q = q) (ht : hinge 6 t = t) :
    connected x (trip p q t) = 0 := by
  have h (s : Badge) (hs : (0 : Fin 3) ∈ s) : faces x (trip p q t) s = 0 := by
    apply even_zero x _ hx
    let a := missing (trip p q t) s
    intro F
    have he : hinge 6 ∘ a = update a 0 (-a 0) := by
      funext i
      fin_cases i <;> simp [a, missing, trip, hs, hp, hq, ht, hinge_leaf, apply_ite] <;>
        split <;> simp_all
    rw [show hinge 6 ∘ missing (trip p q t) s = update a 0 (-a 0) from he,
      MultilinearMap.map_update_neg, update_eq_self]
  simp only [connected, b3, two_smul, map_sub, map_add, map_mul, PowerSeries.constantCoeff_C,
    h _ (by decide : (0 : Fin 3) ∈ Finset.univ), h _ (by decide : (0 : Fin 3) ∈ ({0,1} : Badge)),
    h _ (by decide : (0 : Fin 3) ∈ ({0,2} : Badge)), h _ (by decide : (0 : Fin 3) ∈ ({0} : Badge)),
    zero_mul, mul_zero, add_zero, sub_zero]

private lemma unoccupied_upper (p : Sec G 6) (s : Badge) (hs : (0 : Fin 3) ∉ s) :
    missing (trip p (tin G) (tin G)) s = missing (tag G) s := by
  funext i
  fin_cases i <;> simp [missing, trip, tag, hs]

include W g in
private lemma lower_face (p : Sec G 6) (x : Points 3) (hx : x ∈ conf 3)
    (s : Badge) (hs : s.Nonempty) (hs' : (0 : Fin 3) ∉ s) :
    faces x (trip p (tin G) (tin G)) s = 0 :=
  (congrArg (scene x 6) (unoccupied_upper p s hs')).trans (silent W g hx s hs)

private theorem full_input (x : Points 3) (v : Tags G 6 3) :
    faces x v Finset.univ = scene x 6 v := by
  apply congrArg (scene x 6)
  funext i
  simp only [missing, Finset.mem_univ, if_true]

private theorem scaled (M : Point G 6 3) (p t : Sec G 6) (c : ℂ) :
    M (trip p (c • t) (c • t)) = (∏ i, trip 1 c c i) • M (trip p t t) := by
  let v := trip p t t
  let k := trip 1 c c
  have he : trip p (c • t) (c • t) = fun i => k i • v i := by
    funext i; fin_cases i; exact (one_smul ℂ _).symm; all_goals rfl
  rw [he, MultilinearMap.map_smul_univ]

include W g in
private lemma full_face (p : Sec G 6) (x : Points 3) (hx : x ∈ conf 3) :
    faces x (trip p (tin G) (tin G)) Finset.univ = 0 := by
  rw [full_input, scaled (scene x 6) p (Tuk G) ((↑Rose.f : ℂ)^2),
    reaches W g p x hx, smul_zero]

include W g in
/-- The two occupied lower fields include the native diagnostic normalization.
The first field can have any component of the original cap-six space. -/
theorem same_chirality (p : Sec G 6) (x : Points 3) (hx : x ∈ conf 3) :
    connected x (trip p (tin G) (tin G)) = 0 := by
  have lo := lower_face W g p x hx
  simp only [connected, b3, two_smul, map_sub, map_add, map_mul, PowerSeries.constantCoeff_C,
    full_face W g p x hx, lo {1,2} (by decide) (by decide), lo {1} (by decide) (by decide),
    lo {2} (by decide) (by decide), zero_mul, mul_zero, add_zero, sub_zero]

/-- A pointwise calculation only needs the separated configurations in the
support of the actual prescribed profile. -/
theorem tested {V : Normalize.Store G} (K : Pick V) (p : Tags G 6 3)
    (h : ∀ x ∈ conf 3, connected x p = 0) :
    (Rose.test K).applyTo (fun x => connected x p) = 0 := by
  unfold Test.applyTo
  apply integral_eq_zero_of_ae
  filter_upwards with x
  change (Rose.test K) x * connected x p = 0
  by_cases hx : x ∈ tsupport (Rose.test K)
  · rw [h x ((Rose.test K).tsupport_subset hx), mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

end YM.Integration.WilsonMaxwellThermometerFaces
