import YM.Integration.WilsonMaxwellThermometerInteracting

/-! Read the first interacting coefficient before taking the limit of the
oriented input fields. Both the source vertices and the action vertex belong
to the original finite position prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFirstDetector
open Function Set Filter Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose
open XSpace.Cirrus XSpace.Photo PowerSeries WilsonMaxwellThermometerInteracting
open scoped Topology BigOperators Classical

variable {G : Gauge} (W : Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)

def sampled (x : Sample 3) : Point G 6 3 :=
  row (cooked W V 6 x 0) (cooked W V 6 x 1)

def continuum (x : Points 3) : Point G 6 3 :=
  row (scene x 6) (checked1 W V 6 x)

/-- The whole seven-face derivative before integration. -/
theorem sensed (p : Tags G 6 3) : Senses (conf 3) (fun x => sampled W (V:=V) x p)
    (fun x => continuum W (V:=V) x p) := by
  intro x hx
  have a := tendsto_pi_nhds.mpr fun s : Badge => scans0 W V 6 (missing p s) x hx
  have b := tendsto_pi_nhds.mpr fun s : Badge => scans1 W V 6 (missing p s) x hx
  have c : Continuous (fun h : (Badge→ℂ)×(Badge→ℂ) => first h.1 h.2) := by
    unfold first
    fun_prop
  exact c.continuousAt.tendsto.comp (a.prodMk_nhds b)

def finite (m : Mesh) : Point G 6 3 :=
  (m.spacing : ℂ)^(4*3) • ∑ x : m.Tuple (n:=3),
    m.smear (Mesh.back m x) (Rose.test K) • sampled W (V:=V) ⟨m,m.back x,0⟩

theorem finite_read (m : Mesh) (p : Tags G 6 3) : finite W K m p =
    Deposit m (fun x => sampled W (V:=V) x p) (Rose.test K) := by
  simp only [finite, Deposit, smul_apply, sum_apply, smul_eq_mul]

theorem fixed (p : Tags G 6 3) : Tendsto (fun m => finite W K m p) Front
    (𝓝 ((Rose.test K).applyTo fun x => continuum W (V:=V) x p)) := by
  simp_rw [finite_read]
  exact sees_test (conf 3) _ _ (conf_open _) (sensed W p) (fun _ _ _ => rfl) (Rose.test K).tsupport_subset

def smeared : Point G 6 3 := MultilinearMap.mk'
  (fun p => (Rose.test K).applyTo fun x => continuum W (V:=V) x p)
  (fun p i a b => tendsto_nhds_unique (fixed W K _) (by
    simpa only [MultilinearMap.map_update_add] using
      (fixed W K (update p i a)).add (fixed W K (update p i b))))
  (fun p i a b => tendsto_nhds_unique (fixed W K _) (by
    simpa only [MultilinearMap.map_update_smul] using (fixed W K (update p i b)).const_smul a))

theorem actual (m : Mesh) : finite W K m (Rose.tag G) = coeff 1 (Detector W K m) := by
  rw [finite_read,detector]
  congr 1
  funext x
  rw [together,coefficient]
  simp only [sampled,read,batchT,coeff_mk]
  rfl

theorem normalized (hG : G.Simple) : smeared W K (Rose.tag G) = ((c_T K : ℝ) : ℂ) := by
  apply tendsto_nhds_unique (fixed W K (Rose.tag G))
  simpa only [actual] using diagnosed W K hG

/-- The whole regulated coefficient at varying intrinsic fields, taken in the
same order as the corresponding regulator and field coordinates. -/
theorem moving {I : Type*} {l : Filter I} (m : I → Mesh) (geometry : Tendsto m l Front)
    (v : I → Tags G 6 3) (fit : ∀ i, Reads 6 (F:=l) (fun z => v z i) (Rose.tag G i))
    (hG : G.Simple) :
    Tendsto (fun z => finite W K (m z) (v z)) l (𝓝 ((c_T K : ℝ) : ℂ)) := by
  rw [←normalized W K hG]
  exact lights 6 _ v fit (fun z => finite W K (m z)) (smeared W K)
    fun p => (fixed W K p).comp geometry

end YM.Integration.WilsonMaxwellThermometerFirstDetector
end
