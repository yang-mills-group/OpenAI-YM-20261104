import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Formal

/-!
# Continuity of measurement legs and tests

Pay extensions for the bounded T part on *any* threshold with clearance on its layouts,
if T₀ is set before the crop, and prepare the continuity for joint tests. No semiclassical
hypotheses are invoked here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Filter Function Set Scale O O.Enh O.Score O.Read O.Canon PowerSeries
open XSpace XSpace.Normalize Register MS.Land Dframe
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    (phys : Canon.Physical V ψ B)
    {n m h p H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : Covered d H) (he : Covered e H)
    {K : Set (Points n)} {S : Set (Points m)}

/-- Both cropped readings on the same pairs x,y; don't move Far replacements onto
independent weights. -/
def jointY (V : Arenas G) (B : ℝ → Frames G) {n m H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : Covered d H) (he : Covered e H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) (p : ℕ)
    (f : ℂ) (T : ℝ) (x : Points n) (y : Points m) : ℂ :=
  filedCrop122 p f (series V B (-Real.log T) (forest x (T • y)) hd he u v)

def jointD (V : Arenas G) (B : ℝ → Frames G) {n m h H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (he : Covered e H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) (p : ℕ)
    (lh : h ≤ H) (f : ℂ) (T : ℝ) (x : Points n) (y : Points m) : ℂ :=
  filedCrop122 p f (rowsResponse122 V B (-Real.log T) (outgoing (T • y)) h lh he v (filedVector122 V x h p f u))

abbrev Profiles (K : Set (Points n)) (S : Set (Points m)) := ↥K × ↥S

variable {X : Type} [TopologicalSpace X]
include phys
lemma extAt_cont {z : X → Points n}
    (hz : Continuous z) (hs : ∀ x, z x ∈ conf n) (v : Fin n → Sec G H) (k : ℕ) :
    Continuous (fun i => extAt V (z i) H k v) := by
  have hQ (t : Fin n → Toon G H) i : extAt V (z i) H k (fill t) = coeff k
      (install V n (z i) (flash ∘ t)) := by
    rw [coeff_install_eq V (z i) phys.dimensions (flash ∘ t) (d:=H) (fun j => Dframe.size_le (t j)) k]; rfl
  simp_rw [stencil_he (extAt V _ _ _) v, hQ]; apply continuous_finsetSum; intro i _
  apply Continuous.const_mul; exact (phys.awake n (flash ∘ i) k).comp_continuous hz hs

lemma basis_cont {z : X → Points (n+m)} (hz : Continuous z) (hs : ∀ x, z x ∈ conf (n+m))
    {η : X → ℝ} (hη : Continuous η) (u : Words G d) (v : Words G e) (p : ℕ) :
    Continuous (fun i => coeff p (series V B (-(η i)) (z i) hd he (basisFields u) (basisFields v))) := by
  have hU (w : LivesP (labeling v)) (j : Fin m) (k : ℕ) : Continuous
      (fun i => coeff k (cue (seats (B (-(η i)))) (labeling v j) (decode (labeling v) w j))) := by
    obtain ⟨P,hP⟩ := Rhythm.from_poly.mp (polynomial_cost phys.scope (labeling v j) (w j) k)
    change Continuous ((fun t => coeff k (cue (seats (B (-t))) (labeling v j) (own (w j)))) ∘ η)
    rw [hP]; fun_prop
  have raw (w : Scan G (n+m)) (k : ℕ) : Continuous (fun i => coeff k (install V _ (z i) w)) :=
    (phys.awake (n+m) w k).comp_continuous hz hs
  simp_rw [expand_basis phys.scope _ hd he phys.dimensions _, Acres, coeff_C_mul, concert,
    map_sum, play, Constants.admits]
  apply Continuous.mul; · unfold Score.fee; fun_prop
  apply continuous_finsetSum; intro w _; apply continuous_finsetSum; intro j _; apply Continuous.mul
  · exact continuous_finsetProd _ (fun i _ => hU w i _)
  exact raw _ _

omit phys in
lemma multipliers_cont (u : X → Appointed122Fields G d) (hu : ∀ i, Continuous fun x => account G (d i) (u x i))
    (w : Words G d) : Continuous (fun x => filedMultipliers122 (u x) w) := by
  unfold filedMultipliers122; simp_rw [← account_entry]
  exact continuous_finsetProd _ (fun j _ => (continuous_apply _).comp (hu j))

lemma continuous_crop {z : X → Points (n+m)} (hz : Continuous z) (hs : ∀ i, z i ∈ conf _)
    {η : X → ℝ} (ht : Continuous η)
    (u : X → Appointed122Fields G d) (v : X → Appointed122Fields G e) (p : ℕ) {f : X → ℂ} (hf : Continuous f)
    (hu : ∀ i, Continuous fun x => account G (d i) (u x i))
    (hv : ∀ i, Continuous fun x => account G (e i) (v x i)) :
    Continuous (fun i => filedCrop122 p (f i) (series V B (-(η i)) (z i) hd he (u i) (v i))) := by
  simp_rw [decompose_near V _ _ _ hd he (u _),decompose_far V _ _ _ hd he _ (v _),
    filedCrop122_sum, filedCrop122_C_mul, filedCrop122_sum,filedCrop122_C_mul,filedCropEq122]
  apply continuous_finsetSum; intro i _; apply (multipliers_cont u hu i).mul
  apply continuous_finsetSum; intro j _; apply (multipliers_cont v hv j).mul
  exact continuous_finsetSum _ fun k _ => (basis_cont phys hd he hz hs ht i j k).mul (hf.pow _)

lemma tariff_cont {z : X → Points n} (hz : Continuous z) (hs : ∀ x, z x ∈ conf n)
    (u : X → Appointed122Fields G d) (p : ℕ) {f : X → ℂ} (hf : Continuous f)
    (hu : ∀ i, Continuous fun x => account G (d i) (u x i)) (q : Q G) :
    Continuous (fun i => filedCrop122 p (f i) (tariff V (z i) (u i) q)) := by
  simp_rw [filedCropEq122, tariff, map_sum, coeff_C_mul]; apply continuous_finsetSum; intro i _
  apply Continuous.mul _ (hf.pow _); apply continuous_finsetSum; intro j _
  apply (multipliers_cont u hu j).mul; exact ((phys.far (labeling j)).2.1 q i).comp_continuous hz hs

lemma joint_cont {x : X → Points n} (cx : Continuous x) {y : X → Points m} (cy : Continuous y)
    {T : X → ℝ} (ct : Continuous T) (ht : ∀ i, 0 < T i)
    (hk : ∀ i, x i ∈ conf n) (u : X → Appointed122Fields G d) (v : X → Appointed122Fields G e) (p : ℕ)
    (lh : h ≤ H) {f : X → ℂ} (cf : Continuous f) (hT : ∀ i, forest (x i) (T i • y i) ∈ conf (n+m) ∧
      outgoing (T i • y i) ∈ conf (1+m))
    (hu : ∀ i, Continuous fun x => account G (d i) (u x i))
    (hv : ∀ i, Continuous fun x => account G (e i) (v x i)) :
    Continuous (fun i : X => jointY V B hd he (u i) (v i) p (f i) (T i) (x i) (y i)) ∧
    Continuous (fun i : X => jointD V B he (u i) (v i) p lh (f i) (T i) (x i) (y i)) := by
  have hg := ct.smul cy; have hw := ct.log (fun i => (ht i).ne')
  refine ⟨continuous_crop phys hd he (Enh.continual cx hg)
    (fun i => (hT i).1) hw u v p cf hu hv, ?_⟩
  simp_rw [jointD, crop_response_vector]
  apply continuous_finsetSum; intro q _
  exact Continuous.mul (tariff_cont phys cx hk u p cf hu _)
    (continuous_crop phys (d:=fun _ : Fin 1 => h) (fun _ => lh) he (Enh.continual continuous_const hg)
    (fun i => (hT i).2) hw (fun _ _ => theory q) v p cf (fun _ => continuous_const) hv)

end YM.FVA2.GradedFar
