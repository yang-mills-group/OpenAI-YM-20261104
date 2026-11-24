import YM.Integration.MSFiniteReceiverMatrix
import YM.Integration.MSDeckProbeGram

/-! Recover the strictly lower engineering rows of an arbitrary paid
field from its genuine rectangular high-versus-low two-point matrix. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.MSMeasuredEngineering

open Function Filter Matrix FVA2 MS MS.Local.Physical MS.Menus MS.Land MS.Dial MSPhysicalDeckChange
open MSMeasuredFeeField MSFiniteReceiverMatrix MSCutoffGerms MSMeasuredGermSeries
open scoped Topology Classical BigOperators

variable {G : Gauge} {A B : Deck G} {I : Type} {J K L : Type*} {l : Filter I}
variable (V : Warehouse G) (P : Prescription A) (E : Fees B A) (T : Trial I (Fin 2)) (μ : ℝ)
variable (ht : Tendsto T.profile.θ l atTop)

def cast (ht : Tendsto T.profile.θ l atTop) := PowerSeries.map (ring ht).subtype

def gather (F : I → Matrix J K (PowerSeries ℂ)) : Matrix J K (PowerSeries (Germ l ℂ)) :=
  fun a b => diagram l (fun i => F i a b)

theorem add (a b : I → Matrix J K (PowerSeries ℂ)) :
    gather (l := l) (fun i => a i + b i) = gather a + gather b := by
  apply Matrix.ext
  intro i j
  exact map_add (diagram l) (fun s => a s i j) (fun s => b s i j)

theorem multiply [Fintype K] (f : I → Matrix J K (PowerSeries ℂ))
    (g : I → Matrix K L (PowerSeries ℂ)) :
    gather (l := l) (fun i => f i * g i) = gather f * gather g := by
  apply Matrix.ext
  intro i j
  change diagram l (fun s => ∑ k, f s i k*g s k j) =
    ∑ k, diagram l (fun s => f s i k) * diagram l (fun s => g s k j)
  have he : (fun s => ∑ k, f s i k*g s k j) =
      ∑ k : K, (fun s => f s i k)*(fun s => g s k j) := by
    funext s
    rw [Finset.sum_apply]
    rfl
  rw [he, map_sum]
  simp only [map_mul]

theorem lift_entries (f : I → Matrix J K (PowerSeries ℂ))
    (hf : ∀ a b, ∀ k, Moderate l T.profile.θ (fun i => PowerSeries.coeff k (f i a b))) :
    ∃ q : Matrix J K (PowerSeries (ring ht)), q.map (cast T ht) = gather f := by
  refine ⟨fun a b => stored ht (fun i => f i a b) (hf a b), ?_⟩
  apply Matrix.ext
  exact fun a b => exposed ht (fun i => f i a b) (hf a b)

theorem lift_converges (f : I → Matrix J K (PowerSeries ℂ))
    (hf : ∀ a b k, ∃ z : ℂ, Tendsto (fun i => PowerSeries.coeff k (f i a b)) l (𝓝 z)) :
    ∃ q : Matrix J K (PowerSeries (ring ht)), q.map (cast T ht) = gather f := by
  apply lift_entries T ht
  intro a b k
  obtain ⟨_, h⟩ := hf a b k
  exact convergent ht h

def align (h : ℕ) := (MSFiniteReceiverMatrix.identification A B h).symm

def lowChange (h : ℕ) (i : I) :=
  (matrix P E h μ (T.profile.θ i)).submatrix (align (A := A) (B := B) h) id

def donor (h : ℕ) (i : I) :=
  (target V P E h T μ i).submatrix (align (A := A) (B := B) h) (align (A := A) (B := B) h)

def cutting (h : ℕ) (i : I) :=
  (highData V P E h T μ i).submatrix id (align (A := A) (B := B) h)

private theorem reindex_pair {R : Type*} [Semiring R] [Fintype J] (e : J → K)
    (U : Matrix K J R) (Z : Matrix J J R) :
    (U * Z * U.transpose).submatrix e e = U.submatrix e id * Z * (U.submatrix e id).transpose := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]

private theorem reindex_edge {R : Type*} [Semiring R] [Fintype J] (e : J → K)
    (U : Matrix K J R) (Z : Matrix L J R) :
    (Z * U.transpose).submatrix id e = Z * (U.submatrix e id).transpose := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]

theorem lower_match (h : ℕ) :
    gather (l := l) (donor V P E T μ h) =
      gather (lowChange P E T μ h) * gather (source V P h T μ) *
        (gather (lowChange P E T μ h)).transpose := by
  have w (i : I) : donor V P E T μ h i = lowChange P E T μ h i * source V P h T μ i *
      (lowChange P E T μ h i).transpose := by
    let e := align (A := A) (B := B) h
    exact (congrArg (fun X : Matrix (Glyph B h) (Glyph B h) (PowerSeries ℂ) => X.submatrix e e)
      (MSFiniteReceiverMatrix.measured V P E h T μ i)).trans (reindex_pair e _ _)
  rw [show donor V P E T μ h = _ from funext w]
  rw [multiply, multiply]
  rfl

theorem upper_match (h : ℕ) :
    gather (l := l) (cutting V P E T μ h) =
      (gather (l := l) (fun i => lowerPort P E h μ (T.profile.θ i)) * gather (l := l) (source V P h T μ) +
      gather (l := l) (fun i => samePort P E h μ (T.profile.θ i)) * gather (l := l) (lowData V P h T μ)) *
      (gather (l := l) (lowChange P E T μ h)).transpose := by
  have w (i : I) : cutting V P E T μ h i =
      (lowerPort P E h μ (T.profile.θ i) * source V P h T μ i +
       samePort P E h μ (T.profile.θ i) * lowData V P h T μ i) * (lowChange P E T μ h i).transpose := by
    let e := align (A := A) (B := B) h
    exact (congrArg (fun X : Matrix (Plaid B (h+1)) (Glyph B h) (PowerSeries ℂ) => X.submatrix id e)
      (MSFiniteReceiverMatrix.rectangle V P E h T μ i)).trans (reindex_edge e _ _)
  rw [show cutting V P E T μ h = _ from funext w]
  rw [multiply, add, multiply, multiply]
  rfl

/-- The two legitimate measured square matrices are units by their
true Maxwell heads. All high and low observations in the result are
the concrete finite Wilson fees from the fixed Trial. -/
theorem excludes [NeBot l] (h : ℕ)
    (u a b : Matrix (Glyph A h) (Glyph A h) (PowerSeries (ring ht)))
    (hu : u.map (cast T ht) = gather (lowChange P E T μ h))
    (ha : a.map (cast T ht) = gather (source V P h T μ)) (ua : IsUnit a.det)
    (hb : b.map (cast T ht) = gather (donor V P E T μ h)) (ub : IsUnit b.det)
    (hs : ∀ v w k, ∃ z : ℂ, Tendsto (fun i => PowerSeries.coeff k (lowData V P h T μ i v w)) l (𝓝 z))
    (hr : ∀ v w k, ∃ z : ℂ, Tendsto (fun i => PowerSeries.coeff k (cutting V P E T μ h i v w)) l (𝓝 z)) :
    ∀ (b : Plaid B (h+1)) (a : Glyph A h), raw P E (Land.read b) a = 0 := by
  let f := cast T ht
  have hfi : Injective f := PowerSeries.map_injective (ring ht).subtype (ring ht).subtype_injective
  have hL : b = u*a*u.transpose := by
    apply MSGradedReceiverRigidity.same f hfi
    rw [hb, lower_match, ←hu, ←ha, Matrix.map_mul, Matrix.map_mul]
    rfl
  obtain ⟨d, hd⟩ := lift_entries T ht (fun i => samePort P E h μ (T.profile.θ i))
    (fun v w k => by
      change Moderate _ _ (fun i => PowerSeries.coeff k (charged P E μ (T.profile.θ i) (Land.read v) (Land.read w)))
      simp only [same_grade P E μ (Land.read v) (Land.read w) _ k rfl]
      exact polynomial ht μ _)
  obtain ⟨k, hk⟩ := lift_converges T ht _ hs
  obtain ⟨m, hm⟩ := lift_converges T ht _ hr
  let x := gather (l := l) (fun i => lowerPort P E h μ (T.profile.θ i))
  have hx : m.map f = (x * a.map f + (d*k).map f) * u.transpose.map f := by
    change m.map (cast T ht) = _
    rw [hm, upper_match, ←ha, ←hu, ←hd, ←hk, Matrix.map_mul]
    rfl
  obtain ⟨y, hy⟩ := MSGradedReceiverRigidity.rectangle f u a b hL ub ua d k m x hx
  intro v w
  exact extinguish P E ht μ (Land.read v) w (Nat.lt_succ_of_le (MSFeeCoordinates.remaining w))
    (y v w) (congrFun (congrFun hy v) w)

def limiting {C : Deck G} {Q : Booked C} (M : MS_Data G Q) (h : ℕ) (p q : E4) (μ : ℝ) :
    Matrix (Glyph C h) (Glyph C h) (PowerSeries ℂ) :=
  fun a b => PowerSeries.mk fun k => MSDeckProbeGram.matrix M h p q μ k a b

/-- The only scalar hypotheses are the actual coefficient limits at one
genuine pair. They are supplied simultaneously by the independently
paid and canonical removal theorems. -/
theorem grading [NeBot l] (ht : Tendsto T.profile.θ l atTop) {QA : Booked A} {QB : Booked B}
    (D : MS_Data G QA) (S : MS_Data G QB) {p q : E4} (hp : p ≠ q)
    (hs : ∀ h (a b : Glyph A h) k, Tendsto
      (fun i => PowerSeries.coeff k (source V P h T μ i a b)) l
      (𝓝 (MSDeckProbeGram.matrix D h p q μ k a b)))
    (hr : ∀ h (a b : Glyph B h) k, Tendsto
      (fun i => PowerSeries.coeff k (target V P E h T μ i a b)) l
      (𝓝 (MSDeckProbeGram.matrix S h p q μ k a b))) :
    ∀ h d (b : Glyph B h) (a : Glyph A d), b.size ≠ a.size → raw P E b a = 0 := by
  classical
  have horizon (h : ℕ) :
      ∀ (b : Glyph B h) (a : Glyph A h), b.size ≠ a.size → raw P E b a = 0 := by
    induction h with
    | zero =>
      intro b a he
      have hb := MSFeeCoordinates.remaining b
      have ha := MSFeeCoordinates.remaining a
      omega
    | succ h ih =>
      have hl (a b : Glyph A h) (k : ℕ) :
          Moderate l T.profile.θ (fun i => PowerSeries.coeff k (lowChange P E T μ h i a b)) := by
        let v := align (A := A) (B := B) h a
        change Moderate l T.profile.θ (fun i => PowerSeries.coeff k (charged P E μ (T.profile.θ i) v b))
        by_cases e : v.size = b.size
        · simp only [same_grade P E μ v b _ k e]
          exact polynomial ht μ _
        · have z := ih v b e
          simp only [charged, z, map_zero, mul_zero]
          exact convergent ht tendsto_const_nhds
      obtain ⟨u, hu⟩ := lift_entries T ht (lowChange P E T μ h) hl
      let ZA := limiting D h p q μ
      let ZB := (limiting S h p q μ).submatrix (align (A := A) (B := B) h) (align (A := A) (B := B) h)
      have a' (a b : Glyph A h) (k : ℕ) : Tendsto
          (fun i => PowerSeries.coeff k (source V P h T μ i a b)) l (𝓝 (PowerSeries.coeff k (ZA a b))) :=
        by simpa only [ZA, limiting, PowerSeries.coeff_mk] using hs h a b k
      have b' (a b : Glyph A h) (k : ℕ) : Tendsto
          (fun i => PowerSeries.coeff k (donor V P E T μ h i a b)) l (𝓝 (PowerSeries.coeff k (ZB a b))) :=
        by simpa only [ZB, limiting, Matrix.submatrix_apply, donor, PowerSeries.coeff_mk] using hr h (align h a) (align h b) k
      let a := bank ht (source V P h T μ) ZA a'
      let b := bank ht (donor V P E T μ h) ZB b'
      have ha : a.map (cast T ht) = gather (source V P h T μ) := by
        apply Matrix.ext
        exact fun i j => exposed ht _ (fun k => convergent ht (a' i j k))
      have hb : b.map (cast T ht) = gather (donor V P E T μ h) := by
        apply Matrix.ext
        exact fun i j => exposed ht _ (fun k => convergent ht (b' i j k))
      have ua := MSMeasuredGermSeries.measured ht (source V P h T μ) ZA a'
        (MSDeckProbeGram.invertible V D μ hp h)
      have zb : IsUnit ((PowerSeries.constantCoeff (R := ℂ)).mapMatrix ZB) :=
        (MSDeckProbeGram.invertible V S μ hp h).map
          (Matrix.reindexRingEquiv ℂ (MSFiniteReceiverMatrix.identification A B h))
      have ub := MSMeasuredGermSeries.measured ht (donor V P E T μ h) ZB b' zb
      have drop := excludes V P E T μ ht h u a b hu ha ua hb ub
        (fun v w k => ⟨_, hs (h+1) (Land.read v) (MSFeeCoordinates.extend (Nat.le_succ h) w) k⟩)
        (fun v w k => ⟨_, hr (h+1) (Land.read v)
          (MSFeeCoordinates.extend (Nat.le_succ h) (align h w)) k⟩)
      intro v w hd
      by_cases hw : v.size < w.size
      · exact above P E v w hw
      have we : w.size ≤ h := by
        have hv := MSFeeCoordinates.remaining v
        omega
      by_cases hv : v.size ≤ h
      · exact ih (MSFeeCoordinates.restrict v hv) (MSFeeCoordinates.restrict w we) hd
      obtain ⟨j, hj⟩ : ∃ j : Plaid B (h+1), Land.read j = v := by
        rcases v with ⟨⟨r, hR⟩, j⟩
        have eq : r = h+1 := by
          change ¬ r ≤ h at hv
          omega
        subst r
        exact ⟨j, rfl⟩
      subst v
      exact drop j (MSFeeCoordinates.restrict w we)
  intro h d b a ne
  exact horizon (max h d) (MSFeeCoordinates.extend (Nat.le_max_left h d) b)
    (MSFeeCoordinates.extend (Nat.le_max_right h d) a) ne

end YM.Integration.MSMeasuredEngineering
