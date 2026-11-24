import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Subarrays
import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.PricedRows

/-!
# Even the output vector in (M.2) uses the same unit and padding conventions

Not needed to prove the inequality. Identify on the mass-independent book by
the FAR characterization (stock `honest`, with the probes interpreted before
cropping as above). No fresh payment required; no taking a UV limit in the
large-T estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set Scale O.Enh O.Score O.Read O.Canon PowerSeries Dframe
open XSpace XSpace.Normalize MS.Land
open scoped Classical Topology BigOperators Matrix
variable {G : Gauge} (N : Register.WilsonPrescription G)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {Sms : MS.Land.Prescription (Press.portDeck G)}
    {hG : G.Simple} (matched : Main.Match N hG M Sms true)
    {n m a b h k H : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}

local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "Z" => install V
local notation "B" => GroupS.gaugeN N.scheme N.criterion M (Teller.logNu 1)

lemma sheer {p : Test m} (f g : Points m → PowerSeries ℂ) (he : EqOn f g (CoverP p)) :
    smearing p f = smearing p g := by
  ext k; rw [smearing,smearing,coeff_mk, coeff_mk]; exact smear_price _ (fun x hx => by rw [he hx])

/-- Full formal measurement row against any detecting family at center 0
using the same layout for all probes. -/
def probes (t : ℝ) (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d)
    (Q : Geology G h) (lh : h ≤ H) (j : Toon G h) := ∑ i : Toon G h, smearing (Q j i).val fun y =>
      series V B (-t) (forest x (squeeze (-t) y)) hd (e:=fun _ : Fin 1 => h) (fun _ => lh) u (fun _ => theory i)

def quotePoint (t : ℝ) (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d)
    (Q : Geology G h) (lh : h ≤ H) := (Sheet B Z Q t)⁻¹ *ᵥ probes N (M:=M) t x hd u Q lh

include matched
lemma smear_word (t : ℝ) (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d)
    (Q : Geology G h) (lh : h ≤ H) (clear : Part t {x} Q) (i j : Toon G h) :
    smearing (Q j i).val (fun y => series V B (-t) (forest x (squeeze (-t) y)) hd
      (e:=fun _ : Fin 1 => h) (fun _ => lh) u (fun _ => theory i)) =
    ∑ w : Words G d, C (filedMultipliers122 u w) * smearing (Q j i).val
      (fun y => ShowT B Z t x (labeling w) y (LetterQ i)) := by
  let Q' := Q j i
  have hP w y := expand_show (matched.dilation (Teller.logNu 1)).check hd (fun _ : Fin 1 => lh) (matched.separatedOPE (Teller.logNu 1)).wilson.dimensions x y t
    (u:=w) (v:= fun _ => i)
  have hQ (w: Words G d) : draw Q'.val (fun y => ShowT B Z t x (labeling w) y (LetterQ i)) :=
    draw_once (indoors (matched.separatedOPE (Teller.logNu 1)).wilson.awake (clear j i) (LetterQ i)) (mem_singleton _)
  simp_rw [decompose_near _ _ _ _ _ _ u];
  change smearing _ (fun y => ∑ w : Words G d, C (filedMultipliers122 u w) *
    series V B (-t) (forest x (squeeze (-t) y)) hd (fun _ : Fin 1 => lh) (basisFields w)
      (basisFields (d:= fun _ : Fin 1 => h) (fun _ => i)))=_
  simp_rw [hP]; rw [smearing_sum]
  · exact Finset.sum_congr rfl fun i _ => smearing_mul _ (hQ i) _
  · intro i _; exact region _ (hQ i) _

lemma probe_step (t : ℝ) (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d)
    (Q : Geology G h) (lh : h ≤ H) (clear : Part t {x} Q) (i : Toon G h) :
    probes N (M:=M) t x hd u Q lh i =
      ∑ w : Words G d, C (filedMultipliers122 u w) * Perch B Z Q (labeling w) t x i := by
  unfold probes Perch; simp_rw [smear_word N matched _ _ _ _ _ _ clear]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun w _ => (Finset.mul_sum ..).symm)

lemma step_quote (t : ℝ) (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d)
    (Q : Geology G h) (lh : h ≤ H) (clear : Part t {x} Q) (b : Toon G h) :
    quotePoint N (M:=M) t x hd u Q lh b =
      ∑ w : Words G d, C (filedMultipliers122 u w) * QuoteShape B Z Q (labeling w) t x b := by
  simp_rw [quotePoint, QuoteShape, Matrix.mulVec,dotProduct, probe_step N matched _ _ _ _ _ _ clear, Finset.mul_sum]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..

lemma converge_quote (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d) (hx : x ∈ conf n)
    (Q : Geology G h) (det : Detected V Q) (lh : h ≤ H) (b : Toon G h) (k : ℕ) :
    Tendsto (fun t => coeff k (quotePoint N (M:=M) t x hd u Q lh b)) atTop
      (𝓝 (coeff k (tariff V x u (flash b)))) := by
  have hp (i : Words G d) := (honest (matched.dilation (Teller.logNu 1)).check (matched.separatedOPE (Teller.logNu 1)).wilson.dimensions (matched.separatedOPE (Teller.logNu 1)).wilson.awake isCompact_singleton (singleton_subset_iff.mpr hx)
    ((matched.separatedOPE (Teller.logNu 1)).wilson.far (labeling i)) det b k).tendsto_at (mem_singleton _)
  have he := tendsto_finsetSum Finset.univ fun i _ => (hp i).const_mul (filedMultipliers122 u i)
  unfold tariff; rw [map_sum]; simp_rw [coeff_C_mul]; apply he.congr'
  filter_upwards [life Q isCompact_singleton (singleton_subset_iff.mpr hx)] with t ht
  rw [step_quote N matched _ _ _ _ _ _ ht, map_sum]; simp_rw [coeff_C_mul]

variable (A : Fin a ↪ Fin n)
lemma same_probes (t : ℝ) (x : Points n) (hd : Covered d H) (u : Appointed122Fields G d) (hu : ∀ i : Fin n, i∉Set.range A → u i = leaf G (d i))
    (Q : Geology G h) (lh : h ≤ H) (clear : Part t {x} Q) :
    probes N (M:=M) t x hd u Q lh = probes N (M:=M) t (positions A x) (within_abbr A d hd) (fun i => u (A i)) Q lh := by
  funext i; unfold probes; apply Finset.sum_congr rfl; intro j _; apply sheer; intro y hy
  let E := Function.Embedding.refl (Fin 1)
  have e (y : Points 1) : positions E y = y := rfl
  dsimp only
  rw [series_select N matched A E (Teller.logNu 1) _ (clear i j x (mem_singleton _) y hy) _ hd _ u hu,
    projected,e]
  · rfl
  intro i h; exact False.elim (h ⟨i,rfl⟩)

omit matched in
lemma common_height (d : Fin n → ℕ) : Covered d (∑ i, d i) :=
  fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma tariff_erasure (x : Points n) (u : Appointed122Fields G d) (hu : ∀ i : Fin n, i∉Set.range A → u i = leaf G (d i))
    (hx : x ∈ conf n) (q : O.Score.Q G) :
    tariff V x u q = tariff V (d := d ∘ A) (positions A x) (fun i => u (A i)) q := by
  ext k
  let h := heft q; let H := max h (∑ i, d i); have lh : h ≤ H := le_max_left ..
  have hd : Covered d H := fun i => (common_height d i).trans (le_max_right ..)
  let b : Toon G h := O.Score.low q le_rfl
  obtain ⟨P,hp,det⟩ := (matched.separatedOPE (Teller.logNu 1)).wilson.light h
  have h₁ := converge_quote N matched x hd u hx P det lh b k
  have h₂ := converge_quote N matched (positions A x) (within_abbr A d hd)
    (fun i => u (A i)) (positions_conf A hx) P det lh b k
  have he := h₁.congr' (f₂:= fun t => coeff k (quotePoint N (M:=M) t (positions A x) (within_abbr A d hd) (fun i => u (A i)) P lh b))
    (by filter_upwards [life P isCompact_singleton (singleton_subset_iff.mpr hx)] with t ht; unfold quotePoint; rw [same_probes N matched A _ _ _ u hu _ _ ht])
  exact tendsto_nhds_unique he h₂

lemma vector_erasure (x : Points n) (u : Appointed122Fields G d) (hu : ∀ i : Fin n, i∉Set.range A → u i = leaf G (d i))
    (hx : x ∈ conf n) (h p : ℕ) (z : ℂ) :
    filedVector122 V x h p z u = filedVector122 V (d := d ∘ A) (positions A x) h p z (fun i => u (A i)) := by
  unfold filedVector122; simp_rw [tariff_erasure N matched A x u hu hx];

lemma quote_at_center (u : Sec G h) (t : ℝ) (Q : Geology G h) (det : Detected V Q) :
    quotePoint N (M:=M) t (0 : Points 1) (fun _ => le_refl h) (fun _ => u) Q le_rfl =
      fun i => C (coord i u) := by
  let W := B
  let f (i : Toon G h) := C (coord i u)
  let F := (matched.separatedOPE (Teller.logNu 1)).wilson
  let D := (matched.dilation (Teller.logNu 1)).check
  have hp : probes N (M:=M) t (0 : Points 1) (fun _ => le_refl h) (fun _ => u) Q le_rfl = Sheet W Z Q t *ᵥ f := by
    funext i
    have x (j b : Toon G h) (y : Points 1) : rowsResponse122 V B (-t) (outgoing (squeeze (-t) y)) h le_rfl (fun _ : Fin 1 => le_refl h) (fun _ => theory b) (theory j) =
      LongT W Z t (flash j) y (LetterQ b) := expand_long D (lh:=le_rfl) (fun _ : Fin 1 => le_refl h) F.dimensions y t j (fun _ => b)
    let g y := rowsResponse122 V B (-t) (outgoing (squeeze (-t) y)) h le_rfl (fun _ : Fin 1 => le_refl h)
    have split (b : Toon G h) (y : Points 1) : g y (fun _ => theory b) u = ∑ j : Toon G h, f j * LongT W Z t (flash j) y (LetterQ b) := by
      unfold g; conv_lhs => rw [← all_sig u]
      rw [response_sum]; simp_rw [x]; rfl
    change ∑ b : Toon G h, smearing (Q i b).val (fun y => g y (fun _ => theory b) u) = _
    unfold Matrix.mulVec dotProduct
    have draw' b (j : Toon G h) : draw (Q i b).val (fun y => LongT W Z t (flash j) y (LetterQ b)) := forever (t:=t) D F.awake F.dimensions (flash j) (LetterQ b) _
    have w b : smearing (Q i b).val (fun y => g y (fun _ => theory b) u)=
      ∑ j : Toon G h, f j * smearing (Q i b).val (fun y => LongT W Z t (flash j) y (LetterQ b)) := by
      simp_rw [split, smearing_sum _ Finset.univ (fun j _ => region _ (draw' b j) (f j)), smearing_mul _ (draw' b _)]
    simp_rw [w, Sheet, Finset.sum_mul]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => mul_comm ..
  unfold quotePoint; rw [hp,Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (sealed_t D F.awake F.dimensions det)), Matrix.one_mulVec]

lemma tariff_at_center (u : Sec G h) (j : Toon G h) :
    tariff V (d:=fun _ : Fin 1 => h) 0 (fun _ => u) (flash j) = C (coord j u) := by
  ext k; obtain ⟨P,_,det⟩ := (matched.separatedOPE (Teller.logNu 1)).wilson.light h
  refine tendsto_nhds_unique (converge_quote N matched (0 : Points 1) (fun _ => le_refl h) (fun _ => u)
    (Function.injective_of_subsingleton _) P det le_rfl j k) ?_
  simp_rw [quote_at_center N matched u _ _ det]
  exact tendsto_const_nhds

theorem vector_center (u : Sec G h) (p : ℕ) (z : ℂ) :
    filedVector122 V (d:=fun _ : Fin 1 => h) 0 h p z (fun _ => u)=u := by
  apply (account G h).injective; funext i
  rw [account_entry, account_entry, vector_entry, tariff_at_center N matched]; simp [filedCrop122]

theorem vector_empty (x : Points 0) {d : Fin 0 → ℕ} (u : Appointed122Fields G d) (h p : ℕ) (z : ℂ) :
    filedVector122 V x h p z u = leaf G h := by
  let e := (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 1)
  let d' := (fun _ : Fin 1 => h) ∘ e
  let u' : Appointed122Fields G d' := fun _ => leaf G h
  have h' (u : Appointed122Fields G d') : filedVector122 V x h p z u = leaf G h := by
    have hx : positions e (0:Points 1) = x := by ext1 i; exact i.elim0
    rw [show u=u' from funext fun i => i.elim0, ← hx, ← vector_center N matched (leaf G h) p z,
      vector_erasure N matched e 0 (fun _ => leaf G h) (d:=fun _ => h)
      (fun _ _ => rfl) (Function.injective_of_subsingleton _)]
  have hv : d = d' := funext fun i => i.elim0
  subst d; exact h' u
end YM.FVA2.GradedFar

