import YM.FormalOPE.RG10.Capture.Profiles

/-!
# Announced horizon inputs as actual finite-volume "slots"

Global test language: represent actual addresses using the same physical test instance on every
anchor. `α` indexes those tests. (E.g. an address `u` with derivative letter `w` based at r is
evaluated against that very test's translated/scaled derivative at `u`, with the requisite
Nyquist/preimage/period convention, not silently moved along with anchor.) Root changes compose
on these encodings; kernel formulas for unmasked insertion on the *entire group* are still on
`Channel`. Include extra retained jets/lifts before collapsing to this view. Needed as a
literal finite-period encoding *adapter* for the producer's own periodic approximants to the
cover formal WilsonX calculation; no period identities with infinite sums from this type.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Finset Function Route Transit
open scoped Topology BigOperators Classical
variable {T U J : ℕ→Type} {X : Type} {α : Type*}

-- choose geometry giving L etc explicitly
structure Fibers (T : ℕ → Type) where
  parent : ∀ i,T (i+1)→ T i
abbrev Skin (T U : ℕ→Type) (α : Type*) (i : ℕ) := T i → α → Channel (U i)

def nominal (u : ℝ) := algebraMap ℂ Series (u:ℂ)
@[simp] lemma product_nom (u v : ℝ) : nominal (u*v)= nominal u*nominal v := by simp [nominal]
@[simp] lemma nominal_un : nominal 1=1 := by unfold nominal; simp
lemma nominal_mag {U : Type} (r : ℝ) (hr:0≤r) (v : U→ℝ) (n d) (x : Channel U) : mag v n d (nominal r • x)= r* mag v n d x := by unfold nominal; rw [tower, mag_smul]; simp [Real.norm_eq_abs, abs_of_nonneg hr]
lemma nominal_rcut (i j : ℕ) (r : ℝ) (h : j>i) : PowerSeries.coeff j (nominal r)=0 := by unfold nominal; simp [coeff_C,show j≠0 by omega]
-- volume factor in native units of root addressed data. spacing exponent four explicitly

def price (W : Scale X U) (h b i : ℕ) := nominal ((W.μ b/W.μ i)^h * (W.μ i)^4)

variable (F : Fibers T) [∀ i,Fintype (T i)] (φ : α) (W : Scale X U) (h b i : ℕ)
local notation "P₀" => price W h b

def fingerprint : Skin T U α i →ₗ[Series] Channel (U i) where
  toFun x := P₀ i • ∑ j : T i,x j φ
  map_add' x y := by simp [Finset.sum_add_distrib,smul_add]
  map_smul' c x := by
    change P₀ i • (∑ j,c • x j φ) = _; rw [← Finset.smul_sum]; exact smul_comm ..
local notation "a" => W.μ i
-- transmit L^h and average central preimages using next site volume factor
variable (V : Voyage U J) [∀ i,Fintype (J i)]

def upwards : Skin T U α (i+1) →ₗ[Series] Skin T U α i where
  toFun x := fun j t => nominal ((W.μ i/W.μ (i+1))^h*(W.μ (i+1)/W.μ i)^4) •
         ∑ k∈ Finset.univ.filter (fun k:T (i+1) => F.parent i k=j), (V.sail i).floats (x k t)
  map_add' x y := by ext j t k; dsimp only [Pi.add_apply]; simp [Finset.sum_add_distrib,smul_add]
  map_smul' c x := by
    funext j t; dsimp only [RingHom.id_apply,Pi.smul_apply]; simp_rw [(V.sail i).floats_smul,← Finset.smul_sum, smul_comm (nominal _)] -- check

/-- This is a transfer in the SAME field expansion operator, not just matrix consistency. No
position costs or root multiplicity assumptions in this equality. -/
theorem regroup (K : Skin T U α (i+1)) :
    fingerprint φ W h b i (upwards F W h i V K) = (V.sail i).floats (fingerprint φ W h b (i+1) K) := by
  let h' := W.μ (i+1)
  have h1 : 0<h':= W.positive _; have h2:= W.positive i
  let q:= ∑ k:T (i+1),(V.sail i).floats (K k φ)
  let r:ℝ:= (W.μ i / h')^h*(h'/W.μ i)^4
  have he : price W h b i*nominal r=price W h b (i+1):= by unfold price r; rw [← product_nom]; apply congr_arg nominal; change _=(W.μ b/h')^h*h'^4; simp_rw [div_pow]; field_simp; try ring -- inspect
  have ht : (∑ j : T i, upwards F W h i V K j φ) = nominal r • q := by
    unfold upwards; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [← Finset.smul_sum]; congr 1
    exact Finset.sum_fiberwise univ _ _
  change price W h b i • (∑ j,upwards F W h i V K j φ)= (V.sail i).floats (price W h b (i+1) • ∑ k:T (i+1), K k φ); rw [ht,smul_smul,he,(V.sail i).floats_smul, map_sum]
end YM.FormalOPE.RG10.Capture
