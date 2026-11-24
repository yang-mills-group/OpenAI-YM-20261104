import YM.GradedFar.Moving.Direction

/-!
# Consume prepared orientation at these compact estimation steps
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "K"=> Kseries N M
local notation "B"=> GroupS.gaugeN N.scheme N.criterion M ν
local notation "ψ"=> GroupS.ψ N.criterion M ν
open Reg.Point (stepV)
-- W confines. Negative/zero s allowed since Z constant of structure. Signed-axis convention preserved.
abbrev Rolled (G : Gauge) (d : ℕ) := ℝ→ℝ→(Sec G d≃ₗ[ℂ] Sec G d)
-- represents *actual* W_r^-1 W_{r exp(s)}
abbrev forwards (Z : Rolled G d) (r s : ℝ) := (Z r s).toLinearMap
abbrev inverseZ (Z : Rolled G d) (r s : ℝ) := (Z r s).symm.toLinearMap
abbrev Zenith (Z : Rolled G d): Coven G d := fun r s => chairs G d (forwards Z r s)
abbrev downward (Z : Rolled G d): Coven G d := fun r s => chairs G d (inverseZ Z r s)
lemma tilted_on (Z : Rolled G d) (r s : ℝ) : forwards Z r s * inverseZ Z r s =1 := by ext1 u; exact LinearEquiv.apply_symm_apply ..
lemma tilted_out (Z : Rolled G d) (r s : ℝ) : inverseZ Z r s * forwards Z r s=1 := by ext1 u; exact LinearEquiv.symm_apply_apply ..
lemma inverse_ok (Z : Rolled G d) (r s : ℝ) : Zenith Z r s * downward Z r s=1 ∧ downward Z r s*Zenith Z r s=1 := by unfold Zenith downward; rw [← chairs_mul, tilted_on,← chairs_mul, tilted_out,chairs_one]; exact ⟨rfl,rfl⟩
lemma nearby_right (A V : I→Maps G d) (h : Tendsto (fun i=> A i-1) T (𝓝 0)) (hv : ∀ i, A i*V i=1 ∧ V i*A i=1) :
    Tendsto (fun i=> V i-1) T (𝓝 0) := by
    have h0 : Tendsto A T (𝓝 1):= by simpa only [sub_add_cancel,zero_add] using h.add (tendsto_const_nhds (x:=1))
    let U i : (Maps G d)ˣ:= ⟨A i,V i,(hv i).1,(hv i).2⟩
    have he : Tendsto (fun i=> (↑((U i)⁻¹): Maps G d)) T (𝓝 1) := by
      have hn:= (NormedRing.inverse_continuousAt (1:(Maps G d)ˣ)).tendsto.comp h0
      simp_rw [Ring.inverse_unit] at hn
      refine hn.congr ?_
      intro i; change Ring.inverse (↑(U i) : Maps G d)= _; rw [Ring.inverse_unit]
    change Tendsto V T (𝓝 1) at he
    simpa only [sub_self] using he.sub_const (1:Maps G d)

/-- Frame uses a single operator `Z`, from W_r^-1W_s. Its leading relation and
orientation are in `Righted`; ratio z ∈ [0,log2]. These predicates will be purchased.
-/
def probe := ℝ × (↥Growth.Small)
abbrev filed := comap (Prod.fst : ℝ × (↥Growth.Small)→ℝ) τ
-- eventually in filed is ∀ small s, all r, etc.
def Righted (Z : Rolled G d) :=
    (∀ᶠ r in τ,∀ z∈Growth.Small, permissible (forwards Z r z)) ∧
    Tendsto (fun i : ℝ × (↥Growth.Small)=> Zenith Z i.1 i.2.val * engine G d (-i.2.val) - 1) filed (𝓝 0)

def refit (Z : Rolled G d) (F : Pose.Plans G d) := ∀ (r s : ℝ), 0<r → s∈ Growth.Small → ∀ (n : ℕ) (v : Fin n→Sec G d) (x : Points n),
    x∈conf n → F (resize r s) n x v= F r n (exp s • x) (forwards Z r s∘v)
-- true orientation of rows with same field pose; remember r-home. No assuming any tolerance of a substitute pose.
variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ i,z i∈Growth.Small) {simple : G.Simple}
    {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
    {Z : Rolled G d} (hZ : Righted Z)
include hr hz hZ H
lemma tight : Tendsto (fun i => Zenith Z (r i) (z i)*engine G d (-z i)-1) T (𝓝 0) := by
    let u (i : I) : ℝ × (↥Growth.Small) := (r i,⟨z i,hz i⟩)
    have h : Tendsto u T filed := tendsto_comap_iff.mpr hr
    have hu := hZ.2.comp h; exact (And.intro hu (Nonempty.intro H)).1
lemma tight' : Tendsto (fun i=> engine G d (z i) * downward Z (r i) (z i) - 1) T (𝓝 0) := by
  apply nearby_right T _ _ (tight T N M r z hr hz H hZ)
  intro i; constructor
  · rw [mul_assoc, ← mul_assoc (engine G d _),← engine_sum, neg_add_cancel,engine_zero,one_mul,(inverse_ok ..).1]
  rw [mul_assoc,← mul_assoc (downward Z (r i) (z i)) _, (inverse_ok ..).2, one_mul,← engine_sum,add_neg_cancel,engine_zero]
lemma weak_bound : Buys T (fun i=> downward Z (r i) (z i)) (g∘r) 0 := by
  let F i:= engine G d (-z i)
  let U i:= engine G d (z i) * downward Z (r i) (z i)
  have he : Buys T F (g∘r) 0 := budget T (Eventually.of_forall fun i=> engine_neg_bound _ (neg_nonpos.mpr (hz i).1) d)
  have hP : Buys T U (g∘r) 0 := by
    have hu: Tendsto U T (𝓝 1):= by simpa only [U,zero_add,sub_add_cancel] using (tight' T N M r z hr hz H hZ).add (tendsto_const_nhds (x:=1))
    apply budget T ((hu.norm.eventually_lt_const (lt_add_one _)).mono fun _ h=>h.le)
  refine (times_cost T he hP).congr_left (fun i=>?_)
  unfold F U; rw [←mul_assoc,← engine_sum,neg_add_cancel,engine_zero,one_mul]
lemma soft_engine : Buys T (fun i=>engine G d (z i)) (g∘r) 0 := by
    apply budget T (C:=(exp doubling)^d); filter_upwards with i
    exact (And.intro ((engine_pos_bound _ (hz i).1 d).trans (pow_le_pow_left₀ (exp_pos _|>.le) (Real.exp_le_exp.mpr (hz i).2) _)) (And.intro hr (And.intro hZ (Nonempty.intro H)))).1
lemma weak_bound_out : Buys T (fun i=>Zenith Z (r i) (z i)) (g∘r) 0 := by
  let U i:= Zenith Z (r i) (z i)*engine G d (-z i)
  have hP : Buys T U (g∘r) 0 := by
    have hu: Tendsto U T (𝓝 1):= by simpa only [U,zero_add,sub_add_cancel] using (tight T N M r z hr hz H hZ).add (tendsto_const_nhds (x:=1))
    apply budget T ((hu.norm.eventually_lt_const (lt_add_one _)).mono fun _ h=>h.le)
  refine (times_cost T hP (soft_engine T N M r z hr hz H hZ)).congr_left (fun i=>?_); unfold U; rw [mul_assoc,← engine_sum,neg_add_cancel,engine_zero,mul_one]

omit hr hz hZ H in
lemma bounded_and_vanish {E : Type} [NormedRing E] {t : I→ℝ}{V U : I→E}
    (hu : Buys T U t 0) (hv : Tendsto V T (𝓝 0)) : Tendsto (fun i=> U i*V i) T (𝓝 0) ∧ Tendsto (fun i=> V i*U i) T (𝓝 0) := by
    obtain ⟨C,hC,h⟩:=hu.exists_pos
    have he:Tendsto (fun i=> C*‖V i‖) T (𝓝 0):= by simpa only [norm_zero,mul_zero] using hv.norm.const_mul C
    constructor
    · refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ he)
      filter_upwards [h.bound] with i hi; rw [pow_zero,norm_one,mul_one] at hi
      exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ he)
    filter_upwards [h.bound] with i hi; rw [pow_zero,norm_one,mul_one] at hi
    exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left hi (norm_nonneg _)).trans_eq (mul_comm ..))

variable (θ : ℝ→ℝ) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1))
abbrev compareZ (Z : Rolled G d) (p : ℕ) (r z : ℝ) := inverseZ Z r z * ray N M θ z r p d
include ht
lemma sensed_op : Tendsto (fun i=> chairs G d (compareZ N M θ Z p (r i) (z i) - 1)) T (𝓝 0) := by
    let V i:= Zenith Z (r i) (z i); let U i:= downward Z (r i) (z i); let A i:= chairs G d (ray N M θ (z i) (r i) p d); let E i:= engine G d (z i)
    have hV : Tendsto (fun i=> V i-E i) T (𝓝 0) := by
      refine (bounded_and_vanish _ (soft_engine T N M r z hr hz H hZ) (tight T N M r z hr hz H hZ)).2.congr (fun i=>?_)
      unfold V E; rw [sub_mul,one_mul,mul_assoc,← engine_sum,neg_add_cancel,engine_zero,mul_one]
    have hB:=collapses T N M r hr H (base_at T N M r z hr (Eventually.of_forall hz) H θ ht p d) le_rfl
    have hA : Tendsto (fun i=>A i-V i) T (𝓝 0):= by
      have hv:= hB.sub hV; rw [sub_zero] at hv; apply hv.congr; intro i; unfold V A E ray; abel
    refine (bounded_and_vanish T (weak_bound T N M r z hr hz H hZ) hA).1.congr (fun i=>?_)
    unfold compareZ A V; rw [map_sub (chairs G d),chairs_one,chairs_mul,mul_sub]; change _-downward Z (r i) (z i)* Zenith Z (r i) (z i)= _
    rw [(inverse_ok ..).2]
end
end YM.FVA2.GradedFar.Moving
