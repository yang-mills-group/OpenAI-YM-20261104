import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Accounting
import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Amortize
/-! # Receive the three price inputs *on the same comparison*: quantitative M.2 to M.3.

Analytic filter lemma for use also on the real operands (`D : Sec G h →ₗ[ℂ] ℂ`,
and `c_W^h` the packet in same frame). No hidden inverse norm assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {I : Type*} {n m h z : ℕ} {V : Arenas G} {B : ℝ → Frames G} {R : ℝ → PowerSeries ℂ}
    (L : Law V R B) (P : O.Canon.Physical V R B) {X : Filter I}

/-- The functional readout at the center (same Far normalization as Y). -/
def predicted (V : Arenas G) (B : ℝ→ Frames G) {e : Fin m→ℕ} (he : ∀ j,e j≤z)
    (hh : h ≤ z) (y : Points m) (η : ℝ) (v : Slots G e) (p : ℕ) (t : ℝ) : Sec G h →ₗ[ℂ] ℂ :=
  ∑ k∈Finset.range (p+1), (t:ℂ)^k • centerCoeff V B he hh y η v k

lemma center_read {e : Fin m→ℕ} (he : ∀ j,e j≤z) (hh : h ≤ z) (y v η p t) (f : Sec G h) :
    predicted V B he hh y η v p t f = crop p t (center V B he y hh η f v) := by
  unfold predicted; rw [LinearMap.sum_apply,crop_apply]; refine Finset.sum_congr rfl fun j _=>?_
  rw [center,measurement,coeff_mk]; rfl

/-- norm convention on linear functional on Sec's coefficient-sup unit ball (can use as
an upper bound on any of the individual readings; fixed-horizon norm-equivalence conventions).
Using even the sum, includes orientation/unit coefficients without special casing. -/
def opCost (A : Sec G h →ₗ[ℂ] ℂ) : ℝ := ∑ j : Toon G h, ‖A (theory j)‖
lemma opPos (A : Sec G h →ₗ[ℂ] ℂ) : 0 ≤ opCost A := Finset.sum_nonneg (fun i _ =>norm_nonneg _)
lemma opBound (A : Sec G h →ₗ[ℂ] ℂ) (u : Sec G h) (C : ℝ) (hc : ∀ i, ‖coord i u‖ ≤ C) :
    ‖A u‖ ≤ C * opCost A := by
  rw [← all_sig u,map_sum]; unfold opCost; rw [ Finset.mul_sum]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro j _; rw [_root_.map_smul, norm_smul]; exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)

/-- Pay even if using all the coordinates simultaneously for different profiles. -/
lemma costed {A : I → Sec G h →ₗ[ℂ] ℂ} {T f : I→ℝ} (hT : ∀ᶠ i in X, 1 ≤ T i)
    (h : ∀ i,Fare T X f (fun j=> A j (theory i))) : Fare T X f (fun i=>opCost (A i)) := by
  refine Fare.sum hT fun j _=>?_ ; obtain ⟨C,h⟩ := h j; exact ⟨C, isBigO_norm_left.mpr h⟩
lemma component_pay {A : I → Sec G h →ₗ[ℂ] ℂ} {f : I→ℝ}
    (H : (fun i=>opCost (A i))=O[X] f) (b : Toon G h) :
    (fun j=> A j (theory b))=O[X] f := by
  refine (IsBigO.of_bound' ?_).trans H
  refine Eventually.of_forall fun i=>?_ ; rw [Real.norm_of_nonneg (opPos _)]
  exact Finset.single_le_sum (f:=fun j=> ‖A i (theory j)‖) (fun x (_: x∈(Finset.univ:Finset (Toon G h)))=>norm_nonneg _) (Finset.mem_univ b)

section Bought
include P
lemma crop_bound {d: Fin n→ℕ} (q : Q G) {U : ℝ} (hU : 0≤U) (p : ℕ) {K:Set (Points n)}
    (hK : IsCompact K) (hk : K ⊆ conf n) :
    ∃ M : ℝ, ∀ u ∈ Balls U G d, ∀ t:ℝ, |t| ≤ 1 → ∀ x ∈ K, ‖crop p t (farCf V u x q)‖ ≤ M := by
  let I := ↥(Balls U G d) × ↥K
  choose M hM using fun k : ℕ => through_horizon hU P hK hk (r:=fun i:I=>i.1.val) (fun i=>i.1.property)
    (x:=fun (i:I)=>i.2.val) (fun i=>i.2.property) q k
  refine ⟨∑ j∈Finset.range (p+1), M j,fun u hu t ht x hx=>?_⟩
  rw [crop_apply]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=> ?_
  rw [norm_mul,norm_pow,Complex.norm_real]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht)).trans (hM i (⟨u,hu⟩,⟨x,hx⟩))
end Bought

-- Write the exact scalar outputs for easier use at every viewer separately or all viewers at once.
-- Works hfloor varying tests. (No proof below of the physical G.6 budget.)
def checkPrice (Y YX : ℂ) (D DX : Sec G h →ₗ[ℂ] ℂ) (packet c : Sec G h) : ℝ :=
  ‖Y-YX‖ + opCost (D-DX) + ‖Y-YX - (D-DX) c‖ + ‖Y-D packet‖ + ‖Y-D c‖
lemma checkPos (Y YX : ℂ) (D DX : Sec G h →ₗ[ℂ] ℂ) (packet c : Sec G h) :
    0 ≤ checkPrice Y YX D DX packet c := by unfold checkPrice; have h:=opPos (D-DX); positivity

variable {r g T t : I→ℝ} (ht : Tendsto g X (𝓝[>] 0)) (hl : ∀ a:ℝ,r =O[X] fun i=>g i^a)
    (hc : ∀ᶠ i in X, |t i| ≤ 1) (paid : ∀ᶠ i in X, |t i| ≤ 2*g i) {b : ℝ} (hb : 0<b)
    (H : T =Θ[X] fun i=>g i ^ (-b)) {W U : ℝ} (floor : ∀ᶠ i in X, W ≤ T i) (hW : 1 ≤ W)
    (hU : 0 ≤ U) {K:Set (Points n)} {S:Set (Points m)}
    (hK : IsCompact K) (hk : K⊆conf n) (hS : IsCompact S) (hs : S⊆Outside m) (hz : clears W K S)
    {x : I→Points n} {y : I→Points m} (hx : ∀ᶠ i in X,x i∈K) (hy : ∀ᶠ i in X,y i∈S)
    {d : Fin n→ℕ} {e : Fin m→ℕ} (hd : ∀ i,d i ≤ z) (he : ∀ i,e i ≤ z) (hh : h ≤ z)
    {u : I → Slots G d} {v : I → Slots G e} (hu : ∀ᶠ i in X,u i∈Balls U G d) (hv : ∀ᶠ i in X,v i∈ Balls U G e)
    {η : ℝ} (q p : ℕ)
local notation "YY" => (fun i : I => crop p (t i) (measurement V B hd he (x i) (T i • y i) (-Real.log (T i)) (u i) (v i)))
local notation "DD" => (fun i:I => predicted V B he hh (T i • y i) (-Real.log (T i)) (v i) p (t i))
local notation "cost" => (fun i:I => T i^(∑ j,e j)*g i^(p+1))
local notation "cc" => (fun i:I=> purchased V (u i) (x i) h p (t i))

include ht hl L P H hc paid hb floor hW hU hK hk hS hs hz hx hy hu hv

lemma summary (Y : I→ℂ) (D : I→ Sec G h →ₗ[ℂ] ℂ) (A : I→ Sec G h)
    (hY : Fare T X cost (fun i=> Y i - YY i)) (hD : Fare T X cost (fun i=> opCost (D i - DD i)))
    (D₀ : ℕ) (h₀ : (fun i=> Y i - D i (A i)) =O[X] fun i=> ((g i)⁻¹)^D₀*( r i * T i + ((T i)⁻¹)^(h+1)))
    (hPc : (q:ℝ)+b*((↑(∑ j,e j):ℝ)+h+η)+1 ≤ p+1) (hS : (q:ℝ)+D₀+1 ≤ b*(1-η)) :
    (fun i=> checkPrice (Y i) (YY i) (D i) (DD i) (A i) (cc i)) =O[X] margin q h η g T := by
  let m := margin q h η g T
  have hT := floor.mono fun i hi=> hW.trans hi
  have hgY := turns ht hT hb H _ _ _ _ hPc hY
  have hgD := turns ht hT hb H _ _ _ _ hPc hD
  have hgA := spatial ht hT hb H q h D₀ hS hl h₀
  obtain ⟨C,hC,k,hc'⟩ := all_T hd he hh L P hU hK hk ‹IsCompact S› hs hW hz p
  have formal : Fare T X (fun i=> ((T i)⁻¹)^(h+1)+g i^(p+1)) (fun i=> YY i-DD i (cc i)) := by
    refine Fare.of_le k C hC.le ?_; filter_upwards [floor,hx,hy,hc,hu,hv,paid] with i hfloor x' y' c u' v' pay'
    rw [center_read]; exact (hc' _ hfloor _ x' _ y' _ u' _ v' _ _ c pay').trans_eq (mul_assoc ..)
  have hmid := recrop ht hT hb H q h p (η:=η) (by nlinarith [Nat.cast_nonneg (α:=ℝ) (∑ j,e j)]) (by linarith [Nat.cast_nonneg (α:=ℝ) D₀]) formal
  have cross : (fun i=>Y i-YY i-(D i-DD i) (cc i))=O[X] m := by
    refine hgY.sub ?_
    simp_rw [purchased,map_sum,_root_.map_smul,smul_eq_mul]
    refine IsBigO.sum fun i _=>?_ ; obtain ⟨M,Hr⟩ := crop_bound P (d:=d) (flash i) hU p hK hk
    have Hc : (fun a=> crop p (t a) (farCf V (u a) (x a) (flash i))) =O[X] fun a:I=>(1:ℝ) := by
      refine IsBigO.of_bound M ?_; filter_upwards [hx,hc,hu] with j xhj hc hu; rw [norm_one,mul_one]; apply Hr _ hu _ hc _ xhj
    exact (Hc.mul (component_pay hgD i)).congr_right fun i=> one_mul _
  have Hb := cross.add hmid
  have Hu : (fun i => Y i-D i (cc i))=O[X] m := Hb.congr_left fun i=> by rw [LinearMap.sub_apply]; abel
  exact ((((isBigO_norm_left.mpr hgY).add hgD).add (isBigO_norm_left.mpr cross)).add (isBigO_norm_left.mpr hgA)).add (isBigO_norm_left.mpr Hu)
end YM.FVA2.GradedFar259.Comparing
