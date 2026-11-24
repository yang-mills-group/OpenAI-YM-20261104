import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Utmost
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Window
/-! # Exercise G.6 at M.1 buyers' exact meters.

Packaging; clearances convention may also use `arbitrarily_large` for compacts in application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

variable {I K: Type} [Fintype I] [Fintype K] {d:I→ℕ}{e:K→ℕ}
    {M δ L:ℝ}(mn:0≤M)(dp:0<δ) (h:ℕ)
-- clarify F-spectrum. E labels all caps d. H can use any tower, our candidate uses actual one.
abbrev width {d:I→ℕ} (L:ℝ)(u:(i:I)→ Sec G (d i)) : Prop := ∀ i b, ‖coord b (u i)‖ ≤ L
private structure Layout (F:Final C f S) (d:I→ℕ) (e:K→ℕ) (L M δ:ℝ) where
   r : ℝ
   s : ℝ
   x : I→E4
   y : K→E4
   o : E4
   ready : Flash259HorizonFork.Ready r s M δ x y
   p : Viewers F
   q : Viewers F
   u (i:I) : Sec G (d i)
   v (i:K) : Sec G (e i)
   billed : width L u
   reserve : width L v
include H hZ hq hQ mn dp

/-- All terms in the original G.6, including uniform phase prices. NO upper price assumption on T.
Stronger: given the pricing indicated (LogTrace F on the exact Reader, Step **first** Field ratio
comparison of G.1 on the H actually used, Leading on H), buy all radii of s eventually small,
no need to fix a B. Every arity incl. empty, every cap. Use the exact physical reader.
Sec norm convention as usual. Compiled independently of the wider profile estimates except where
using the formal Match outputs here in QScale.
-/
theorem G6 : ∃ C :ℝ, 0<C ∧ ∃ k:ℕ, ∀ᶠ s:ℝ in late, ∀ r x y, Flash259HorizonFork.Ready r s M δ x y →
    ∀ o p q, ∀ u:(i:I)→Sec G (d i), width L u → ∀ v:(i:K)→ Sec G (e i), width L v →
      let b:= C*(g0 G r)⁻¹^k
      let Y t:= trueY F Z r s o t x y u v; let D t:= trueD F Z r s o t y v h; let c:= trueC F Z Q r o x u h
      ‖Y p-D p c‖ ≤ b*(s+(r/s)^(h+1)) ∧
        ‖Y p‖+tallyZ (numbers c)+opCost (D p) ≤ b ∧
        ‖Y p-Y q‖+opCost (D p-D q) ≤ b*s := by
  let J:= Layout F d e L M δ; let s : J→ℝ := Layout.s; let X:= Filter.comap s late
  obtain ⟨C,hC,z,A⟩:= salaries F Z Q H hZ hq hQ (l:=X)
    tendsto_comap mn dp (x:=Layout.x) (y:=Layout.y) (o:=Layout.o) (u:=Layout.u) (v:=Layout.v)
    (Eventually.of_forall fun i=>i.ready) (fun i b=> Allowance.covers (IsBigO.of_bound L (by simpa only [norm_one,mul_one] using (Eventually.of_forall (fun x:J=>x.billed i b)))))
    (fun i b=> Allowance.covers (IsBigO.of_bound L (by simpa only [norm_one,mul_one] using (Eventually.of_forall (fun x:J=>x.reserve i b))))) Layout.p Layout.q (h:=h)
  refine ⟨C,hC,z,(eventually_comap.mp A).mono fun s v r x y h o p q u u' w w'=>?_⟩
  exact v (⟨r,s,x,y,o,h,p,q,u,w,u',w'⟩:J) rfl
omit mn dp H hQ hq hZ

section Threshold
variable {n m:ℕ}{A:Set (Points n)}{B:Set (Points m)}(hA:IsCompact A)(hx:A⊆conf n)(hB:IsCompact B)(hy:B⊆Outside m)
    {W:ℝ} (hW:1≤W)

-- Shape units fixed separately, not relative to r. A flag for RoundMeter proof.
def Clears (W M δ:ℝ) (A:Set (Points n)) (B:Set (Points m)) : Prop := ∀ x∈A,∀ y∈B,∀ T≥W, ∀ r,0<r→
    Flash259HorizonFork.Ready r (r*T) M δ x.ofLp y.ofLp
-- existence price; exercise both eventual sets separately.
private lemma suite (K:Set (Points n)) (h:IsCompact K)(hk:K⊆conf n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, WithinRoom 1 M η x.ofLp 0 := by
  obtain ⟨r,hr,hx⟩:= ((eventually_gt_atTop (0:ℝ)).and (Work.A05.compact_fits h hk)).exists
  refine ⟨r,hr.le, r⁻¹,by positivity,fun x h=> ⟨fun i=> ?_,fun i j hij=>?_⟩⟩
  · rw [sub_zero,mul_one]; exact (PiLp.norm_apply_le x i).trans (hx h).2
  rw [mul_one]; refine ((hx h).1 i j hij).trans ?_
  unfold cubedist; rw [dist_eq_norm]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun k=> PiLp.norm_apply_le (x i-x j) k)
include hA hx hB hy in
lemma arbitrarily_large : ∃ M:ℝ, 0≤M ∧ ∃ δ:ℝ, 0<δ ∧ ∀ᶠ W:ℝ in atTop, 1 ≤ W ∧ Clears W M δ A B ∧ clears W A B := by
  let s (Y:Points m):= forest (0:Points 1) Y
  let L:= s '' B
  have hL : IsCompact L := hB.image (O.Enh.continual continuous_const continuous_id)
  obtain ⟨M,hM,e,he,V⟩:= suite A hA hx
  obtain ⟨M',hM',e',he',U⟩:= suite L hL (by rintro x ⟨y,h,rfl⟩; exact hy h)
  let D:=max M M'; let δ:= min e (e'/2); have dp : 0<δ := lt_min he (half_pos he')
  refine ⟨D,hM.trans (le_max_left ..),δ,dp,?_⟩
  filter_upwards [ eventually_ge_atTop (D/δ),eventually_ge_atTop (1:ℝ), always_clear hA hx hB hy ] with W h' hw hz
  refine ⟨hw,?_,hz⟩
  intro x v y u T h r p; specialize U _ (mem_image_of_mem s u); specialize V x v
  have Y (i:Fin m): s y (Fin.natAdd 1 i)=y i := forest_right ..
  let g: Fin 1:=0
  have L:s y (Fin.castAdd m g)=0 := forest_left g
  constructor
  · exact p
  · exact le_mul_of_one_le_right p.le (hw.trans h)
  · intro i; have q:=V.1 i; rw [sub_zero,mul_one] at q; exact q.trans (le_max_left ..)
  · intro i; have P:=U.1 (Fin.natAdd 1 i); rw [sub_zero,mul_one] at P; change ‖s y _‖≤ _ at P; rw [Y] at P; exact P.trans (le_max_right ..)
  · intro j; have v:= U.2 (Fin.castAdd m g) (Fin.natAdd 1 j) (opposite g j); rw [mul_one,L,Y,zero_sub,norm_neg] at v; exact le_trans (by linarith [ show δ ≤ e'/2 from min_le_right .. ]) v
  · intro i j e; exact (min_le_left ..).trans (by simpa using V.2 i j e)
  · intro i j eq; have q:=U.2 (Fin.natAdd 1 i) (Fin.natAdd 1 j) ((Right 1 m).injective.ne eq); rw [mul_one,Y,Y] at q; exact (min_le_right ..).trans (by linarith)
  · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((div_le_iff₀ dp).mp (h'.trans h)) p.le
end Threshold
end YM.FVA2.GradedFar259.Original
