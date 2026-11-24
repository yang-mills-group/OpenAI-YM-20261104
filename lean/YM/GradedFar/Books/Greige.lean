import YM.GradedFar.Books.Tools

/-!
# One aligned system at the two homes

Finitely many compact requests from C5. Variants of these receipts may buy
Leading but need even the right selection of branch.
-/
namespace YM.FVA2.GradedFar.Books
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth Pose Moving Matrix
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
open Reg.Point (stepV)
local notation "Tn"=> Toon G d
local notation "N1"=> (1:ℕ)

-- explicit [1,2] measurement. Root choice same as detector in last part.
abbrev rootPoints := outgoing RootG
abbrev arms (x y : Sec G d) := Fin.append (fun _ : Fin 1=> x) (fun _:Fin 1=> y)
local notation "xρ"=>rootPoints

-- P : MLM, partial applied
abbrev artist (P : Point G d (1+1)) (x y : Sec G d) : ℂ := P (arms x y)
lemma artist_expand (P : Point G d (1+1)) (x y : Sec G d) : artist P x y=∑ q:Tn, coord q x * artist P (theory q) y := by
    let M := (freezeFar P (fun _ : Fin 1=> y)); let B := (one_grade 1 d)
    change M (fun _=>x)= _; rw [basis_spelling (d:=B),← Equiv.sum_comp (Equiv.funUnique (Fin 1) Tn).symm]
    exact Finset.sum_congr rfl fun q _=> by unfold combo; rw [Fin.prod_univ_one]; rfl
lemma artist_expand' (P : Point G d (1+1)) (x y : Sec G d) : artist P x y=∑ q:Tn, coord q y * artist P x (theory q) := by
    let M := (freezeNear P (fun _ : Fin 1=> x)); let B := (one_grade 1 d)
    change M (fun _=>y)= _; rw [basis_spelling (d:=B),← Equiv.sum_comp (Equiv.funUnique (Fin 1) Tn).symm]; exact Finset.sum_congr rfl fun q _=> by unfold combo; rw [Fin.prod_univ_one]; rfl
lemma artist_tends (P : Point G d (1+1)) (x y : Sec G d) (u v : I→Sec G d)
    (hu : Tendsto (fun i=>chair G d (u i)) T (𝓝 (chair G d x))) (hv : Tendsto (fun i=>chair G d (v i)) T (𝓝 (chair G d y))) :
    Tendsto (fun i=>artist P (u i) (v i)) T (𝓝 (artist P x y)) := by
    have he (v : Sec G d) := artist_expand P x v
    have hh p : Tendsto (fun i=>artist P p (v i)) T (𝓝 (artist P p y)) := by
      rw [artist_expand' P p y]; simp_rw [show ∀ i, artist P p (v i)=_ from (fun i=> artist_expand' P p (v i))]; exact tendsto_finsetSum _ fun j _=> (tendsto_pi_nhds.mp hv j).mul_const _
    rw [artist_expand P x y]; simp_rw [show ∀ i, artist P (u i) (v i)=_ from (fun i=> artist_expand P (u i) (v i))]; exact tendsto_finsetSum _ fun j _=> (tendsto_pi_nhds.mp hu j).mul (hh _)

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {F : Pose.Plans G d} {Z : Rolled G d}
abbrev DataPoint := ℝ × (↥Growth.Small)
local notation "V"=> F
local notation "T0"=> filed
local notation "Z0"=> (Zenith Z)

/-- Mixed job with first slot called at home r exp s (test at xρ on r scale).
Includes leading engineering tilt in that announcement. This is merely a request
among those in the submitted argument. Equivalent true row in W units via `forwards` on it.
Second lens `Read.prism` for the fixed Maxwell pair.
-/
def orient (Z : Rolled G d) (r s : ℝ) := forwards Z r s * Level.Dial d s
variable (u v : Toon G d)
def safari (F : Pose.Plans G d) (r : ℝ) : Matrix Tn Tn ℂ := fun v u=> artist (F r _ xρ) (theory u) (Read.prism (theory v))
def mix (F : Pose.Plans G d) (Z : Rolled G d) (r s : ℝ) : Matrix Tn Tn ℂ := fun v u=> artist (F r _ xρ)
    (orient Z r s (theory u)) (Read.prism (theory v))

/-- Need from C5 that these mixed poses tend to the leading reference; one
way to expose the exact hypothesis. See `from_mixed` for deriving from C5
leading receipts, orientations as at B.
-/
def Mixed (F : Pose.Plans G d) (Z : Rolled G d) := ∀ a b : Tn,
    Tendsto (fun i : DataPoint=> mix F Z i.1 i.2.val a b) T0 (𝓝 (Read.GramP G d a b))
variable (θ : ℝ → ℝ)
include H
lemma gram : artist (fxt (Pose.Bbook N d) xρ 0) (theory u) (Read.prism (theory v))=
    Read.GramP G d v u := by
    rw [Pose.nickel N M H xρ ok_wall d]
    change Maxwell.Wick.moment G xρ _ = Maxwell.Free.bond G _ _ ((theory u).val) ((Read.prism (theory v)).val)
    unfold rootPoints outgoing RootG; rw [O.Enh.lamp,Maxwell.Free.bond_eval]
    congr 1; ext1 i; fin_cases i <;> rfl

variable (h : Beginning N θ d F) (hθ : Tendsto (fun r=>θ r/gYM G r) τ (𝓝 1))
include h
-- arity 2 both same r always, no use of Leading separately
lemma forest_go (a b : Tn) : Tendsto (fun i:DataPoint=> safari F i.1 a b) T0 (𝓝 (Read.GramP G d a b)) := by
    let S:Set (Points (1+1)):={xρ}; have hs : S⊆ conf (1+1):= singleton_subset_iff.mpr ok_wall
    have hh:= (born filed N M _ (show Tendsto (Prod.fst : DataPoint→ℝ) T0 τ from tendsto_comap) H θ (x:=fun _=>xρ)
      (K:=S) isCompact_singleton hs (Eventually.of_forall fun _=> mem_singleton _) h (arms (theory b) (Read.prism (theory a))) (p:=0)).2
    have he:= collapses T0 N M (Prod.fst : DataPoint→ℝ) tendsto_comap H hh le_rfl
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mp
    simp_rw [blend, Nat.zero_add, Finset.sum_range_one, pow_zero, one_smul, tells, Pose.line,coeff_mk] at he -- def
    rw [← gram N M H b a]; exact he

def lampLetter (x:FieldEnd G d): Matrix Tn Tn ℂ:= fun a b=> coord a (x (theory b))
omit h H in
lemma ingredient (F : Pose.Plans G d) (r s : ℝ) (Z : Rolled G d): mix F Z r s = safari F r * lampLetter (orient Z r s):= by ext a b; simp_rw [mix, artist_expand (x:=orient Z r s (theory b)), Matrix.mul_apply]; exact Finset.sum_congr rfl fun j _=>mul_comm ..
variable (hF : Mixed F Z)
include hF
theorem aimed (u v : Tn) : Tendsto (fun i:DataPoint=> lampLetter (orient Z i.1 i.2.val) v u) T0 (𝓝 ((1:Matrix Tn Tn ℂ) v u)) := by
    let B i:=safari F i; let L i:=Read.GramP G d i
    have hv:Tendsto (fun i:DataPoint=>safari F i.1) T0 (𝓝 (Read.GramP G d)) := tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> forest_go N M H θ h a b
    have he:Tendsto (fun i:DataPoint=>mix F Z i.1 i.2.val) T0 (𝓝 (Read.GramP G d)) := tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> hF a b
    let M0 := Read.GramP G d
    have hm : IsUnit M0 := Read.positive_unit Read.GramP_pos
    have hp : M0.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hm).ne_zero
    have hdist : ContinuousAt Ring.inverse M0.det:= by
      rw [show (Ring.inverse : ℂ→ℂ) = Inv.inv from funext Ring.inverse_eq_inv]; exact continuousAt_inv₀ hp
    have hx := (continuousAt_matrix_inv M0 hdist).tendsto.comp hv
    obtain ⟨_,_,hr⟩:= Continuation.Margin.matrix_estate (fun i:DataPoint=>safari F i.1) T0 M0 hm (fun a b=> forest_go N M H θ h a b)
    have hk := hx.mul he
    change Tendsto _ T0 (𝓝 (M0⁻¹*M0)) at hk; rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _|>.mp hm)] at hk
    apply (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hk v) u).congr'
    filter_upwards [hr] with i h; simp_rw [ingredient]; unfold Function.comp; rw [← mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h.1),one_mul]

lemma paced : Tendsto (fun i:DataPoint=> chairs G d (orient Z i.1 i.2.val)) T0 (𝓝 1) := by
    have he (a b:Tn): Tendsto (fun i:DataPoint=> coord b (orient Z i.1 i.2.val (theory a))) T0 (𝓝 (coord b ((1:FieldEnd G d) (theory a)))) := by
      change Tendsto _ _ (𝓝 (coord b (theory a))); rw [pivotδ]; simpa [Matrix.one_apply,eq_comm, lampLetter] using aimed N M H θ h hF a b
    rw [← chairs_one (G:=G) (d:=d)]; simp_rw [stands]
    exact tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun j _ => Tendsto.smul (he ..) tendsto_const_nhds

end
end YM.FVA2.GradedFar.Books
