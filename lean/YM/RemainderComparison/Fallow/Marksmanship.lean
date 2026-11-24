import YM.RemainderComparison.Fallow.Scores
/-!
# Logical singleton projection on the marker-conditioned expression

Keeper runs after Passion.Both. tilts. Literal `Source.Coefficient` in the actual header and kernel conventions. Keeps `ζ` operator tests normalized before bases, connects X to Pet.R and bound. Before conversion on different bases by RG04, use representation supplying THESE commitments. No assumption chosen χ in Region matches a final stable graph.Via β conversion eventual.Se.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {α:Type*}{G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable [Fintype θ][DecidableEq θ](J:Census θ)
variable {i:θ}{D:ι→Finset θ}{z:ι→ Poly J}(X: Hol G) (F:Plane G n θ) (a:Audited Q)
local notation "L"=>F.visor i
set_option quotPrecheck false
local notation "F₀"=>(L).basis
local notation "τ"=> (L).sectionQ
local notation "o'"=>(L).origin
local notation "A" => Roll T R Z D
local notation "A₁"=> cash T p R Z F X SeatD.MaskType.exactM z D

-- Unit projection data. Before α layout tests as all marker packs.V No continuity α on arbitrary OFFMASK required. Need physical test evaluation before operator size. 
local notation "R₀" => players T R Z F D i
local notation "M"=>SeatD.MaskType.exactM
local notation "Wq" => salary T R Z J F z i
local notation "δp" => crowns T p R Z J X F a z i
local notation "Rφ" => kernels T p R Z J X F a z i
variable (hp:Passion.Oriented D J Z z)(he:F.exam i)
variable {σ b t e w:ℝ}{l k:ℕ}
variable (h:Precepts T p R Z D σ b)(hr:AxisG p F X t l e) (hQ : Placed R F D)
variable (w:θ→ℝ) (x:players T R Z F D i)
local notation "Y₁"=> area T R Z F (D:=D)
local notation "Q₁" => PairAt T p R Z F X x.val a i
local notation "P" => p.threshold
local notation "κ" => (w i)⁻¹
variable (hW: Serif.Chorus J w Z z k)
omit [Fintype θ]
include hW
lemma stroke_bound (v:Multiset ι) : ‖Fallow.motto Z J z i v‖ ≤ κ:=by
   have hf := (Poly.member hW.votes (J.fire i) (controls Z z v)).trans (Serif.bought hW v);
   rw [Poly.solo_toll] at hf; rw [inv_eq_one_div]; exact (le_div_iff₀ (hW.votes _)).mpr (by rw [mul_comm]; exact hf)
omit hW
include hQ
omit [DecidableEq θ] [∀ i,NormedSpace ℝ (Q i)] in
lemma issued : Y₁ x.val= Local.joint τ o' (T.halls x.val.val.val) ∧ o'∈ Y₁ x.val:= ⟨(by unfold area; rw [x.prop]), lanes T R Z F x.val (sits T R Z F x.val i x.prop hQ)⟩
include h hr hQ
-- LINEAR CSR log closure. Revisits old basis.same
lemma survey : p.Regular (Y₁ x.val) (Rφ x) ∧ Reads X o' (Y₁ x.val) (0:Labels.Label G (L).degree) (Rφ x):=by
   have hf:= Passion.opal T p R Z F X .exactM x.val a i h x.prop hr
   have hb : p.Regular (Y₁ x.val) (Q₁|>.entry):= by rw [(issued T R Z F hQ x).1]; exact hf.regular
   have hp:Reads X o' (Y₁ x.val) (0:Labels.Label G (L).degree) (Complex.ofReal ∘ (Q₁|>.entry)):=by rw [(issued T R Z F hQ x).1]; exact hf.exactQ
   refine ⟨regular_smul _ (regular_mapped Complex.ofRealCLM hb),?_⟩
   have hr' := (reads_null_iff ..).mp hp; rw [reads_null_iff]; obtain ⟨hV,hK⟩:=hr';
   refine ⟨?_,fun he=>?_⟩; unfold kernels; rw [Pi.smul_apply]; exact congr_arg _ hV |>.trans (smul_zero _)
   intro Xp; -- M notation bug
   obtain ⟨hP,hQ⟩:= hK he Xp; refine ⟨hP.const_smul (Wq x),fun i hi=>?_⟩
   unfold kernels; simp_rw [Pi.smul_apply]; rw [iteratedDeriv_fun_const_smul (hP.of_le (Nat.cast_le.mpr hi)),hQ i hi, smul_zero]

-- summability on fixed marker sum.Sem... Radius.M.Brand per each. α proof not needed here beyond grants.Per ordinal repair. Same allocations for all x.
variable {pP:ℝ} (hκ : Lodge T p R Z F X SeatD.MaskType.exactM D pP)
include hκ hW
local notation "B₁"=>κ * pP
lemma merit : ∃ f:R₀→ℝ, SumBudget (fun x':R₀=> p.mass (Y₁ x'.val) (f x')) B₁ ∧ ∀ x': R₀,∀ a:Audited Q,
       p.supBounds o' (Y₁ x'.val) (kernels T p R Z J X F a z i x') (f x') ∧
        (L).basis.coeffSize (crowns T p R Z J X F a z i x') ≤ f x':=by
    obtain ⟨f,hf,hV,hX⟩:= hκ.budget; let g (x:R₀):=κ*f x.val; have hΩ : 0≤κ:=inv_nonneg.mpr (hW.votes _).le; have hg x:0 ≤ g x:= mul_nonneg hΩ (hf _); refine ⟨g,?_,fun x a=> ?_⟩
    · let t:=hV o'; refine budget_mono (budget_scale hΩ (budget_pull (fun i:R₀=> i.val) Subtype.val_injective t)) (fun i=>(hg i).trans (p.loMass _ _ (hg i))) (fun x=> ?_)
      obtain h:= (issued T R Z F hQ x).2; simp only [if_pos h]; unfold BudgetPoint.mass g
      calc _ = κ * (f x.val*Real.exp (p.supportExponent * coverNumber p.B (Y₁ x.val))) := by ring
           _ ≤ _ := by have hxg:=hf x.val; gcongr; linarith
    obtain ⟨hz,hU⟩:=issued T R Z F hQ x; have he:= Passion.opal T p R Z F X M x.val a i h x.prop hr
    obtain ⟨h_l,hS,hq⟩:= (hX x.val).2.2 i x.prop a _ hU; have hu : ‖salary T R Z J F z i x‖≤ κ:= stroke_bound Z J w hW _
    constructor
    · rw [hz]; exact bound_weaken (bound_smul _ (show p.supBounds o' _ (Complex.ofReal ∘ ((PairAt T p R Z F X x.val a i).entry)) _ from (sup_real he.regular).mpr hS)) (mul_le_mul_of_nonneg_right hu (hf _))
    let Q:= (PairAt T p R Z F X x.val a i).header
    have hz: (F₀).coeffSize (salary T R Z J F z i x • Q) = ‖Wq x‖*(F₀).coeffSize Q:=by unfold Labels.Frame.coeffSize; simp only [Pi.smul_apply, norm_smul, Finset.mul_sum]
    unfold crowns
    change (F₀).coeffSize (_ • Q) ≤_; rw [hz]
    exact mul_le_mul hu h_l (Work.G08.size_nonneg ..) hΩ
end YM.RemainderComparison.Fallow
