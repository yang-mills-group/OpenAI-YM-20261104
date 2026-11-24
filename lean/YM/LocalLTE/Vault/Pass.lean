import YM.LocalLTE.Vault.Rope
import YM.LocalLTE.Concourse.Pane
/-!
# Activation with independent exceptional-stencil pricing

Unit happens off-mask, other terms require switch combinations paid from this
ACTUAL KF. Body tag uses all avail keeper slots. Reserve on input attachment transparent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vault
open Finset Function Lattice Wilson RG Source Labels Extra.Histories
open Set
open Push Local PhysicalNext.Repeat MeasureTheory ConnectedActivityE6 Blaze
open Next.Foundations Push.AbsoluteSums Animals
open YM.MergeProof Vinca River Concourse Planned.GuardedAtom Guard
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{A:Hol G} {F:Labels.Frame G 0}
variable (F)
variable {n : Side} (R:Rep G n) (T:Keeper R.p R.activities) (U:Support n)
local notation "X"=> Config G n
local notation "o"=> (0:Site n)
-- Offered pose shape.A. fixed before approval, independent regulator chart.
variable (f:Config G n→ℂ)
def halcyon : Config G n →ℂ:= fun _=> f 1
noncomputable def gorge (R:Rep G n) (S:Support n) (g:Config G n→ℂ) := g - masked R.p.threshold S g
section
local notation "q"=> (f-Vault.halcyon f)
noncomputable def shoot : ℕ→ Config G n→ℂ:= Pi.single 0 (gorge R U (f-Vault.halcyon f))
local notation "t"=> shoot R U f
variable (S: Berths R.p R.activities (fun _:ℕ=>U))
noncomputable def nucleus := Dilation.rented S (shoot R U f) (R:=R)
local notation "kH"=> nucleus R U f S
noncomputable def draw :Coefficient F n:={x:= f 1 • F.e0,support:= fun _=>U, regular:= Pi.single 0 (f-halcyon f), forced:= nucleus R U f S}
local notation "V"=> draw F R U f S
variable {e : ℝ}
set_option quotPrecheck false
local notation "θ" => (R).p
-- dominators guaranteed for all configurations incl flags.
lemma tagStore (hf:(R).p.Regular U f)(h:∀ i,‖(q) i‖≤e): (∀ i:ℕ, Attaches R.p.threshold U (t i)) ∧ ∀ i I', ‖t i I'‖≤ (Pi.single 0 e : ℕ→ ℝ) i :=by
    let A:= q
    have he:(R.p).Regular U A:=regular_sub hf (regular_const _); have hv:= uses_mask (R).p.threshold he.sites
    have ht:Attaches (R.p).threshold U (t 0):=by
        unfold shoot; rw [Pi.single_eq_same];
        exact ⟨fun X' Y h1 ht=>congr_arg₂ (·-·) (he.sites X' Y h1) (hv X' Y h1 ht),fun g X'=>congr_arg₂ (·-·) (he.symmetry _ _) (invariant_mask he.symmetry _ _ _ _),(he.borel).sub (masked_measurable _ _ _ he.borel),fun I h=>sub_eq_zero.mpr (masked_eq _ _ _ _ h).symm⟩
    constructor; intro i; by_cases h:i=0; exact h.symm ▸ ht; rw [show t i=0 from Pi.single_eq_of_ne h _]; exact Attaches.zero ..
    intro i U'; by_cases he:i=0;swap
    · rw [show t i=0 from Pi.single_eq_of_ne he _, Pi.single_eq_of_ne he]; change ‖(0:ℂ)‖≤_; rw [norm_zero]
    subst i; rw [Pi.single_eq_same]; by_cases hP:Healthy (R.p).threshold U U'
    · rw [ht.healthy_zero U' hP,norm_zero]; exact (norm_nonneg _).trans (h U')
    rw [show t 0=gorge R U A from Pi.single_eq_same ..]; unfold gorge; simp only [Pi.sub_apply,masked_ne _ _ _ _ hP,sub_zero]; exact h U'
variable {σ C δ Λ r x y z:ℝ}
variable (hD:0∈U)(hp:R.Lawful σ C Λ δ x)(hx:0 < x)(hK:Local.hitWidth R.p*x ≤1)
lemma one_bill (q0 :ℕ→Support n)(u:ℝ)(h:0≤u): SumBudget (fun i:ℕ=> R.p.mass (q0 i) ((Pi.single (0:ℕ) u : ℕ→ℝ) i)) (R.p.mass (q0 0) u):=by
    classical
    have ht i: (R).p.mass (q0 i) ((Pi.single 0 u : ℕ→ℝ) i)=(Pi.single 0 (R.p.mass (q0 0) u):ℕ→ℝ) i:=by by_cases h:i=0; subst i;simp; simp [Pi.single_eq_of_ne h,BudgetPoint.mass]
    simp_rw [ht]; have he:HasSum (Pi.single (0:ℕ) (R.p.mass (q0 0) u)) (R.p.mass (q0 0) u):= hasSum_pi_single ..;refine ⟨fun i=>?_,he.summable,he.tsum_eq.le⟩; change 0 ≤ (Pi.single (0:ℕ) (R.p.mass (q0 0) u):ℕ→ℝ) i; by_cases hx:i=0; subst i; rw [Pi.single_eq_same]; exact mul_nonneg (Real.exp_nonneg _) h; rw [Pi.single_eq_of_ne hx]
variable (hf:R.p.Regular U f)
local notation "g"=> hitWidth R.p*x*reservedMass R.p U e
include hf
lemma pivot (hi:Nonwrapping U (0:Site n))(H:Hol G) : H.PiVanish 0 0 (f-halcyon f):=by
    have ht : (R).p.Regular U (f-halcyon f):=regular_sub hf (regular_const _)
    have hz:=Push.Local.project_reads H 0 ht (Nat.zero_le _); rw [Reads,if_pos hi] at hz; refine fun j=>⟨(hz j).1, fun k hk=>?_⟩
    rw [Nat.eq_zero_of_le_zero hk,iteratedDeriv_zero]; change _-f 1=0; rw [show H.testLinks _ _ j 0=(1:Config G n) from funext fun i=>(congr_fun (H.flat _ _) _),sub_self] -- inference
include hf hD hp hx hK
lemma roots (χ:Hol G)(A:SectionData F)(h:∀ i,‖f i-f 1‖≤e)(u:ℝ)(he:R.p.supBounds 0 U (f-halcyon f) u) : let V':= Vault.draw F R U f S
    V'.Format 0 χ R ∧ V'.x 0=f 1∧
    (∀ W:Config G n, V'.density 0 A R W=(R.eval W:ℂ)*f W) ∧ Local.ForceCost R.p R.activities V'.forced (hitWidth R.p*x*Local.reservedMass R.p U e) ∧ Tab V' 0 R (Real.sqrt x) ((R.p).mass U u) ((hitWidth R.p*x*Local.reservedMass R.p U e)/(Real.sqrt x)):=by
    intro W; let Ω:ℕ→ℝ:= Pi.single (0:ℕ) e; have ht:= tagStore R U f hf h; have hN: 0 ≤ e:= (norm_nonneg _).trans (h 1)
    have hm(i): 0 ≤ Ω i:=by by_cases he:i=0; subst i; rw [show Ω 0=e from Pi.single_eq_same ..]; exact hN; rw [show Ω i=0 from Pi.single_eq_of_ne he _]
    have hg': reservedMass R.p U e≥0:=mul_nonneg (Real.exp_nonneg _) hN
    have hh:SumBudget (fun i:ℕ=>reservedMass R.p U (Ω i)) (reservedMass R.p U e):=by
        rw [show (fun i:ℕ=> reservedMass R.p U (Ω i))=Pi.single (0:ℕ) (reservedMass R.p U e) from funext (fun i=>by by_cases hi:i=0; subst i; simp [Ω]; simp [Ω,Pi.single_eq_of_ne hi, reservedMass])]
        let v:(ℝ):= reservedMass (R).p U e; have h0:= hasSum_pi_single (0:ℕ) v; refine ⟨fun i=> ?_, h0.summable, h0.tsum_eq.le⟩; by_cases ht:i=0; subst i; simpa only [Pi.single_eq_same] using! hg'; rw [Pi.single_eq_of_ne ht]
    obtain ⟨hH,hT,hU,hP,h₀⟩:=Dilation.cover S (shoot R U f) ht.1 (fun _=>hD) Ω (fun i=>⟨hm _,ht.2 _⟩) hh hp hx.le hK
    have hk i (hi:i≠0): W.regular i=0:=Pi.single_eq_of_ne hi _
    let p:= q; have hz:W.regular 0=p:=by unfold W Vault.draw; dsimp only; rw [Pi.single_eq_same]
    have hm:R.p.Regular U p:=regular_sub hf (regular_const _)
    refine ⟨⟨fun i=>?_,fun i=>hD,fun i=>?_,fun i H=> ?_,hH.forcing,hH.carried,hH.invariant,hH.supported,hH.borel⟩,?_,fun Y=> ?_,hT,?_⟩
    · by_cases h:i=0; subst i;exact hz.symm ▸ hm
      rw [hk i h]; exact regular_const _
    · by_cases h:i=0; subst i; rw [hz]; exact sub_self _
      rw [hk i h]; rfl
    · by_cases h:i=0
      · subst i; rw [hz]; exact pivot R U f hf H χ -- args
      rw [hk i h]; exact fun j=>⟨contDiffAt_const,fun k hk=>by change iteratedDeriv k (0:ℝ→ℂ) 0=0; simp ⟩
    · simp [W,Vault.draw,Frame.e0]
    · let uS:= Real.exp (R.exponent Y); let v:=masked (R).p.threshold U p Y
      have he1: ∀ i:Finset ℕ, W.marked R i Y=gasMark R.p R.activities Y i W.forced:=fun _=>(gasMark_eq ..).symm
      have he2:(∑' i,(W).maskedTerm R i Y) = v:=by rw [tsum_eq_single 0]; exact congr_arg (fun u=>masked R.p.threshold U u Y) hz; intro j h; rw [Coefficient.maskedTerm,hk j h];exact congr_fun (map_zero (maskLinear _ _)) _
      have he3:(∑' j,(t j Y))=p Y-v:=by rw [tsum_eq_single 0,show t 0=gorge R U p from Pi.single_eq_same ..];rfl; intro i hi; rw [show t i=0 from Pi.single_eq_of_ne hi _];rfl
      rw [Coefficient.density, Concourse.center_entry, he2]; simp_rw [he1]; rw [show (∑' j, gasMark R.p R.activities Y j W.forced)=_ from (h₀ Y).tsum_eq,he3]; have ht : p Y=f Y-f 1:=rfl; rw [ht, show W.x 0=f 1 from (by simp [W,Vault.draw,Frame.e0]),Rep.eval,Complex.ofReal_mul]; ring
    have hV:0<Real.sqrt x:=Real.sqrt_pos.mpr hx; have hp:0≤g:=mul_nonneg (mul_nonneg (zero_le_one.trans (width_one_le _)) hx.le) hg'
    refine ⟨hV,mul_nonneg (Real.exp_nonneg _) he.1,by exact div_nonneg hp hV.le, ⟨Pi.single 0 u, Vault.one_bill R (fun _=>U) u he.1, fun j=>?_⟩,?_⟩
    · by_cases h:j=0; subst j; rw [hz, Pi.single_eq_same]; exact he
      rw [hk j h,Pi.single_eq_of_ne h]; simpa only [norm_zero] using! bound_const (B:=R.p) («X»:=U) («o»:=(0:Site _)) (0:ℂ)
    rw [mul_div_cancel₀ _ hV.ne']; exact hT
end
end YM.LocalLTE.Vault
