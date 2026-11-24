import YM.LocalLTE.Vault.Branch
/-! Summit affordability in all arities. Marker argument transported separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vault
open Finset Function Filter Lattice Wilson RG Source Labels Extra.Histories Motion
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open LocalLTE.Port ConnectedActivityE6 Blaze
open AbsoluteSums Animals Next.Foundations
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Interval Classical
variable {G:Gauge}{n:Side}
attribute [local instance] Gauge.frobInner
variable (f:Config G n→ ℂ) (Z:Grove (0:Site n)){s k:ℕ}{x κt :ℝ}
variable (hp: Reliable G κt x)
local notation "Q"=> strut κt Z s k f
variable {b e u w:ℝ}
set_option quotPrecheck false
local notation "W" => neighbors s (0:Site n)
local notation "W'"=> neighbors (s+1) (0:Site n)
variable {F:Labels.Frame G 0} (A:Hol G)(D:SectionData F)
variable (R:Rep G n)
variable {i:Site n}
local notation "P"=> (R.p)
variable (hF:R.p.Regular (neighbors s (0:Site n)) f)(hB:R.p.supBounds 0 (neighbors s (0:Site n)) f b)(he:f 1=0)
    {v t :ℝ}
section
variable (F)
noncomputable def roughHat (s k:ℕ)(κ:ℝ) : Coefficient F n where
   x:=0
   support _:=neighbors (s+1) 0
   regular:= Pi.single 0 (strut κ Z s k f)
   forced:=0
end
open Concourse
-- summit. credit vector includes plus etc.
variable (M:Coefficient F n)(hX:M.support=(fun _=> Animals.neighbors (s+1) (0:Site n)))(h:M.regular=Pi.single 0 f)(ht:M.Format 0 A R)(hK:Local.ForceCost R.p R.activities M.forced (Real.sqrt e*v))
include hp hF he hB hX h ht hK
lemma supported (hδ:∀ i:Bool,R.p.supBounds 0 W' ((Port.scaleQ i ∘ f)-Hall.shave Z s κt k (Port.scaleQ i ∘ f)) u)(h0:∀ i:Bool,ContDiffAt ℝ (↑k) ((Port.scaleQ i ∘ f) ∘ Grove.soloV) 0)
    (hc:0<k)(l:ℕ)(hv:s+1 ≤l)(a:ℕ)(H:k ≤a+1) (hh:0 ≤w)(hν:v≤w)(he₁:0<e)(ht0:R.p.mass W' (2*u)≤w)(hx:R.p.mass W' (b+2*u)≤t) :
    Exhibition D κt l a A R (Concourse.memo 0 M) (Vault.roughHat f Z F s k κt) (Real.sqrt e) t w:=by -- order F
    let T':= Vault.roughHat f Z F s k κt; let ff:=(Q); let I:= Animals.neighbors (s+1) (0:Site n); let q:= R.p.mass I (b+2*u); have hO:(0:Site n)∈ I:= (neighbors_mem ..).2 (by rw [separation_self]; exact Nat.zero_le _)
    obtain ⟨hz',hp₁,hb,hV⟩:=strutFits f Z hp hF hB h0 hδ hc; have hs:T'.Format 0 A R:=by
        refine ⟨fun i=> ?_,fun i=>hO,fun i=>?_,fun j hj=>?_,fun j u h=>(h rfl).elim,fun j h=>(h rfl).elim,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl, fun _=> measurable_const⟩
        · by_cases h:i=0; subst i; unfold T' Vault.roughHat; simpa only [Pi.single_eq_same] using! hz'
          rw [show T'.regular i=0 from Pi.single_eq_of_ne h _]; exact regular_const _
        · by_cases h:i=0; subst i; simpa only [T',Vault.roughHat,Pi.single_eq_same] using! hV.trans he
          rw [show T'.regular i=0 from Pi.single_eq_of_ne h _];rfl
        · by_cases h:j=0
          · subst j; have hx: Vault.halcyon (strut κt Z s k f)=0:= funext (fun _=> hV.trans he)
            have hv:= Vault.pivot R I (Q) hz' hj A
            change R.p.Regular I (Q) at hz'; rw [show Vault.halcyon (Q)=0 from hx,sub_zero] at hv; simpa [T',roughHat] using hv
          rw [show T'.regular j=0 from Pi.single_eq_of_ne h _]; exact fun v=>⟨contDiffAt_const,fun k hk=>by change iteratedDeriv k (0:ℝ →ℂ) 0=0; simp⟩
    have hc₁:0≤q:= mul_nonneg (Real.exp_nonneg _) hp₁.1; let f₁:= decrement (memo (0:F.Coeff) M) T'; have hl:M.support=T'.support:=hX
    refine ⟨?_, hs, hl, River.offFormat (memo_format _ ht) hs (show T'.forced=0 from rfl) hl, ?_,?_⟩ -- expected signature offFormat states requires species; inspect
    · apply (show Patrons D κt l a R.p T' q from ?_).priced hx; refine ⟨by simpa [Frame.coeffSize,T',roughHat] using hc₁,⟨Pi.single 0 (b+2*u),Vault.one_bill R (fun _=>I) _ hp₁.1,?_⟩,rfl⟩; intro i; by_cases h:i=0; swap; · rw [show T'.regular i=0 from Pi.single_eq_of_ne h _,Pi.single_eq_of_ne h]; exact River.Canvas.quiet (le_refl _)
      subst i; unfold T' Vault.roughHat; rw [Pi.single_eq_same]; dsimp only; rw [Pi.single_eq_same]; change R.p.supBounds _ _ _ _ at hp₁;refine ⟨hp₁,fun _=>⟨fun x hx=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp hx).trans hv),Q,hz',hp₁,⟨0,by simpa only [Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero] using hp₁.1,by rw [map_zero,add_zero]⟩,s,(Nat.le_succ s).trans hv,Z,fun i=>rp_raise _ (strutPowers ..) H⟩⟩
    · refine ⟨Real.sqrt_pos.mpr he₁,hh,hh,⟨Pi.single 0 (2*u),?_,fun i=>?_⟩,?_⟩; · let v:= Vault.one_bill R (fun _=>I) (2*u) hb.1; change SumBudget (fun i=> R.p.mass (M.support i) _) w; rw [hX];exact Push.AbsoluteSums.budget_loosen v ht0 -- notation
      · change R.p.supBounds 0 (M.support i) (f₁.regular i) _; have hv':f₁.regular i=(Pi.single 0 f : ℕ→ Config G n→ℂ) i-(Pi.single 0 ff : ℕ→ Config G n→ℂ) i:=by change M.regular i-T'.regular i=_;rw [h]; rfl
        by_cases hi:i=0; subst i; rw [hv', Pi.single_eq_same,Pi.single_eq_same,Pi.single_eq_same,hX];exact hb
        rw [hv',Pi.single_eq_of_ne hi,Pi.single_eq_of_ne hi,Pi.single_eq_of_ne hi,sub_self]; simpa only [norm_zero] using! bound_const (B:=R.p) (X:=(M.support i)) (o:=(0:Site n)) (0:ℂ)
      change Local.ForceCost R.p R.activities f₁.forced _; rw [show f₁.forced=M.forced from sub_zero _]; obtain ⟨q,hq,hp⟩:= hK; exact ⟨q,budget_loosen hq (mul_le_mul_of_nonneg_left hν (Real.sqrt_nonneg _)),hp⟩
    · change F.coeffSize ((0:F.Coeff)-0)≤_; simpa [Frame.coeffSize] using hh
end YM.LocalLTE.Vault
