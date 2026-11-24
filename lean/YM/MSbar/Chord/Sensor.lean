import YM.MSbar.Chord.Acre
import YM.MSbar.Wave.Seat
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open Lattice Wilson Gauge Work.F03 Push Push.Uniform RG Precision AnalyticBridge.VerifiedReset Planned.AtomRegular MSbar.Rolling MSbar.Wave Set
open PhysicalNext.Repeat.Pane
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c : Side}{S:Set (Positions (Primary c G))}{W r K Λ σ α:ℝ}
variable (R:Rep G c)(u v p :ℕ) (t :ℝ)
noncomputable def walnut (R:Rep G c)(x:Positions (Primary c G)) := Real.log (R.eval (palace x))
local notation "E"=>Positions (Primary c G)
variable (h:R.Lawful σ K Λ α W)(g:Bash S R.p)
include h g
lemma pie (x:Positions (Primary c G))(a:x∈ S): walnut R x=(R.v*Fintype.card (Site c)-(R.beta*collectT c R.path R.clip x+liveLoop c R.path x)) - arc R.activities R.p x:=by
    have ht:= (g x a).2; unfold walnut Rep.eval; rw [Activities.gas_one _ _ ht, mul_one,Real.log_exp]; unfold Rep.exponent; rw [crystalline R.path R.clip R.p R.beta _ ht];rfl
-- hypotheses with Open.F.scale.Possible choose directly.
variable (e:G.Color) (he:‖e‖=1)(hG:G.Simple) (hp:IsOpen S)(hT:Convex ℝ S)(hx:(0:Positions (Primary c G))∈ S)
include e he hG hp hT hx
lemma climb (hu:10*(p+4) < c.val) (hB:R.p.B≤v) (hq:10*(u*(4*v+2)+2*v)< c.val):
    ContDiffAt ℝ 2 (walnut R) 0 ∧ |grossH (rim (walnut R)) e + R.beta*grossH (rim (collectT c R.path R.clip)) e| ≤ 2*Λ*url c p σ + brim c R.p G u*α :=by
    let K:= grossH (rim (collectT c R.path R.clip)) e; let C':= Fintype.card (Site c); let W:=(C':ℝ)⁻¹
    let F:= walnut R; let M:= collectT c R.path R.clip; let g':=liveLoop c R.path; let f:= arc R.activities R.p
    let v:= R.v*(Fintype.card (Site c)); let b:=R.beta
    let l: E→ℝ := Function.const _ v; let Q : E→ℝ := l - (b • M +g')-f; have hm : F=ᶠ[𝓝 0] Q:= (show ∀ᶠ x in 𝓝 (0:E),x∈S from hp.mem_nhds hx).mono (fun i hi=> pie R h g i hi)
    let x:= tint G (Exterior.Body 1 c); have hM: ContDiffAt ℝ 2 M 0:=((show ContDiffAt ℝ ω _ (x 0) from Work.F02.mainTerm_contDiffAt h.paths (fun i=> (represent_smooth ..).contDiffAt)).comp _ x.contDiff.contDiffAt).of_le le_top
    have hb: ContDiffAt ℝ 2 g' 0:= (eraP R.path R.clip h.paths (0:E) (0:E)).1.1.of_le le_top
    have hk: ContDiffAt ℝ 2 f 0:= (heir h.labels hp hT g 0 hx 2 ((by norm_num: 2≤6).trans R.p.order_ge)).1
    have ht: ContDiffAt ℝ 2 (fun x=>b*M x) 0:= hM.const_smul b
    have hl : ContDiffAt ℝ 2 l 0:=contDiffAt_const
    have hD:ContDiffAt ℝ 2 Q 0:= (hl.sub (ht.add hb)).sub hk; refine ⟨hD.congr_of_eventuallyEq hm,?_⟩
    have he' : iteratedFDeriv ℝ 2 F 0 = -(b • iteratedFDeriv ℝ 2 M 0 + iteratedFDeriv ℝ 2 g' 0 + iteratedFDeriv ℝ 2 f 0):=by
        have h0p:ContDiffAt ℝ 2 (b • M) 0:=ht; have hk':ContDiffAt ℝ 2 (b • M+g') 0:= h0p.add hb; have heL:ContDiffAt ℝ 2 (l-(b • M +g')) 0:= hl.sub hk'; rw [(hm.iteratedFDeriv ℝ 2).eq_of_nhds]; unfold Q; rw [iteratedFDeriv_sub_apply heL hk,iteratedFDeriv_sub_apply hl hk',iteratedFDeriv_add_apply h0p hb, iteratedFDeriv_const_smul_apply hM]; rw [show iteratedFDeriv ℝ 2 l 0=0 from (by change iteratedFDeriv ℝ 2 (fun _ : E=> v) 0=0; rw [iteratedFDeriv_const_of_ne (𝕜:=ℝ) (show (2:ℕ)≠0 by decide) v] ; rfl)]; abel
    have hV (x y:E) : rim F x y= -(b*rim M x y+rim g' x y+rim f x y):=by
        have ht := congr_arg (fun l:Tensor.T E ℝ 2=> l ![x,y]) he'; change iteratedFDeriv ℝ 2 F 0 _= _ at ht; simp only [_root_.neg_apply,_root_.add_apply, _root_.smul_apply,iteratedFDeriv_two_apply] at ht; exact ht
    have hA : grossH (rim F) e= -(b*K+grossH (rim g') e + grossH (rim f) e) :=by unfold K; unfold grossH gross; simp_rw [hV]; simp_rw [neg_mul,add_mul,Finset.sum_neg_distrib, Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]; ring; -- syntax
    rw [show grossH (rim (walnut R)) e= _ from hA, show -(b*K+grossH (rim g') e+grossH (rim f) e)+R.beta *grossH _ _= -(grossH (rim g') e+grossH (rim f) e) from ?_,abs_neg]; swap; · unfold K b; abel
    exact (abs_add_le ..).trans (add_le_add (elo e R.path R.clip h.paths p hu he) (deposit h.labels hp hT g e he.le hG hx u _ hB hq (by omega)))
end YM.MSbar.Midpoint
