import YM.Juniper.Caret.Regular
import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Push.LOCAL_SPLITTING.Projection
/-!
 # Caret stage C. L-∞ projection true normalized conditional **germ**
 at 0, actual section all addresses; qt threshold actual.

 Literal support version. Do NOT apply at arbitrary test locations yet. This
 adapter's `Pass` is the relative coefficient inside the Wilson density
 including the extensive vacuum, not the naive expectation projection.
 NOT `Push.Local.project` (wrapping skips!). Bounds include traversal.
 Only use on physical origin & Services; here we prove *why* can use on this
 shape. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Caret
open Function Filter Lattice MeasureTheory Wilson RG Input
open PhysicalNext.Repeat Lantern Next.Foundations
open ConnectedActivityE6 Blaze Brush Analysis Work.G05
open Measure Metric Set Labels Extra.Histories Source
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n d : ℕ}
section period
variable (F:Labels.Frame G d){N:Side} (o: Site N) (B: SectionData F)(H: Hol G) (R: Rep G N)
local notation "θ"=> R.p.threshold
local notation "V"=> (Config G N)
local notation "D"=> (Directions G N)
variable (P: Coefficient F N){w:ℝ}{u:ℝ}

abbrev ratio (R: Rep G N) (f: Config G N→ℂ) := fun v=> f v / (R.eval v:ℂ)
local notation "W"=>Push.Local.Probe G d
-- uses germ *of evaluated ratio*, normalized ∏ θ, no masks. total for any V. no claim that
-- ratio agrees when denominator globally off (this is why inside proof needs `flat_flags`).
structure Pass (f: Config G N→ℂ) (v:F.Coeff):Prop where
    listens (i:Push.Local.Probe G d) :
      ContDiffAt ℝ d (ratio R f ∘ H.testLinks d o (θ • i.1)) 0 ∧
      Push.Local.runProbe F i v= iteratedDeriv i.2.val (ratio R f ∘ H.testLinks d o (θ • i.1)) 0
noncomputable def naturalK (f:Config G N→ℂ): F.Coeff:= if h:∃ v,Pass F o H R f v then h.choose else 0
local notation "Δ"=> naturalK F o H R
variable {F o H R}
lemma Pass.unique {x y:F.Coeff}{f: Config G N→ℂ}(h:Pass F o H R f x)(g:Pass F o H R f y):x=y:=by
   obtain ⟨T,C,hC,hH⟩:= Push.Local.probe_budget F
   have ht:= hH (x-y) 0 (le_refl _) (fun i _=>by rw [map_sub,(h.listens i).2,(g.listens i).2,sub_self,norm_zero]); rw [mul_zero] at ht; exact sub_eq_zero.mp (Work.G08.size_separates F _ ht)
lemma Pass.is_natural {f:Config G N→ℂ}{v:F.Coeff}(h:Pass F o H R f v) : Δ f=v:= by
   unfold naturalK; split
   next ht=> exact ht.choose_spec.unique h
   next he => exact False.elim (he ⟨_,h⟩)
lemma Pass.sub {f g : Config G N→ℂ}{x y:F.Coeff}(h:Pass F o H R f x)(k:Pass F o H R g y) : Pass F o H R (f-g) (x-y):= by
  constructor;intro i; let L:= H.testLinks d o (θ • i.1); obtain ⟨he,hz⟩:= h.listens i; obtain ⟨hd,hP⟩:=k.listens i
  let u:=ratio R f ∘ L; let v:=ratio R g ∘ L; rw [show ratio R (f-g) ∘ L=u-v from funext fun i=> by simp [ratio,u,v,sub_div]]; refine ⟨he.sub hd,?_⟩
  rw [map_sub,iteratedDeriv_sub]; simp_rw [hz,hP]; rfl
  exact he.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ i.2.isLt))
  exact hd.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ i.2.isLt))
lemma Pass.scale {f:Config G N→ℂ}{x:F.Coeff}(h:Pass F o H R f x)(c:ℂ) : Pass F o H R (c•f) (c•x) := by
  constructor; intro i; let L:= H.testLinks d o (θ • i.1); obtain ⟨he,hz⟩:= h.listens i; let u:= ratio R f ∘ L; rw [show ratio R (c•f) ∘ L=c•u from funext fun i=> by simp [ratio,u, mul_div_assoc]]
  refine ⟨he.const_smul c,?_⟩; rw [map_smul,iteratedDeriv_const_smul (he.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ i.2.isLt)))]; exact congr_arg (c • ·) hz
lemma Pass.add {f g : Config G N→ℂ}{x y:F.Coeff}(h:Pass F o H R f x)(hy:Pass F o H R g y) : Pass F o H R (f+g) (x+y):=by simpa only [neg_one_smul,sub_neg_eq_add] using h.sub (hy.scale (-1))

variable (o H R)
lemma near_test (v:Jet G) : ∀ᶠ t:ℝ in 𝓝 0, flags R.p.threshold (H.testLinks d o v t)=∅:=by
   have he : Tendsto (increment (1:Config G N)) (𝓝 0) (𝓝 1):=by simpa only [Work.G07.at_zero_increment] using ((show Continuous (increment (1: Config G N)) by unfold increment; fun_prop).tendsto 0)
   have hu: Tendsto (H.testLinks d o v) (𝓝 0) (𝓝 1):= (he.comp (testLog_zero H d o v ▸ (testLog_diff H d o v).continuousAt.tendsto)).congr' (increment_testLog H d o v).symm
   exact hu.eventually (flat_flags N R.p.threshold R.p.threshold_pos)

variable (F)
lemma appears (i:W){v: Label G d}{f: Config G N→ℂ}(he:JetTest H o v f): Push.Local.runProbe F i (F.scaled θ (F.coords v)) = iteratedDeriv i.2.val (f∘ H.testLinks d o (θ • i.1)) 0:=by
     rw [Push.Local.runProbe_eq]; simp_rw [read_frame_scaled,LinearEquiv.symm_apply_apply, show ∀ h:ℝ, θ • scaleJet i.1 h=scaleJet (θ • i.1) h from fun h=> funext fun j=> smul_comm θ (h^(j+2)) (i.1 j)]; exact ((he (θ • i.1)).2.2 _ (Nat.le_of_lt_succ i.2.isLt)).symm

def Sits (N:Side) := ∀ x∈B.stencil,∀ i:Axis,20*((x i).natAbs+1) ≤ N.val
def veil := fun U=> ∑' i, P.regular i U
local notation "Γ"=> veil F P -- F argument explicit because F fixed?
local notation "Λ"=> H.testLinks d o
local notation "Z₀"=> B.places (F.scaled θ⁻¹ P.x) o
local notation "θ'"=> R.p.threshold
local notation "Ω"=> P.density o B R

-- adapt CutoffProjector.Stencil, retain tsum. No assertion f on bad-field. exactly local proof.
lemma unveil (u: Config G N)(hu:flags R.p.threshold u=∅)(h:B.Sound H): ratio R Ω u= Z₀ u+veil F P u:= by
   have hv := Activities.gas_one R.activities R.p hu; have hr : (R.eval u:ℂ) ≠ 0:= Complex.ofReal_ne_zero.mpr (by rw [Rep.eval,hv,mul_one]; exact (Real.exp_pos _).ne')
   have ht : ∀ b,P.marked R b u=0:=by
     intro b; unfold Coefficient.marked; split; swap; · rfl
     rename_i hb; suffices b=∅ by rw [this]; simp
     by_contra hi; obtain ⟨i,hi⟩:= Finset.nonempty_iff_ne_empty.mpr hi; obtain ⟨v,hV⟩:= (R.activities.forced i).inventory_ne; exact Finset.notMem_empty v (hu ▸ (show v∈flags _ u by rw [← hb.2]; exact Finset.mem_biUnion.mpr ⟨i,hi,hV⟩)) -- implicit
   have hh (S:Support N):Healthy θ S u:= by unfold Healthy; rw [hu]; simp
   have hZ : P.exponentialEntry o B R u=(Z₀ u+veil F P u):= by
      unfold Coefficient.exponentialEntry veil; simp_rw [Coefficient.maskedTerm,masked_eq _ _ _ u (hh _)]; congr 1
      nth_rw 3 [← Size.core_plus F P.x]; rw [map_add,map_smul,F.scaled_unit]; unfold SectionData.places; simp only [B.eval_linear.map_add,B.eval_linear.map_smul,h.unit,Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]; ac_rfl
   unfold ratio; rw [Coefficient.density]; simp_rw [ht]; rw [tsum_zero,mul_zero,add_zero,hZ,mul_comm]; field_simp
variable (hSit : Sits F B N) -- check arg order N
variable (hp : P.Format o H R)(hb:P.remBound o R w u)(hk:d ≤ R.p.order)(h : B.Sound H)
include hp hk hb
private lemma veil_eth : ContDiffAt ℝ (d:WithTop ℕ∞) (veil F P ∘ increment (1:Config G N)) 0 :=by
   obtain ⟨a,b,-,-,-,-,⟨f,hf,hA⟩,-⟩:=hb
   have hv : Summable f:= Summable.of_nonneg_of_le (fun i=> (hA i).1) (fun i=> R.p.loMass _ _ (hA i).1) hf.2.1
   obtain ⟨c,hc⟩:= complete R.p P.regular o hk hp.smooth hA; exact (german hc (hv.mul_left c)).1

include hSit h
lemma bills : Pass F o H R Ω (naturalK F o H R Ω):= by
   obtain ⟨v,he,hx⟩:= read_projection H o d (veil F P) (fun k u=> tsum_congr fun i=> (hp.smooth i).symmetry k u) (veil_eth F o H R P hp hb hk)
   let x:= F.scaled θ (F.coords v)
   have hV:JetTest H o (F.coords.symm (F.scaled θ⁻¹ P.x)) Z₀:=by
     have hT:= placed_reads (H:=H) B o hSit h (F.scaled θ⁻¹ P.x); rwa [Reads,if_pos (nonwrapping_placement B o hSit)] at hT
   have hf: Pass F o H R Ω (P.x+x):= by
      constructor; intro i; let z:= θ • i.1; let p:= Λ z; let u:= Z₀ ∘ p; let w:= veil F P ∘ p
      have ht:ratio R Ω ∘ p=ᶠ[𝓝 0] u+w:=(near_test o H R z).mono fun t ht=> unveil F o B H R P _ ht h -- H order
      have hu:ContDiffAt ℝ d u 0:=(hV z).1; have hw:ContDiffAt ℝ d w 0:=(he z).1
      have hy:= Nat.le_of_lt_succ i.2.isLt; refine ⟨(hu.add hw).congr_of_eventuallyEq ht,?_⟩
      rw [ht.iteratedDeriv_eq, iteratedDeriv_add (hu.of_le (Nat.cast_le.mpr hy)) (hw.of_le (Nat.cast_le.mpr hy)),map_add]
      have hP := appears F o H R i hV; rw [F.coords.apply_symm_apply, F.scaled_inv R.p.threshold_pos.ne'] at hP; exact congr_arg₂ (·+·) hP (appears F o H R i he)
   rw [hf.is_natural]; exact hf
end period
end YM.Juniper.Caret
