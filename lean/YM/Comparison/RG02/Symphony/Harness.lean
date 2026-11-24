import YM.Comparison.RG02.Symphony.Breeze
/-!
# First canonical steps on the Actual period P:Offer

Requires actual `Horizon.Suffices/Sworn`, which come from the same constructed Floral
when bound *once* (see Prima). Use compiler's Thermal/Kept identities and Push.Loops canonical
orientation of Hessian symbols, with its Θ/Γ etc. defined on that same Kin path. Compare on
any emitting input through W.Standard (rank≥0 vacuum only here). On the coarse mesh
scan all frequency radii and all frequency modes/plane phases (not physical state phase). No assertion of estimates after masks, nor that
`alpha` gives exact equality of Fk.2 on THIS torus -- keep error; prove Offer in the
period-limit later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly LocalScript Clarity
open Matrix Push.Loops Laurent Bloch YM.Work.F05 YM.Work.F03
open YM.AnalyticNext.QuarticMatch.Joint (shifts)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {P : RG.History G}
abbrev Project (P:History G)(k:ℕ) := fun i=> P.S.side k i
lemma climbs (P:History G) (k:ℕ) : Expands (Project P k) := tendsto_atTop_mono (f:=fun p=> (P.S.period p).val) (fun _=>Nat.le_mul_of_pos_right _ (P.S.denominator k).property) P.S.period_strict.tendsto_atTop
-- Universal port to periodic formal history from one Plan
variable (L:Bulk.Chain P) (N m r i:ℕ) (h:m<N)
local notation "Tq"=> L.horizon.H N m
local notation "C"=> P.levels.clock
local notation "ν"=> Project P m
local notation "α"=> L.kin.alpha N m
local notation "Q"=> L.kin.path N m
local notation "S" i=> (P.levels.clock.op m i)
set_option quotPrecheck false
local notation "p"=> (P.levels.params m).clip
namespace Seed
variable {t:ℕ}
def frame : ℝ:= L.post.Γ ((C).J (m+1))
def rate : ℝ:= L.post.c ((C).J (m+1))
def quote := P.levels.clock.loopCap (m+1) -- β-independent
variable (P) in
def issue (i:ℕ):= 4*(frame L m * (P.levels.clock.loopCap (m+1))* Real.exp (-rate L m * (P.S.side m i).val))
def second (H:Bed) (W:PathData G)(a:ℝ): SpecK G:= (a:ℂ) • kineticSymbol G H.metric + loopSymbol W
local notation "J"=> second Tq Q α
variable {V:Type}[Fintype V][DecidableEq V] {R:Census V}
    (F: Forest (P.levels.clock.op m i).ratio) (u:(P.levels.clock.op m i).Choices)(W:Bulk.Colors R G (P.S.side (m+1) i))
    (hr:2≤r)(hW:W.Standard)
local notation "X"=> fieldDir G (ν i) 1
local notation "g"=> mainTerm p Q ∘ (represent (G:=G) (n:=P.S.side m i))
-- `main` in code orientation Calibration.main.
local notation "g0"=> secondTerm p Q ∘ (represent (G:=G) (n:=P.S.side m i))
local notation "g2"=> Precision.loop Q ∘ (represent (G:=G) (n:=P.S.side m i))
local notation "Γ"=> ground (L.step N m i h) F u W r
local notation "a2"=> Thermal.actionResponse L N m i h F u W r
local notation "S0"=> KRow G Tq (ν i)
local notation "S2"=> loopPrice Q (ν i)
local notation "U"=> linksGrid G (ν i)
local notation "Y"=> chartEquiv G (ν i)
variable {Z:MapPrices}
    (H:L.horizon.Suffices Z)(HE:Bid.Sworn (L.horizon.H N m) (P.S.side m i) G)

-- ignore Lean section vars for budget lemmas
include h
private lemma g_jet : ContDiffAt ℝ ω g 0:= Extra.Iteration.Calibration.main_jet (L.planned.cap N m h.le)
private lemma g2_jet : ContDiffAt ℝ ω g2 0:= Bulk.loop_smooth p _ (L.planned.cap N m h.le)
include H HE
private lemma g_pairs (x z: BondKey G (P.S.side m i)→ℝ) : x ⬝ᵥ (KRow G (L.horizon.H N m) (Project P m i)*ᵥ z)= iteratedFDeriv ℝ 2 g 0 ![Y x,Y z] := by
    let B:= L.planned.cap N m h.le; let F0:= H.all N m h.le (ν i); let F':= L.planned.links N m h.le; let l(x d':X):= Bid.gaugeFiscal (Tq) x d'
    have hg (x:X):= main_limit B F' F0 HE x; rw [KRow_pair];
    exact ((hessian_of_limit (f:=g) (g_jet L N m i h|>.of_le le_top) hg gaugeFiscal_add (fun x d'=> by simp_rw [metric_pair _ B F' _ _ F0, real_inner_comm (Work.F03.faceCurl _ x), real_inner_comm (Work.F03.ellLine Q _ x)])).2.2 _ _).symm
private lemma g0_pairs (x z: BondKey G (Project P m i) → ℝ) : x ⬝ᵥ (KRow G (L.horizon.H N m) (Project P m i) *ᵥ z)=iteratedFDeriv ℝ 2 g0 0 ![Y x,Y z] := by
    have he : jet g 2=jet g0 2 := funext fun z=> Attach.sec_match z Q p (L.planned.cap N m h.le)
    have hg : ContDiffAt ℝ ω g0 0:= Extra.Iteration.Calibration.core_jet (L.planned.cap N m h.le)
    rw [g_pairs L N m i h H HE,← show iteratedFDeriv ℝ 2 (jet g 2) 0=iteratedFDeriv ℝ 2 g 0 from (Thermal.re_jet (g_jet L N m i h) 2 2).trans (if_pos rfl), he, Thermal.re_jet hg, if_pos rfl]
omit H HE in
private lemma g2_pairs (x z: BondKey G (Project P m i) → ℝ) : x ⬝ᵥ (loopPrice (L.kin.path N m) (Project P m i)*ᵥ z)= iteratedFDeriv ℝ 2 g2 0 ![Y x,Y z] := by
   let B:= L.planned.cap N m h.le; rw [← show bilinearAt (g2 ∘ (Y).toContinuousLinearMap) 0= loopPrice (L.kin.path N m) (Project P m i) from ?_, bilinearAt_dotProduct,← bend_apply,bend_linear _ (g2_jet L N m i h),bend_apply]; rfl
   let T:= g2; rw [show g2 ∘ (Y).toContinuousLinearMap=loop Q ∘ vary (1:Config G (P.S.side m i)) from funext fun x=> by change loop Q (represent _) = loop Q _; exact congrArg (loop Q) (represent_chart x)]
   exact (loop_jets_real B.width B.two).2.2
private lemma exactMatch (x z: BondKey G (Project P m i) → ℝ) : x ⬝ᵥ ((α • S0+ S2) *ᵥ z)=iteratedFDeriv ℝ 2 (draft (L.kin.alpha N m) Q p) 0 ![Y x,Y z]:= by
    rw [add_mulVec, dotProduct_add, Matrix.smul_mulVec,dotProduct_smul, g0_pairs L N m i h H HE,g2_pairs L N m i h,show (draft (c:=ν i) α Q p)=α • g0 + g2 from rfl,iteratedFDeriv_add_apply]; rotate_left 1
    · exact ((show ContDiffAt ℝ ω g0 0 from Extra.Iteration.Calibration.core_jet (L.planned.cap N m h.le)).const_smul (α)).of_le le_top
    · exact (g2_jet L N m i h).of_le le_top
    rw [iteratedFDeriv_const_smul_apply (f:=g0) ((show ContDiffAt ℝ ω g0 0 from Extra.Iteration.Calibration.core_jet (L.planned.cap N m h.le)).of_le le_top)]; rfl
lemma reserveO : Clarity.value (ground (L.step N m i h) F u W r 0)= KRow G (L.horizon.H N m) (P.S.side m i) := by
    let f := ground (L.step N m i h) F u W r 0
    have hz:f= (⇑(-Complex.ofRealCLM)) ∘ jet g 2 := funext fun x=> by unfold f; rw [precedence,Symmetry.price,Thermal.maps L N m i h F u,L.clips N i m h.le,L.selected N i m h.le]; rfl
    have hg:= levelJet (g_jet L N m i h) 2
    apply pairing_ext; intro x z; rw [reads (smooth_ground _ F u W r 0|>.contDiffAt), show ground _ F u W r 0= _ from hz, (-Complex.ofRealCLM).iteratedFDeriv_comp_left hg.smooth.contDiffAt le_top, g_pairs L N m i h H HE, Thermal.re_jet (g_jet L N m i h),if_pos rfl]
    simp
omit H HE
include hr hW h
lemma no_k (hG:G.Simple) : Clarity.value (ground (L.step N m i h) F u W r 1)=0:= by
    have hz: ground _ F u W r 1= (⇑(-Complex.ofRealCLM)) ∘ jet g 3 := funext fun x=> by rw [Orbit.Linked.id_cubic (P.levels.budget m) r L N m i h F u W hG (by omega) hW,L.clips N i m h.le,L.selected N i m h.le]; rfl
    have hg:= levelJet (g_jet L N m i h) 3; apply pairing_ext; intro x z; rw [reads (smooth_ground _ F u W r 1|>.contDiffAt), hz, (-Complex.ofRealCLM).iteratedFDeriv_comp_left hg.smooth.contDiffAt le_top,Thermal.re_jet (g_jet L N m i h),if_neg (by omega), Matrix.zero_mulVec,dotProduct_zero]; simp
omit hr hW in
private lemma projected (x z: BondKey G (Project P m i) → ℝ) : x ⬝ᵥ (Clarity.value (ground (L.step N m i h) F u W r 2) *ᵥ z) = iteratedFDeriv ℝ 2 (Thermal.actionResponse L N m i h F u W r) 0 ![Y x,Y z]:= by
   have hg:= g_jet L N m i h; let T:= ground (L.step N m i h) F u W r 2
   have ht: ContDiffAt ℝ ω T 0:= (smooth_ground ..).contDiffAt
   have he : a2=Clarity.real T-jet g 4:= funext fun x=> by
       unfold Thermal.actionResponse Clarity.real T ground; rw [L.clips N i m h.le,L.selected N i m h.le]; change - _ -_= -(detail (logVac _) _ _+ (if _ then _ else 0)).re - jet g 4 x
       rw [if_neg (by omega),add_zero]; rfl
   rw [he,Clarity.value,bilinearAt_dotProduct,← bend_apply,Clarity.full, bend_linear _ (Clarity.known ht),bend_apply, iteratedFDeriv_sub_apply ((Clarity.known ht).of_le le_top) ((levelJet hg _).smooth.contDiffAt.of_le le_top),Thermal.re_jet hg, if_neg (by omega : (2:ℕ) ≠ 4),sub_zero]; rfl
include H HE
lemma deviation :
    Breeze.Rule (Clarity.value (ground (L.step N m i h) F u W r 2)) (second (L.horizon.H N m) (L.kin.path N m) (L.kin.alpha N m)) (Seed.issue P L m i) := by
    let A:= Clarity.value (ground (L.step N m i h) F u W r 2); let X':= α • S0+ S2
    have hp := L.planned.cap N m h.le
    have he := (H.rows N m h.le).2.1
    have hl := loopRow_budget hp.width hp.two
    have hm : Compares U U (cmat S0) (kineticSymbol G (Tq).metric) 0:= Compares.of_routed fun _ _ hh=> kinetic_routed G _ (Row.rights _ _ he (Z.alpha_pos _).le) hh
    have hx : Compares U U (cmat (X')) J 0:= by
       unfold X' second; rw [map_add,map_smul, show α • cmat S0=(α:ℂ) • cmat S0 from ?_]; swap; · ext i j; exact Complex.real_smul ..
       have hv:= (hm.smul (α:ℂ)).add (loop_compares (Row.rights _ _ hl hp.width.le)); rwa [mul_zero, add_zero] at hv
    rw [show Clarity.value _ =_ from (show A=X'+(A-X') by abel),← zero_add (Seed.issue P L m i)]; apply Breeze.shifted X' (Breeze.accepts_zero X' hx); intro k i' x d'
    unfold Seed.issue frame rate
    apply Breeze.pointed; intro k i' σ τ Hσ Hτ Y0
    rw [sub_mulVec,dotProduct_sub,show ∀ x l, x ⬝ᵥ (A *ᵥ l)= _ from fun x l=> projected L N m r i h F u W x l, show ∀ x z, x ⬝ᵥ (X' *ᵥ z)=_ from fun x z=> exactMatch L N m i h H HE x z,show ∀x:fieldDir G (P.S.side m i) 1,Y (Y0 x)=x from (Y).apply_symm_apply,show ∀x:fieldDir G (P.S.side m i) 1,Y (Y0 x)=x from (Y).apply_symm_apply]
    have he := Thermal.sample_kin L N m i h F u W hW r hr k i' σ τ Hσ Hτ; dsimp only at he; rw [L.selected N i m h.le,L.clips N i _ h.le] at he; simpa only [mul_assoc,Project] using he
omit H HE hW hr h
lemma season : Tendsto (Seed.issue P L m) atTop (𝓝 0):= by
   let s:= Project P m; have he := exp_error_limit (s:=s) (climbs P m) (L.post.posC ((C).J (m+1))) (frame L m*(P.levels.clock.loopCap (m+1))); simpa only [Seed.issue,rate,mul_zero,Project,s] using! he.const_mul 4
end Seed
end YM.Comparison.RG02.Symphony
