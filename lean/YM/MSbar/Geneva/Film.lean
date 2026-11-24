import YM.MSbar.Geneva.Eject
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab Bristol
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{X f g:ℕ→ℝ}{A:ℕ→Issue G}(hX:Tendsto X atTop atTop) {p m k q:ℕ}
variable (χ:ChartRatio G)(J:Voice G)(H H':Stage)(P:Patch)(D:KernelChoices)
variable (h:G.Simple) (hD:P.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
variable (M:StageCost)(i':G.ColorIndex){b:ℝ} (hp:∀ᶠ i in atTop,Paid (A i) P H H' J (X i)) (hq:∀ᶠ i in atTop,(A i).S.kernel=D)
variable (hc:∀ᶠ i in atTop,Festival (A i) χ p i'∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f i) b∧ Issue.Receipt (A i) M (X i))
variable (hR:∀ᶠ i in atTop, Ore M (X i) P)(h₁:p+2 ≤ m)(ha:Run atTop X f 0)(hk:k=m+1)(hμ:4≤ m)
variable (hv:∀ᶠ i in atTop,k ≤ (A i).post.p.order)(hP:∀ᶠ i in atTop,hatW (tip G P.L (X i))^4 ≤ (A i).f.val)
local notation "Y₀"=>fun i:ℕ=> tip G P.L (X i)
local notation "Q₀" i=> X i
local notation "v₀" i=> vol (Y₀ i)
local notation "W₀" i=> hull (X i)
local notation "Z!" i=> Issue.preModel (A i) χ p
local notation "θ" i=> Meauring.chart (A i).f G
local notation "Λ" i=> ((A i).F)
local notation "Yx" i=> 5*goalP (Y₀ i) p
local notation "α" i=> αm (X i)
local notation "L"=> (P.L.val:ℝ)
variable {C:ℝ}(hK:Ready P M m C) (hσ:3 ≤ M.sway)(hN:6 ≤ M.s)
include hχ hp hq hX h hc hD hQ hR h₁ ha hk hμ hv hP hK hσ hN
variable (hn:∀ᶠ i in atTop,hatW (X i)^4 ≤ (A i).c.val)(hY:Kappa m C (1024*b)<1)
include hn hY
structure Gain (A:Issue G)(χ:ChartRatio G)(p m s:ℕ)(x:ℝ) :Prop where
   leaf:JetTab.RangeB (Measuring.chart A.c G) s (αm x) (vol x) (A.filmY χ p) m (goalP x p)
   economics:|A.shiftClock-taste p A.tilt A.cClock|≤ goalP x p
   keel: ∀ i∈closedBall (0:Positions (Primary A.c G)) (vol x),ContDiffAt ℝ (↑(m+1:ℕ)) (Issue.filmY A χ p) i
lemma pensionQ :∀ᶠ i in atTop,Gain (A i) χ p m M.s (X i):=by
     have hf:= shrinkR hX χ J H H' P D h hD hQ hχ M i' hp hq hc hR h₁ ha hk hμ hv hP hK hσ hN hn hY
     filter_upwards [hp,hf] with i hv he; -- curvet all global
     let Q:=A i; let R:= (A i).post; let Tv:= Aqua.vine R Q.cClock; let F(v):= PPress (A i).S Q.pre.beta v Q.pre
     let s:ℕ:=m+1; have h:= hv.payments.case_.lawful; have ht:=hv.payments
     have hy(v): ContDiff ℝ s (PPress (A i).S (A i).pre.beta v (A i).pre):= Tonic.curvet _ _ ht.bends.1 _ _ _ _ _ _ h _
     have hz: ContDiff ℝ s Tv := by
         let P(y):= (PPress (A i).S Q.pre.beta Q.cClock Q.pre) y
         have hp: ContDiff ℝ s (logK P):= (hy _).log (fun _=> (Tonic.base _ _ _ ht.bends.1 _ _ _ _ _ _ h ht.shine).ne') -- hp supplies
         have hK :=splice (A i).pre (A i).cClock R.path R.clip ht.bends.1 h ht.shine R ht.taskEval.symm rfl rfl; let f :=fun _ :Positions (Primary (A i).c G) => Real.log (nut (A i).S (A i).pre.beta G); rw [show Tv=logK P - f from ?_]; exact hp.sub contDiff_const; refine eq_sub_of_add_eq ?_; funext i; exact (add_comm _ _).trans (congr_fun hK i).symm
     exact ⟨he.1,he.2,fun x _=> hz.contDiffAt.sub ((Aqua.pure ..).contDiffAt.of_le le_top) ⟩
omit hp hq hX hc hR ha hv hP hn
variable (f:ℝ→ℝ)(hu:Run atTop id f 0)
-- universal sequencewise
include hu
lemma receipt : ∀ᶠ x:ℝ in atTop, Ore M x P → ∀ A:Issue G,Paid A P H H' J x → A.S.kernel=D → Festival A χ p i' → ClockD A p m M.s x→Cs A χ M.s p m x i' (f x) b → Issue.Receipt A M x → k ≤ A.post.p.order → hatW (tip G P.L x)^4 ≤ A.f.val →hatW x^4 ≤ A.c.val →Gain A χ p m M.s x:=by
    let Q (x:ℝ) :=Issue G; let U(x:ℝ)(A:Issue G):Prop:= Ore M x P∧Paid A P H H' J x∧ A.S.kernel=D∧ Festival A χ p i'∧ClockD A p m M.s x∧Cs A χ M.s p m x i' (f x) b∧Issue.Receipt A M x∧ k ≤ A.post.p.order ∧ hatW (tip G P.L x)^4 ≤ A.f.val ∧hatW x^4 ≤ A.c.val
    let X(x:ℝ)(A: Issue G):Prop:= U x A → Gain A χ p m M.s x
    suffices H: ∀ᶠ x:ℝ in atTop,∀ A:Issue G,X x A by
        filter_upwards [H] with x hx hr A a b c d e f g j n; exact hx _ ⟨hr,a,b,c,d,e,f,g,j,n⟩
    refine cofi (S:=U) ?_; intro x a he Hs
    have hC:∀ᶠ i:ℕ in atTop, U (x i) (a i):=Eventually.of_forall Hs; unfold U at hC
    exact pensionQ (A:=a) he χ J H H' P D h hD hQ hχ M i' (hC.mono (fun _ hh=>hh.2.1)) (hC.mono (fun _ hh=> hh.2.2.1)) (hC.mono (fun _ ⟨_,_,_,a,b,c,d,h⟩=>⟨a,b,c,d⟩)) (hC.mono fun _ hh=> hh.1) h₁ (hu.subclock he) hk hμ (hC.mono (fun _ hh=>hh.2.2.2.2.2.2.2.1)) (hC.mono (fun _ hh=>hh.2.2.2.2.2.2.2.2.1)) hK hσ hN (hC.mono (fun _ hh=>hh.2.2.2.2.2.2.2.2.2)) hY
end YM.MSbar.Geneva
