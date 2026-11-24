import YM.RG01Estimate.Covering
/-!
 # Exact compatibility on PERIOD and all real Vir. Not using Π forecast series
 here. Universal author Strat on actual and LCM auxiliary uses, still meaningful
 when small-mult loops allowed. Space for larger angles booked explicitly. Requires
 enough volume and ratios in AND gates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Board
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard
open Abacus Evoc Deck AbsoluteSums.Animals Trio
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{U:Alloy X D}(R:Factor U)
   {c f c' f' C F:Side}{N m d n i j r:ℕ} (Hm:m < N) (H : f.val=c.val*(U.B.a.S.block m).val) (H' : f'.val=c'.val*(U.B.a.S.block m).val)
local notation "J" => U.B.a.clock.J (m+1)
local notation "I" => U.B.a.clock.J m
local notation "L" => D.L (U.B.a.clock.J (m+1))
local notation "B" => U.B.a.budget m
local notation "B'" => U.B.a.budget (m+1)
local notation "W" => R.shape
local notation "χ" => Chi.canonical
local notation "γ" => U.B.kin.alpha N m
local notation "Z'" => R.expense J I
set_option quotPrecheck false
local notation "b'" => (U.B.a.S.block m)
local notation "D₀" => (R.target J I).halo
local notation "t" => radiusB (U.B.a.clock.hatBeta m)
variable {Y:Type} (β:ℝ) (h: Insured U N m d H β Y)(p:Chartlet R.shape U N m H h.rep)
   (hp:SeekR R.shape U N m H p) (r:ℕ) (X₀:Finset Y)
local notation "p₀" => optic D₀ t d
local notation "q''" => house D₀ t d (Fate.steps r)
local notation "Z₀" => Meadow.studio D₀ t
include R Hm hp
lemma morals (g:ℕ)(k:ℕ)(hn:q'' ≤ g)(hm:Z₀≤ g) (x:Site c): (B).Regular (neighbors g x) (Evoc.aspect p h.music (Fate.steps r) χ γ X₀ k x):= by
    rw [← Evoc.pasture p h.music r h.sacrifice h.coverage χ B γ k X₀ h.cost rfl hn hm]
    let K:=Match.staple (H:=p) («J»:=p) rfl rfl rfl
    let π:=Evoc.board p h.music r X₀ k
    let Y:=Pruned.low p χ K h.sacrifice r γ
    apply Rack.plating
    let fQ := Caddy.entries p π; let S:=Beam.marquee p B; have hz:= all_pay R Hm H p hp K
    have ht:= Caddy.low_inherits B χ p K γ h.sacrifice r hz
    let V:= Caddy.cut χ p K γ h.sacrifice r π
    have he:= Acquire.budget_cut (fun i=> i∈fQ) (Abacus.charted (A:=S) (F:=Y) B ht)
    convert he using 1
    ext1 i; rw [Caddy.equals_in]
    by_cases hv:i∈Caddy.entries p (Evoc.board p h.music r X₀ k)<;> simp [*,fQ,π,Y,K]

omit hp
section circles
local notation "h'''" => (normal)
include hp
omit hp
variable (h': Insured U N m d H' β Y)(p':Chartlet R.shape U N m H' h'.rep)

-- Need at least one common lcm placement (also for aux with main).
def Clockset (F : Insured U N m d H β Y)(F' : Insured U N m d H' β Y): Prop:=
   let C:= c*c'; let t₀: C.val=c.val*c'.val:=rfl; let t₁:C.val=c'.val*c.val:= mul_comm ..
   let D':=C*(U.B.a.S.block m); let K':D'.val=C.val*(U.B.a.S.block m).val:=rfl
   ∃ (P: Insured U N m d K' β Y) (v:2≤ c.val) (w:2≤ c'.val), reports H K' β F P t₀ v ∧ reports H' K' β F' P t₁ w

lemma coverUp (η:ℕ) (hσ:q''+p₀+5≤ η)(hu:Z₀≤η)(hc:4*η+16≤ c.val)(hC: 4*η+16≤ c'.val)(hA : Clockset H H' β h h')(he : β∈ Shoot.band U.B.a (m+1)) (k:ℕ) : Trio.Compatible (Evoc.aspect p h.music (Fate.steps r) χ γ X₀ k) (Evoc.aspect p' h'.music (Fate.steps r) χ γ X₀ k) (B) η:= by
   let M:= c*c'; let D:= M*b'; have h₀:M.val=c.val*c'.val:=rfl; have h₁:M.val=c'.val*c.val:=mul_comm ..; have H₁: D.val=M.val*(U.B.a.S.block m).val:=rfl
   obtain ⟨Z,Hh,Hw,hZ,hT⟩:=hA; change Insured U N m d H₁ β Y at Z
   intro x y V W₁ hx hy hP
   have ht : c.val≤ M.val:= Nat.le_mul_of_pos_right _ c'.pos
   obtain ⟨u,pL⟩:=authorizes R H₁ Z.rep (p.laws.data.room.buys.trans ht) (by rw [Z.β']; exact he) Z.pathU Z.clip Z.point Z.legal Hm
   let VA:= Lattice.translate x V; let VB:= Lattice.translate y W₁
   have hV: flags (B).threshold VA=∅:= by unfold VA; rw [← Lattice.pull_one]; exact Pane.tranquility V hx ..
   have hW: flags (B).threshold VB=∅:= by unfold VB; rw [← Lattice.pull_one]; exact Pane.tranquility W₁ hy ..
   have hk:=retros R Hm H H₁ β (h) Z X₀ p u r k h₀ Hh (by omega) hZ 0 VA hV
   have hz:=retros R Hm H' H₁ β h' Z X₀ p' u r k h₁ Hw (by omega) hT 0 VB hW
   rw [map_zero] at hk hz
   let A:=aspect u Z.music (Fate.steps r) χ γ X₀ k 0; have hr : (B).Regular (neighbors η 0) A:= morals R Hm H₁ β Z u pL r X₀ η k (by omega) hu 0
   have he {G:Gauge}{c:Side} (p: Offer G c)(h:Trio.Mirrors p)(x:Site c)(V:Config G c): p x V=p 0 (Lattice.translate x V):= by
       rw [← Lattice.pull_one,h]; simp [Lattice.affine]
   rw [he _ (reflections _ _ _ _ _ _ _) x V,he _ (reflections _ _ _ _ _ _ _) y W₁, ← hk, ← hz]
   apply hr.sites _ _ (Slide.readNear (Z:=η) 0 (by omega) ?_); rw [Slide.rolls,Slide.rolls,map_zero,map_zero]; rw [Slide.increases,Slide.increases]; exact hP
end circles
end YM.RG01Estimate.Board
