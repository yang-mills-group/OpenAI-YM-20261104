import YM.RG12.Arche.Unmarked
import YM.RG12.Rail.Wagon
/-! `earnings` port on the same data. Only mural casting adapted.
    Then variable lamp lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Ribbon Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B: Binding C)(H:C.Makes)(h: G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r D) (O:HaarBudget G) (J:ChartRatio G) {i k N p D0 m n d s:ℕ}
set_option quotPrecheck false
local notation "AX" => C.path.levels
variable (M:Tapes.Panel d) {z l v:ℝ}
local notation "ξ" => M.bag ((AX).clock.J k)
open YM.RG12.Rail
-- users take ax layout, but ANY fixed separated shape is equally authorized; no RP claim elsewhere
variable {a:Points (m+1)}(hβ:a∈conf _)
set_option quotPrecheck false
local notation "kr" k:max=> {x:Points (m+1) | Anemos a (C.path.levels.clock.monitor k) x}
include H h hp hβ
section
open Accent
variable {Kz:Set (Points (m+1))} {d0 : Fin (m+1)→ℕ}
variable (hZ:∀ i≤d, generator G i≤z)
include hZ
-- joint
omit hβ hp hZ in
private lemma muralR {K:Points (m+1)}{d0:Fin (m+1)→ℕ}(hi:∀ i,d0 i ≤ d)(g:(i:Fin (m+1))→ C.label (d0 i))(_ha:K ∈ conf _)(b:ℝ)(hb:6 ≤ b)(hs:∀ i,saves C (d0 i)+3 ≤ b) (D:ℕ) :
   ∀ᶠ k in atTop, Walls b hi g {x:Points (m+1)| Anemos K (C.path.levels.clock.monitor k) x} D k:=by
   let Y (k:ℕ) x:= tested C.path.levels b k (x:Points (m+1)); have hr:0 < b:=by linarith
   let w:= C.path.levels.clock.monitor
   have hp: ∀ᶠ k in atTop,∀ x:Points (m+1),Anemos K (w k) (Y k x)→ Balcon b hi g x k D := by
     apply YM.RG12.Rail.scope
     intro χ hx v t hv ht s hs₀; let T:=jointX g
     obtain ⟨z,hz⟩:= profile_wind K _ha t (fun i=>(hv i).1) hs₀ T
     have hz': Tendsto (fun i=>Read.maxProfile C (Y (χ i) (v i)) T) atTop (𝓝 z):=by
        simp_rw [show ∀ i,Y (χ i) (v i)=t i • K from ht]; exact hz
     filter_upwards [hx.eventually (passingX_all h H D hi g b hr hs),clockR h _ha χ hx v t (fun i=>(hv i).1) ht hs₀ D d hr, coughR h _ha χ hx v t (fun i=>(hv i).1) hs₀ T ht,
         Glimmer.accumulate ℕ atTop (fun i=> Read.maxProfile C (Y (χ i) (v i)) T) z hz' _ ((hat_rate C.path.levels h).comp hx)] with k H1 H2 H3 H4
     exact ⟨H1,H3,H2,H4⟩
   let V k (x:Points (m+1)) (h:Fit C.path.levels b k x) : Prop := Allowed C.path.levels b k →
       (∀ p N (hN:k≤N),Edition.Spaced (Spindle.scouts C k) (seats C b x hN p)) ∧
       ∀ p Ψ,Wall.Vantage C.path.levels d k p (m+1) D b Ψ → Bell C.path.levels Ψ d D h
   have hw:∀ᶠ k in atTop,∀ x:Points (m+1), Anemos K (w k) (Y k x)→ ∀ h, V k x h:=by
      apply YM.RG12.Rail.scope; intro χ hx v t hv ht s hs
      filter_upwards [Wall.on_bearing C.path.levels b D d h _ha hb χ hx v t (fun i=>(hv i).1) (fun i=>(hv i).2) ht hs, Edition.rise_wind C K h _ha hr χ v hx t (fun i=>(hv i).1) ht] with k hC HH h1 h2
      exact ⟨HH h1 h2,hC h1 h2⟩
   filter_upwards [hp,hw] with k hP hV; exact ⟨hP,hV⟩
lemma earningsR (g:(i:Fin (m+1))→ C.label (d0 i))(hm:m+1 ≤ n)(hz:2≤n) (hi:∀ i,d0 i≤d): ∀ᶠ k:ℕ in atTop,
    let α:= M.bag (C.path.levels.clock.J k)
    let _s:= clim C.path.levels k
    ∀ (l v:ℝ) (L: LegacyCost B J (-3) z α k n d O l v),∀ N (p:ℕ)(hk:k<N) V (_X:Actum B H O J M L V hk),∀ x:Points (m+1),tested AX α.band k x ∈ kr k→∀ h:Fit AX α.band k x,
    ∀ (T:(i:Fin (m+1))→ StampDuty C k N p (d0 i) α.taylor V α.era.coast.Q (stamp AX N p)),∀ f:(i:Fin (m+1))→ C.label (d0 i),(∀ i,Solves C (mag AX α.band k) (d0 i) k N p (T i).T (g i) (f i)) →
    ∀ (s : modes (Fin (m+1))) (_:s.val.Nonempty),
      (Ship.yard C α.band hk.le p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX g) (q_asked (C:=C) f) h N p U).part s) ≤ Ship.budget C.path.levels n k:=by
   have hc : 6 ≤ M.arc:=by linarith only [M.huge,Nat.cast_nonneg (α:=ℝ) d]
   have ha : 0 < M.arc:=by linarith only [hc]
   have hQ (t i:ℕ)(h: i ≤ d) : M.arc*i+saves C i ≤ (M.bag t).credit:=by
       have hz:= mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (show 0≤ M.arc from ha.le); linarith only [M.loose t,hz,Next.Rank.Tapes.savings C i,show (i:ℝ) ≤ d from Nat.cast_le.mpr h]
   have hr(i):= StampDuty.procure C h H (d0 i) M.θ (g i) M.arc ha M.currency (show M.currency+M.arc*d0 i + saves C (d0 i)≤ -8 by rw [← M.vital 0];linarith only [(M.bag 0).fits,hQ 0 (d0 i) (hi i)])
   obtain ⟨u,hU⟩:= eventually_atTop.mp (Ship.banking C.path.levels O h)
   filter_upwards [muralR H h hi g hβ M.arc hc (fun i=> by linarith only [Next.Rank.Tapes.savings C (d0 i),M.huge,show (↑(d0 i):ℝ) ≤ ↑d from Nat.cast_le.mpr (hi i)]) M.θ,
     eventually_all.mpr hr,eventually_all.mpr fun i=> (hat_rate AX h).eventually (tremor M.currency (hZ _ (hi i))), eventually_ge_atTop (C.ref d), eventually_all.mpr (fun i=> eventually_ge_atTop (C.ref (d0 i))),Radian.commissioned AX h d 2 (by decide) chartHeat_pos,(hat_rate AX h).eventually Flux.timing, (AX).fits.deep.eventually_gt_atTop ((AX).clock.J u)] with k hM ht hv hh hl Hq hv' hD
   intro α l v L N p hN V X x hy hX T f hf; obtain ⟨he',P,rfl,hP⟩:=X
   let b:= α.band; let s:= clim AX k
   have hY:α.taylor=M.θ:=M.stable _; have hy':b= M.arc:= M.factor _
   have hm' : Walls b hi g (kr k) α.taylor k:=by rw [hY,hy']; exact hM
   have hT:= L.age.allot.permitted; let m0:=Station.width AX b k
   have het(i) : Perch.bill M.currency s* Spindle.moneys C (d0 i) k N p (f i) ≤ Perch.bill (-8) s ∧ Rise.coin ((T i).W (f i))≤ α.principal s := by
      obtain ⟨T0,-,hW,hS⟩:= reborn (j':=α.era.coast.Q) (β:=P k) hY (T i) rfl rfl rfl; have hv : T0.T=(T i).T ∧ T0.W=(T i).W:=⟨hW,hS⟩
      have hφ:Solves C (mag AX M.arc k) _ k N p T0.T (g i) (f i):=by rw [hv.1, ←hy']; exact hf i
      obtain ⟨hj,he⟩:= ht i (hY ▸ L.moves.year) N p hN.le T0 _ hφ; rw [hv.2] at he; exact ⟨hj,he.trans (Glimmer.billed _ (hQ _ _ (hi i)))⟩
   have hΩ:u ≤ m0:=by
      by_contra! he; have hh : (AX).clock.J m0=(AX).clock.J k:= hT.plateau _ (le_refl _) ((wider ..).trans (before ..)); exact not_lt_of_ge (hh ▸ (AX).fits.mono he.le) hD
   apply y_ready B H J L (hf:=hh) hP (le_trans ha.le (Eq.le (M.factor _).symm)) (hU _ hΩ) hv' (fun h=> Hq _ _ h) hl hi T g f hf hm' hy hX hz hm _ (fun i=> (het i).2)
   · intro hd; let Q:= C.path.rep N p k; let y:= seats C b x hN.le p; let r':= Hat s^z
     have hu:0 < r':=Real.rpow_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (C.path.levels.fits.delayed _)))) _
     have he: Edition.Spaced Q.p.B y:= by rw [show Q.p=(AX).budget k from (H.wilson.represents N p k hN.le).vac]; exact hd
     refine caughtX C N k p m f b x hN H hl _ hp.1 ⟨fun _ _ i hi j hj hh=> he i j hh⟩ (fun a=> (Extra.Multi.Occupancy.of_injective (injected _ y Q.p.B_pos he) a).trans (hp.2 k)) hu (fun i=> ?_)
     exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Spindle.paid_pos ..) (C.path.levels.params k).columns_ge) hu.le).trans (hv i _ (Spindle.money_nn ..) (het i).1)
   intro i; rw [Purse.cash,M.vital]; exact (het i).1
end
end YM.MergeProof
