import YM.LocalLTE.Motion.Germ
/-! Kernel bills ready. clauses α births. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Bakers
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ κ k: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
local notation "K"=> Veil c f
local notation "E"=>Disk G c
variable (D:Finset (Veil c f)) (I:Finset (Tubular f G))(H: Cash W t μ L Q o a T R)(he:X.x=t)(hK:X.width=o.K)
include H he hK
variable (hs:Stamp T)
include hs
lemma outset (z:Air f G)(k : Cell f): Pressure.toll (inputΛ X z 0) k <R.p.threshold/2:=by
    let Z:=(timeΛ X (0:Disk G c)); have hz:Z=X.blank:= by unfold Z timeΛ Vine.pass dry; rw [show ((0:Disk G c).snd,(0:Directions G f)).1=0 from rfl,Work.G07.at_zero_increment]; rfl
    have hx:= H.laws.intake; let Y:=H.laws.data; have hM:X.blank.manifest:= X.bowed (temp_nonneg _) -- edit
    have hr: Intake P T X.blank.x R := he.symm ▸ hx; let i:= S.ratio.parent k.1
    have ht := Y.safety.2.2.2 F X.blank he hK hM
    have hG:0<X.blank.t := R.p.threshold_pos.trans_eq hr.received.temp
    have ha := ht.2 hs i (X.blank_no i _) R.beta hr.positive 0 (show X.blank.watch i o.ξ R.beta X.blank.B 0 from (fun i hi=>by
       rw [WithLp.ofLp_zero,Pi.zero_apply,abs_zero]; have h:=o.rare; unfold gStep
       positivity))
    have hu: (Vine.switchΛ X z (0:Disk G c))= X.blank.liftA R.beta 0:=by
       rw [Vine.shine X.blank (show Room P S _ X.blank.x from ?_) hM R.beta 0]; unfold switchΛ worldZ; rw [show timeΛ X (0:Disk G c)=X.blank from hz]; dsimp; rw [show X.blank.atmos 0=0 from rfl, zero_smul,smul_zero]
       exact he.symm ▸ H.laws.data.room
    rw [openingΛ, show timeΛ X (0:Disk G c)=X.blank from hz, hu]; have he':= ha.2.1 k rfl; rw [hr.received.temp]; exact he'.trans (by linarith)
-- radius e core all flags independent H pack. k.Read.B.
variable {C:ℝ} (hp:∀ (z:Air f G)(_hz:∀ i,|z i| ≤ |postponement L t o|)(x:Disk G c), ‖x‖ < v→ Mode (inputΛ X z) x 1 C) (hv: 0<v)
include hp hv
lemma brightening : ∀ᶠ x:Disk G c in 𝓝 0,∀ (z:Air f G),(∀ i, |z i| ≤ |postponement L t o|) → ∀ j:Cell f,toll (inputΛ X z x) j < R.p.threshold:=by
    let D:ℝ:=royalty G*(4*(C*royalty G)); let s:=R.p.threshold; let p:= G.colorScale; have hP:0<p:= G.colorScale_pos
    have hF : Continuous (fun x:Disk G c=> D*‖x-(0:Disk G c)‖):=by fun_prop
    have hZ:D* ‖(0:Disk G c) -(0:Disk G c)‖ < p*(s/2):=by simp only [sub_self,norm_zero,mul_zero]; exact mul_pos hP (half_pos R.p.threshold_pos)
    filter_upwards [hF.continuousAt.eventually (gt_mem_nhds hZ),ball_mem_nhds (0:Disk G c) hv] with x hx hU z h j
    let f(u:Disk G c):= G.mat (faceValue (inputΛ X z u) j); have hy u (hu:u∈ball 0 v): Brush 1 (royalty G) (4*(C*royalty G)) f u:= by
       have H:= hp z h u (mem_ball_zero_iff.mp hu); let l:= square j.2.val.1 j.2.val.2; have hz : l.length=4:=rfl; convert Blaze.tour l j.1 H.pos H.atLink using 1 <;> first| (rw [hz]; norm_num)| rfl
    have hΩ : ‖f x - f 0‖ ≤ D*‖x-0‖:= (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le (fun u hu=> (hy u hu).smooth.differentiableAt (by norm_num)) (fun u hu=>by simpa only [normJ,pow_one,norm_iteratedFDeriv_one] using (hy u hu).order 1 le_rfl) (mem_ball_self hv) hU
    have hv:= outset X H he hK hs z j; change ‖f 0-1‖/p<_ at hv; change ‖f x-1‖/p<_; apply (div_lt_iff₀ hP).2; linarith only [(lt_of_le_of_lt hΩ (show D*_ < p*(s/2) from hx)), (div_lt_iff₀ hP).1 hv,norm_sub_le_norm_sub_add_norm_sub (f x) (f 0) 1]
end YM.LocalLTE.Fan.Bakers
