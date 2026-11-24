import YM.MSbar.Fiber.Sprain
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rose
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Broom

/-! # A ticket at a flagged F-input necessarily retains at least one seed, even THIN.
   Tilting in the SD probe at the resulting radius in the normalized output.
   Never requires absolute summing a volume-scale beyond normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity.Storm
variable (M:Fibre S R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)


set_option quotPrecheck false
local notation "D" => jewelDebt (paper M) Q L x
local notation "V₀" => Real.exp (Q.mark L μ x)
local notation "s₀"=> M.lotus T x χ o.K W o.a Q.table Q.halo
variable {τ β e:ℝ}{j₀:ℕ}(h:M.turn=Wing.gasKey j₀) (hb:Bikes Q L μ x a e B j n)(hf:foam Q L)
include H h
lemma seed_required (V: Config G c) (p : Molecule S) (hp:s₀ V p≠0) : 1≤ Cash.numP p:=by
  obtain ⟨hx,hT,hR,_⟩:=whitherF M H V hp
  obtain ⟨v,hv⟩:= (R.activities.forced j₀).inventory_ne
  obtain ⟨w,hw,hx⟩:= hT.2.2 _ ((literal p j₀).2 (by rw [h] at hR; exact hR)) _ hv
  by_cases hh:p.toLeft=∅
  · unfold roster Packets.store at hw; rw [hh] at hw; simp at hw
  obtain ⟨i,hi⟩:= nonempty_iff_ne_empty.mpr hh
  have he : 1 ≤ i.shares := by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hT.1.checkpoints i hi).1
  exact he.trans (Finset.single_le_sum (f:= Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hi))
include hb hf
include N
lemma tiltPrices (V: Config G c) (hp:|τ| *D≤V₀) : Ready H.smallAt (radiusB x) (fun i=> ‖H.entriesMill (color M H χ V τ) i‖) (a+e) (pledgeQ L Q μ x B j n) e (1/2):=by
    have hx:= H.laws.data.funds.length_eq
    have hF:= H.laws.acquired; rw [hx] at hF
    have hC:R.p.B ≤ 2*radiusB x:=by rw [H.laws.intake.sizes,hx]; exact hb.covers
    let u := color M H χ V τ
    let F:= (fun i:H.ThinP=> H.ours 0 n 0 0 i.val + V₀*persona (paper M) H C H.opt 0 0 1 i.val)
    have hv:= premium_hit (paper M) H _ _ H.positive hf hC (hx.symm ▸ hb.rev _ _ hF) H.armed 0 0 1
    let z:= (swing Q L μ 1 x 0).ceiling 0 0 0 0
    have ht : V₀*(swing Q L μ R.beta x C).ceiling 0 0 1 0=z:=by
       let c:=swing Q L μ 1 x 0; change _*c.ceiling 0 0 1 _=_; unfold z
       have he : c.ceiling 0 0 1 0=c.ceiling 0 0 0 0*Real.exp (-(Q.mark L μ x)):=by unfold Mixed.Costs.ceiling Reserves.extract; simp only [Nat.cast_one,Nat.cast_zero,mul_zero,mul_one,sub_zero]; change _*Real.exp (0-_)*_=(_*Real.exp 0*_)*Real.exp (-(Q.mark L μ x)); rw [zero_sub,Real.exp_zero,show c.markSeed=Q.mark L μ x from rfl]; ring
       rw [he,mul_left_comm, ← Real.exp_add, add_neg_cancel,Real.exp_zero,mul_one]
    have hr : 0 ≤ z:= ht ▸ mul_nonneg (Real.exp_pos _).le (budget_nonneg (hv 0))
    have hJ:= raindance (paper M) H N hf hb; have hQ:= Q.overture_pos (L:=L) (μ:=μ) x n hb.paid; have hx:0 < pledgeA L Q μ x B j n:= hJ.first.1
    have hf' : Q.overture L μ x n+ z ≤ pledgeQ L Q μ x B j n:=by unfold z at *; unfold pledgeQ pledgeX; linarith only [hr,hx,hQ]
    have hl : Ac.Hit H.smallAt (radiusB x) F (a+e+e) (pledgeQ L Q μ x B j n) := by
       intro y
       have he:= budget_scale (Real.exp_pos (Q.mark L μ x)).le (budget_pull (fun i:H.ThinP=>i.val) Subtype.val_injective (hv y)); rw [ht] at he
       have hu : (a+e+e) ≤  Q.exp:=hb.win
       have hm := budget_plus (H.goods 0 n 0 0 hu y) he; refine budget_loosen (budget_mono hm ?_ ?_) hf'
       · intro i; split; exact mul_nonneg (add_nonneg (H.ours_pos ..) (mul_nonneg (Real.exp_pos _).le (earned _ _ C _ H.positive ..))) (Real.exp_pos _).le; rfl
       intro i; unfold F; split
       next h =>
         dsimp only; rw [if_pos (show y∈H.unionP i.val from h)]; rw [add_mul]; apply add_le_add_right; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hu (by positivity))) (earned _ _ _ _ H.positive ..)
       next hh => rw [if_neg (show y∉H.unionP i.val from hh)]; simp
    refine ⟨lt_of_lt_of_le (add_pos_of_pos_of_nonneg hQ hr) hf',hb.allow,hb.heat,by norm_num,fun _=> norm_nonneg _,Labels.raise_prices _ _ (fun _=> norm_nonneg _) hl (fun i=> ?_)⟩
    have hx : |H.spawn χ V i.val| ≤ H.ours 0 n 0 0 i.val:=H.renew χ V n |>.1 i
    refine le_trans (abs_add_le ..) (add_le_add hx ?_)
    let p := persona (paper M) H C H.opt 0 0 1 i.val
    by_cases hh:s₀ V i.val =0
    · rw [hh,mul_zero,abs_zero]; exact mul_nonneg (Real.exp_pos _).le (earned _ _ _ _ H.positive ..)
    have hb : |s₀ V i.val|≤ D*p:=by simpa only [pow_zero,mul_one,p] using petalsF M H V 0 0 1 (Nat.zero_le _) (seed_required M H h V i.val hh) -- χ
    rw [abs_mul]; refine le_trans (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) ?_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hp (earned _ _ C _ H.positive ..)
-- all Good V, no Thick seeds
lemma at_storm (V:Config G c) (hv : RG.flags (Pressure.temp x) V=∅) (ht:|τ| *D≤V₀): 0<S.push R.beta R.eval V + τ*S.push R.beta M.cicada V:=by
    let r:= color M H χ V τ; let m:= H.homesteadMill r; have hm := tiltPrices M H N h hb hf V ht
    let O := Classical.choice (Tree.select S.ratio S.patch.odd_side)
    let p:= overhead (prism T x χ o.K V O) R Q.table; have hp:=H.rampartMill χ V _ O (sprouting M H χ V τ) (tint M H χ V τ O) hm (add_nonneg hb.posts hb.allow.le)
    rw [← hp.tsum_eq]; change 0 < ∑' A:Finset H.ThickP,p* H.siegeMill V r A
    rw [tsum_eq_single ∅]
    · apply mul_pos
      · exact Matter.overhead_pos (prism _ _ _ _ _ _) H
      unfold Cash.siegeMill
      apply mul_pos _ (Real.exp_pos _); refine mul_pos ?_ ?_
      · simp [Cash.bankedMill,Cash.inventory,hv,Gas.value,separated]
      rw [← (H.threshold_logMill _ hm (add_nonneg hb.posts hb.allow.le)).2]; exact Real.exp_pos _
    intro i hi; unfold Cash.siegeMill Cash.bankedMill; obtain ⟨j,hx⟩:= Finset.nonempty_iff_ne_empty.mpr hi
    rw [hv,if_neg (show H.inventory i≠∅ from Finset.Nonempty.ne_empty (j.prop.2.mono (Finset.subset_biUnion_of_mem (fun i:H.ThickP=> (roster i.val).flags) hx))),zero_mul,zero_mul,mul_zero]
end Charity.Storm
end YM.PhysicalNext.Repeat.Daisy
