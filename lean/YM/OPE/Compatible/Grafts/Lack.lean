import YM.OPE.Compatible.Straws.Oui
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
def tor (n:Side): Score (Body 1 n) (Site n):=⟨Prod.fst,fun i=>i.1+step (axisEquiv.symm i.2)⟩
abbrev driftB (n:Side): Edge (Site n)≃ Body 1 n := Equiv.prodCongr (Equiv.refl _) axisEquiv -- Axis.
def vital : Score (forest S.ratio he).Free (Site c):=⟨fun i=> S.ratio.parent i.val.1,fun i=> S.ratio.parent (i.val.1+step i.val.2)⟩
lemma putReal (x:Bid.Dir G n): represent x=(put (I:=Body 1 n) x) ∘ driftB n:= by funext i; change _*1= _; rw [mul_one]; rfl
lemma vacTor (u:Libra.Tile G (Body 1 n))(k:Libra.Tile G (Site n)): ((tor n).dress k u) ∘ driftB n= Lattice.gauge k (u ∘ driftB n):=by funext i; unfold tor Score.dress; change k _ * _ * (k (i.1 + step (axisEquiv.symm (axisEquiv i.2))))⁻¹= Lattice.gauge k _ _; rw [Equiv.symm_apply_apply];rfl
lemma Mar_ord (x y:Bid.Dir G n)(u:Site n→G.El):(tor n).dress u (put x)=put y ↔ Lattice.gauge u (represent x)=represent y:=by
    rw [putReal,putReal,← vacTor]; constructor; · rintro H; rw [H]
    intro h; funext i; obtain ⟨x,rfl⟩:= (driftB n).surjective i; exact congr_fun h x
lemma cstV (q:Site n→G.El)(h:(tor n).dress q 1=1)(i j:Site n):q i=q j:=by
         refine YM.Pert.Orb.site_induct (fun j=> q i=q j) ?_ i rfl j; intro w k hk; have hp: q w * 1 * (q (w+step k))⁻¹=1:=congr_fun ( (vacTor (1:_) q).symm.trans (show (tor n).dress q 1 ∘ driftB n=1 from by rw [h];rfl) ) (w,k)
         rw [mul_one] at hp; exact hk.trans (mul_inv_eq_one.mp hp)
lemma frameReal (x:K! × Z!): represent (ribz S he x)= fieldF X! x.2:=by rw [spoolP]; rfl
lemma compassV (x y:K! × Z!)(q:Site c→G.El)(hp: (vital S he).dress q (put x.2)=put y.2): (tor f).dress (q ∘ S.ratio.parent) (put (ribz S he x))=put (ribz S he y):=by
      rw [Mar_ord,frameReal,frameReal]; ext1 i; by_cases h:i∈ (forest S.ratio he).trunks
      · let p: { i// i∈ (forest S.ratio he).trunks}:= ⟨i,h⟩
        have hl(x:Z!): fieldF (forest S.ratio he) x i=1:=(forest S.ratio he).on_tree (expF (forest S.ratio he) x) p
        change q _*fieldF _ _ i*(q _)⁻¹=_;rw [hl x.2,hl y.2,mul_one, (forest S.ratio he).trunk_internal h,mul_inv_cancel]
      let p:(forest S.ratio he).Free:=⟨i,h⟩; have ht(z:Z!): fieldF (forest S.ratio he) z i= put z p := (forest S.ratio he).off_tree _ p
      change q _*fieldF _ _ i*(q _)⁻¹= _; rw [ht x.2,ht y.2]; exact congr_fun hp p
lemma liftedTr (a b:ℝ→ K! × Z!)(p:ℝ→ Site c→G.El)(h: Fiber.Scheme (tor c) (vital S he) a b p): (tor f).Track (ribz S he ∘ a) (ribz S he ∘ b) (fun j=> p j ∘ S.ratio.parent):=by
      refine ⟨(ribz S he (G:=G)).contDiff.contDiffAt.comp _ (h.jobs.hX.prodMk h.forks.hX), (ribz S he (G:=G)).contDiff.contDiffAt.comp _ (h.jobs.hY.prodMk h.forks.hY),?_,?_, h.forks.law.mono (fun i hi=>compassV S he _ _ _ hi),fun i=> h.jobs.chart _⟩
      · rw [Function.comp_apply, show a 0=0 from Prod.ext h.jobs.gx h.forks.gx,map_zero]
      rw [Function.comp_apply, show b 0=0 from Prod.ext h.jobs.gy h.forks.gy,map_zero]
lemma irruption (p:ScriptJ U!)(h:(tor f).Marbles p): Fiber.Creative (p ∘ ribz S he) (tor c) (vital S he):=by
     refine ⟨fun i=> (h.toll i).compLinear (ribz S he).toLinearMap,fun {a b s} ht=>?_⟩; apply (h.honors (liftedTr S he a b s ht)).congr' _ EventuallyEq.rfl; filter_upwards with t; change (p (_ • _)).atK _-(p (_ • _)).atK _=(p (ribz S he (_ • _))).atK _ - (p (ribz S he (_ • _))).atK _;rw [map_smul,map_smul];rfl
-- lift supports H
end YM.OPE.Cascade.Rill
