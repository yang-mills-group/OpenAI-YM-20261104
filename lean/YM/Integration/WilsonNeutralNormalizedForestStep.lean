import YM.Integration.WilsonRunFormalMarkedStep
import YM.FormalBulk08.Turner.Brief

/-! The forward normalized column on one original nonbare block. Every
conditional uses its own measured forest, the complete independently carried
upper vacuum, and the translated test on that fine preimage. The period
limit below is an auxiliary coefficient identification at fixed UV cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralNormalizedForestStep
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free Work.F03 Work.F05 Work.F08
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open WilsonRunFormalMarkedStep
open scoped Topology BigOperators Matrix Classical

section Forest
variable {G:Gauge} {K:KernelChoices} {j d:ℕ} (P:Flight j d) (h:P.patch.Branches K G) (n:Side)
variable (F:Forest (primary P.patch K n).ratio) (t:(primary P.patch K n).Choices)

-- The positive saddle is the original finite-forest compression.
include h t in
private theorem positive : (testPrecision G (primary P.patch K n) F P.wing).PosDef:=by
  classical
  let S:=primary P.patch K n
  obtain ⟨σ,_,paid⟩:=center_price G K _ P.patch.order_cut
  obtain ⟨_,_,cell⟩:=paid P.patch rfl h
  obtain ⟨W,H,_⟩:=cell P.wing
  let a:=clothe G S
  have old : meat (G:=G) S t P.wing*repackM a.symm a.symm (W.acts n)=1:=by
    apply Lodge.prunes (B:=W.acts n) a
    apply (H n t).trans
    ext i j
    by_cases v:i=j <;> simp [Matrix.one_apply,v]
  exact Flat.definite S h t P.wing F old P.legal

private def saddle {V:Type} [Fintype V] [DecidableEq V] (T:Matrix V V ℝ) (pd:T.PosDef):Saddle ℝ V :=
  ⟨T⁻¹,T,fun i j=>(Matrix.isHermitian_iff_isSymm.mp pd.inv.isHermitian).apply j i,
    fun i j=>(Matrix.isHermitian_iff_isSymm.mp pd.isHermitian).apply j i,
    Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr pd.det_pos.ne')⟩

def chamber : Hull (Pine G (primary P.patch K n) F) (wire G n):=
  ⟨saddle _ (positive P h n F t),crunch (kernelP G K.penalty P.land n),draught (pMean G K P n F)⟩

private theorem conditional (L:Lodge P.patch) (r:(primary P.patch K n).Choices) (O:ChartRatio G)
    (localO:LocalRatio O) (room:4≤d) (U T:Pap (wire G (n*P.L)))
    (head:coeff 0 U=crunch (kernelP G K.penalty P.wing _))
    (quiet:Rite U U 1 0) (insert:Rite T T 1 0) :
    Orb.flag (chamber P h n F t) (Reef.flush F t O U) (Reef.seat F T) =
      Reef.tossed P O h L n r U T := by
  rw [Turner.tossed_choice O P h L r t U T]
  let E:=Reef.floor K P L n
  exact Turner.summer_fren (Work.F05.freeEquiv F E) t O h localO _ (Reef.ferry P h L n) U quiet T insert
    (Reef.baked G K P n F room h O localO t _ rfl _ head)
    (Reef.consolidate P O h L n localO t U head room)
end Forest

variable {G:Gauge} (R:Run G) {d D:ℕ}
local notation "V" => R.family.path.levels
private abbrev branches (i:ℕ) := (R.family.path.levels.blocks i 0).branches

def integral (run:Run G) (wood:∀ k,Lodge (run.family.path.levels.clock.op k 0).patch)
    (color:hue G) (Dfit:d<D) (top k:ℕ) (n:Side)
    (F:Forest (primary (destination run.family.path.levels top k).patch run.family.path.levels.clock.kernel n).ratio)
    (t:(primary (destination run.family.path.levels top k).patch run.family.path.levels.clock.kernel n).Choices)
    (b:Letter (run.family.labels.level d)) (f:Studio D) : Pap (wire G n) := by
  let A:=destination run.family.path.levels top k
  let y:=WilsonRunFormalMarkedStep.graph run wood color Dfit top (k+1)
  let w:=Dove.model run.family.path.levels wood (branches run) run.metals.O color top (k+1)
  let α:=Reef.flush F t run.metals.O (Mesa.stone w (n*A.L))
  let H:=chamber A (branches run k) n F t
  exact PowerSeries.C (MvPolynomial.C (Kemp.aven A.L d)) *
    ∑ x : Site A.L, Orb.flag H α
      (Reef.seat F (Kemp.resite (wrap _ (lift x)) (Kemp.banner (slots (run.family.labels.level d) b)
        (y b (Dawn.throughW x D (Elm.growL run.family.path.levels k) f)) (n*A.L))))

theorem received (run:Run G) (wood:∀ j,Lodge (run.family.path.levels.clock.op j 0).patch)
    (col:hue G) (Dfit:d<D) (top k:ℕ) (hs:G.Simple) (o:Loc G 1) (hk:k<top)
    (hd:d≤run.family.path.levels.clock.J (k+1)) (n:Side)
    (F:Forest (primary (destination run.family.path.levels top k).patch run.family.path.levels.clock.kernel n).ratio)
    (t tag:(primary (destination run.family.path.levels top k).patch run.family.path.levels.clock.kernel n).Choices)
    (b:Letter (run.family.labels.level d)) (f:Studio D) :
    let A:=destination run.family.path.levels top k
    let w:=Dove.model run.family.path.levels wood (branches run) run.metals.O col top (k+1)
    let y:=WilsonRunFormalMarkedStep.graph run wood col Dfit top (k+1)
    integral run wood col Dfit top k n F t b f =
      WilsonFormalMarkedCubature.finiteTransfer A (wood k) w run.metals.O (branches run k)
        (Elm.growL run.family.path.levels k) (y b) d (slots (run.family.labels.level d) b) f n tag := by
  intro A w y
  have column:=WilsonRunFormalMarkedStep.normalized run wood col Dfit hs o top (k+1) hk
    (hd.trans (run.family.path.levels.fits.mono (Nat.le_succ _)))
  have action:=Dove.genu run.family.path.levels wood (branches run) run.metals.O col run.alloy.B.ratio hs
    (i:=k+1) (N:=top) hk
  obtain ⟨c,C,hc,hC,stock,-⟩:=colors G run.family.path.levels.clock.kernel.penalty
    run.family.path.levels.clock.kernel.penalty_pos A.legal
  have head:=stoned_main hc.le hC.le (stock A.wing).1 action.toVivid action.ink (n*A.L)
  unfold integral WilsonFormalMarkedCubature.finiteTransfer
  apply congrArg (_ * ·)
  refine Finset.sum_congr rfl fun x _=>?_
  apply conditional _ _ _ _ _ _ _ _ run.alloy.B.ratio (run.family.path.levels.clock.adm k) _ _ head (action.civic _ 1 0)
  let Z:=Kemp.banner (slots (run.family.labels.level d) b)
    (y b (Dawn.throughW x D (Elm.growL run.family.path.levels k) f)) (n*A.L)
  have source:Rite Z Z 1 0:=(Kemp.solo_iff ..).mp (column.officers b).ward _ _
  simpa only [Signed.act_one, Z, y, A] using! (Kemp.repulp (x:=wrap _ (lift x)) 1 Z Z source)

theorem original (run:Run G) (wood:∀ j,Lodge (run.family.path.levels.clock.op j 0).patch)
    (col:hue G) (Dfit:d<D) (top k:ℕ) (hs:G.Simple) (o:Loc G 1) (hk:k<top)
    (hd:d≤run.family.path.levels.clock.J (k+1)) (per:ℕ)
    (F:∀n:Side,Forest (primary (destination run.family.path.levels top k).patch run.family.path.levels.clock.kernel n).ratio)
    (t:∀n:Side,(primary (destination run.family.path.levels top k).patch run.family.path.levels.clock.kernel n).Choices)
    (b:Letter (run.family.labels.level d)) (f:Studio D) (e r:ℕ) (v:chain (wire G (run.family.S.side k per)) r) :
    let n:=run.family.S.side k per
    let A:=destination run.family.path.levels top k
    let w:=Dove.model run.family.path.levels wood (branches run) run.metals.O col top (k+1)
    let clock:=Roof.epoch col A (wood k) run.family.path.levels.clock.kernel w run.metals.O (branches run k)
    Tendsto (fun m:Side=>∑j∈Finset.range (e+1),Wine.bill (bookH clock) (bookU clock) e j r*
      Shore.cores (Shore.tray m n) (rancho (integral run wood col Dfit top k (m*n) (F _) (t _) b f) j r) v)
      atTop (𝓝 (rancho (Kemp.banner d ((Roof.larch (WilsonRunFormalMarkedStep.graph run wood col Dfit top k)
        (WilsonRunFormalMarkedStep.matrix run wood col Dfit top k)) b f) n) e r v)) := by
  intro n A w clock
  have step (m:Side) := received run wood col Dfit top k hs o hk hd (m*n) (F _) (t _) (t _) b f
  simp_rw [step]
  exact WilsonRunFormalMarkedStep.measured run wood col Dfit hs o top k per hk hd t b f e r v

end YM.Integration.WilsonNeutralNormalizedForestStep
end
