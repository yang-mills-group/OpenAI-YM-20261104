import YM.LocalLTE.FieldPT.Day
/-! # Uniform proposal over all unreindexed ancestry -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {χ : Chi}
open PhysicalNext.Repeat Roost
open YM.LocalLTE FrameBox Inset PriceCompiler
open LocalLTE.Fan Field Fan.Bakers Vine Weft
variable {κ :ℝ}
open Tensor
-- assembly containing Epoch tour income. Cost from stencils under Operation geometry. All at requested hist+fragrances H.E.Clock.
open Collection.Price Scarf
namespace LayersQ
variable (P:BudgetPoint) (κ:ℝ)(Φ:ℕ→ℝ→ Config G f→ℝ) (t':ℕ→ℕ) (J:ℕ) (i M l k:ℕ) (z:ℕ)
local notation "b"=> radiusB s
local notation "v!"=> stagnate l X.halo*(radiusB s)
local notation "Z"=> z*radiusB s
local notation "Q'"=> (East.canvases H P t' J l k z)
variable (hZ:East.stagnate l X.halo*Pressure.radiusB s < z*Pressure.radiusB s)
local notation "W'"=> East.eyes (East.stagnate l X.halo* Pressure.radiusB s) (z*Pressure.radiusB s) (East.broad H l) hZ Q' (East.dial H)
local notation "θ"=> Price.Tour Q' Z
local notation "age"=> East.award H t' J l k i
local notation "x!" p=> East.offK M H t' χ i l k κ (Fan.vest R Φ p)
set_option quotPrecheck false
local notation "V!" p=> Song.choir (East.way M H t' χ J l k i κ (Fan.vest R Φ p)) ∘ Song.pennant H
variable (w:ℕ)(f:H.fragrances→ℝ)
lemma identityK (p:H.fragrances)(_ht: Sum.inl p∈East.window H (East.lectures H J l t') k)(u:ℕ)(he:(Song.pennant H u).2=.inl p)(hz: age p) (j:ℝ) : (V! j) u= Rim c • ((x! j) p∘ (Song.pennant H u).1.view) := by
    change _ • (East.way _ _ _ _ _ _ _ _ _ _ ((Song.pennant H u).2) ∘ _) = _; rw [he]; unfold East.way; rw [Sum.elim_inl,if_pos hz]
lemma natively (hK:Reliable G κ C)(hu:∀ p:H.fragrances,age p→ let a:=(Beam.dashboard H p).site; Scene (cane a) κ v! w (pie i+1) (fun s=>(x! s) p) (f p) ∧ ∀ s∈Weft.clip, P.Regular (neighbors v! a) ((x! s) p))
    (h:∀ s:Site c,SumBudget (fun i=> if Orchestra H i l ∧ s∈Captain.reachability i then f i else 0) y) (hp:P.B= b) : Genome Q' W' P i w κ (fun p=> V! p) (kiosk P.supportExponent z*y):=by
    let C:=East.page H P t' J l k z
    have hC x: (East.canvases H P t' J l k z).reg x=Song.revolve C (Song.pennant H x):= East.pages H P t' J l k z x
    let B(i':Magazine H):= i'.elim (fun p=> if age p then f p else 0) (fun _=>0)
    let q:= fun x=> |Rim c| * B (pennant H x).2
    have hb(i':Magazine H):0 ≤ B i':= by
       rcases i' with p|p; swap; · exact le_rfl
       unfold B; dsimp only [Sum.elim]; split; next ht=> exact hu p ht|>.1.price
       exact le_rfl
    have he(p:H.fragrances)(h:age p):C (.inl p)= Marlin.leap Z (Beam.dashboard H p).site:= if_pos h.1
    have hx: anchored P C B (kiosk P.supportExponent z*y):= by
        intro x; rw [← add_zero (kiosk P.supportExponent z*y)]; apply Cost.sum; swap; · simp [RG.SumBudget, B, BudgetPoint.mass] -- edit
        refine budget_mono (budget_scale (show 0≤ kiosk P.supportExponent z from Real.exp_nonneg _) (h x)) (fun i=>?_) (fun i=> ?_)
        · split; exact mul_nonneg (Real.exp_nonneg _) (hb _); exact le_rfl
        split
        next hi=>
           unfold B; dsimp only [Sum.elim]; split
           next h'=>
             rw [he i h'] at hi ⊢; have hg: x∈Captain.reachability i:=hi ▸ ((show (Beam.dashboard H i).support=Captain.reachability i from Beam.see ..) ▸ (Beam.dashboard H i).anchor)
             rw [if_pos (show _∧ _ from ⟨(East.litAge H t' J l k _ i h'|>.1),hg⟩)]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by -- edit
                 apply Scarf.standing Z P z _; rw [hp])) P.exponent_pos.le)) (hu _ h'|>.1.price)
           next=> unfold BudgetPoint.mass; rw [mul_zero]; exact mul_nonneg (Real.exp_nonneg _) (h _|>.1 i)
        next=> exact mul_nonneg (Real.exp_nonneg _) (h _|>.1 i)
    let q0:= East.eyes (East.stagnate l X.halo * radiusB s) (z*Pressure.radiusB s) (East.broad H l) hZ Q' (East.dial H)
    refine ⟨q,?_,fun j=>?_⟩
    · intro i; have hv := Weft.playsB C hx i
      convert Cost.equiv (pennant H) hv using 2 with j; rw [hC]
    have hp':0 ≤ q j:= mul_nonneg (abs_nonneg _) (hb _)
    let p':= pennant H j; let S':= p'.1; let W₀:= p'.2
    by_cases hz:∃ x:H.fragrances, W₀=.inl x ∧ age x
    · obtain ⟨x,hi,ha⟩:= hz; have heq:∀ t:ℝ,(V! t) j= (Rim c) • ((East.offK M H t' χ i l k κ (Fan.vest R Φ t) x) ∘ S'.view):=fun t=> identityK H κ Φ t' J i M l k x ha.1 j hi ha _
      let A':=(Beam.dashboard H x).site; let B₀:= (Q').reg j; have hv:B₀=Song.line (Marlin.leap Z A') S' := by
         unfold B₀; rw [hC]; change Song.line (C W₀) _=_; rw [hi,he x ha]
      have hP:B₀.site=StepData.sendSites S'.1 S'.2 A' := congr_arg _ hv
      have hQ:B₀.support=neighbors Z B₀.site:= hv ▸ Scarf.normRange (s:=S') rfl Z
      let U:= East.estuary v! Z hZ (East.broad H l) S' B₀ hQ
      have hm: q0 j= Option.some U:= dif_pos hQ
      refine ⟨hp',fun h=>False.elim ((show q0 j ≠ none from by rw [hm]; simp) (Option.map_eq_none_iff.mp h)),fun z₁ ν h=>?_⟩
      change Option.map _ (q0 j)=_ at h; rw [hm] at h; obtain ⟨rfl,rfl⟩:=Sigma.mk.inj (Option.some.inj h); refine ⟨le_rfl,?_,?_⟩; swap
      · intro a hx; simp_rw [heq]; apply CouplingShape.reg_scale; change P.Regular B₀.support _; rw [hv]; apply S'.regular; exact reg_larger (hu _ ha|>.2 a hx) (Corona.halo_mono hZ.le (Finset.Subset.refl _))
      have hx: Weft.Scene (Hall.transplanted S'.1 S'.2 (cane A')) κ v! w (pie i+1) _ (f x):= (hu x ha|>.1).turning hK S'
      simp_rw [heq]; rw [show q j=|Rim c| * f x from (by unfold q; rw [show (pennant H j).2=.inl x from hi]; unfold B; dsimp only [Sum.elim]; rw [if_pos ha])]; apply Scene.scale
      -- root identity
      let V:Grove B₀.site:=by rw [hP]; exact Hall.transplanted S'.1 S'.2 (cane A')
      have hh: U.grove=V:= eq_of_heq ((East.atEstuary v! Z hZ _ _ _ _ A' hP).trans (HEq.symm (cast_heq ..)))
      have hz (o:Site c)(hp:o=StepData.sendSites S'.1 S'.2 A'): let z:Grove o:=by rw [hp]; exact Hall.transplanted S'.1 S'.2 (cane A')
                                                            Scene z κ (stagnate l X.halo*radiusB s) w (pie i+1) (fun i=>(x! i) x∘S'.view) (f x):=by subst o; exact hx
      rw [hh]; exact hz B₀.site hP
    have hF t: (V! t) j=0:= by
       let G:= East.way M H t' χ J l k i κ (Fan.vest R Φ t); have he: G W₀=0:= by
          cases h: W₀; next p=>
                          apply if_neg (show ¬age p from fun h'=> hz ⟨p,h,h'⟩)
          rfl
       change Rim c • (G W₀ ∘ S'.view)=_; rw [he]; ext; simp
    refine ⟨hp',fun _ i _=> hF i,fun d a hd=>?_⟩ -- if some: scope length =z, vacant, body regular costs.
    change Option.map _ (q0 j)=_ at hd; cases he: q0 j with
    | none=> rw [he] at hd; cases hd
    | some a=> rw [he] at hd; obtain ⟨rfl,rfl⟩:=Sigma.mk.inj (Option.some.inj hd); simp_rw [hF]; exact ⟨le_rfl,(Scene.blank _).generous _ le_rfl hp', fun _ _=> reg_const _⟩
end LayersQ
end YM.PhysicalNext.Repeat.East
