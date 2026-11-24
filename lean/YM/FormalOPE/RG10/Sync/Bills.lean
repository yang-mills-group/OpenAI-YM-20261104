import YM.FormalOPE.RG10.Sync.Account
/-!
 # Concrete open-field rank and single-join estimate in the same basis
 Finite orbit history only. `exists_width` cost supplies are not uniform (uniform versions
 concern Kernel, including its log weight polynomial estimates; unavailable). Use requested
 physical distance Tape and moved stencils on same assembly. Not an analytic remainder
 estimate on actual step. Need support-price hypotheses on the genuine data here when using
 in polynomial-log or exponential rate claims!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp OpenSlots
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]

open PertExtension Precision Inherit Push.Loops Chart Lattice RG PowerSeries BlockGauge MultiGauge.Blocking Fabric OpenSlots.Quadratic
variable {G: Gauge} {c f : Side} {X:Type}
variable {S: StepData c f}
variable {I B:Type}[Fintype I] [Fintype B] [DecidableEq I]
variable (J:ChartRatio G) (t:S.Choices)(P:Inside S.ratio)
variable (L:Layout I (Flats G f))(Q: Layout B (Flats G c))
variable (w:PowerSeries ℝ) (U:Unmasked G f)
-- natural layout offers exact coordinates if desired (not using norm from it as including Momentum etc costs)
 def juxtapose {O:Type}[Fintype O]: Layout (O × Space E) (O→E) where
 toFun v i:= stock.ordinary (v i.1) i.2
 invFun w i:= stock.ordinary.symm fun k=> w (i,k) -- type?
 map_add' x y := funext fun i=> by rw [Pi.add_apply,map_add]; rfl
 map_smul' r x:= funext fun i=>by rw [Pi.smul_apply,map_smul]; rfl
 left_inv x:= funext fun i=> stock.ordinary.symm_apply_apply (x i)
 right_inv x:=funext fun ⟨i,j⟩=>by simp
-- use `position` of i.1 in both charts.
 def natural (n:Side)(G:Gauge) : Layout (Orb.OEdge n×Space G.Color) (Flats G n):= juxtapose

variable (R:Tape X)(x:I→X)(y:B→X) (r d n : ℕ)
section
variable {K:Type}[Fintype K]
 def costVisit (e:Episode I B K):= ∑ i∈ Iic r, ∑ a, |pins (Sum.elim x y) R (n+n) (coeff i e.vertices) a|
open Binary Beams
-- finite; avoid using C itself as uniform on family. all lemmas Proof.
omit [Fintype B] in
 private lemma peak (e:Episode I B K)(h:e.Eligible r) : ∀ᶠ C:ℝ in atTop, e.Supply R x y r d n C:= by
  obtain ⟨m,hm⟩ := exists_wide (Fin r) (d+3*r)
  let p:= Sum.elim x y; let t₁ (a:I): ℝ:= ∑ b:I, coinAt p e.joint R (n+n) a b
  let t₂ (a:I):= mag (fun i=> R.Δ (x a) (p i)) (n+n) r (e.spur a)
  let g (i:ℕ) (a:I) := pins p R (n+n) (coeff i e.vertices) a
  have hv : ∀ᶠ C:ℝ in atTop,∀ i : Fin (r+1),∀ a:I, g i.val a ≤ C := Filter.eventually_all.mpr fun i=> Filter.eventually_all.mpr (fun _=>Filter.eventually_ge_atTop _)
  filter_upwards [hv, Filter.eventually_ge_atTop ((r:ℝ)+1), Filter.eventually_ge_atTop m, Filter.eventually_all.mpr (fun i=> Filter.eventually_ge_atTop (t₁ i)), Filter.eventually_all.mpr (fun i=> Filter.eventually_ge_atTop (t₂ i))] with C v cY pY h₁ h₂;
  refine ⟨h,hm _ pY,cY,fun i hi a=> v ⟨i,by omega⟩ a,h₁,h₂⟩
end

lemma exists_width (H:S.patch.Branches S.kernel G)(hs: stock 0 U.W)(h:(core (gated P U t w)).RespectsPrice): ∃ C:ℝ,(Engine J t P L Q w U h).Supply R x y r d n C:= (peak R x y r d n _ (eligible J t P L Q w U hs H h r)).exists
-- issue vacancy Binder.Element.
 def divideUp (h:(core (gated P U t w)).RespectsPrice) (p:Ticket (Flats G f)): Ticket (Flats G c):= Broadcast P t J w U h (boost (blankRight P) p)
include L Q
lemma accumulated (hJ: LocalRatio J)(up: incline U.W)(h:(core (gated P U t w)).RespectsPrice) (p q:Ticket (Flats G f))(C:ℝ) (hc:(Engine J t P L Q w U h).Supply R x y r d n C) (hp:Guard (digital L p) r d)(hq:Guard (digital L q) r d)
 (O A D : Lens R) (L':ℝ) (ha: O.m≤ A.m)(hd:O.m≤ D.m)(hs:0≤L')(he:A.Spaced D L'):
 Route.tip L' n * mag (O.m ∘ y) n r (digital Q (divideUp J t P w U h (p*q)- divideUp J t P w U h p * divideUp J t P w U h q)) ≤
 C ^ Episode.pressure r d * mag (A.m ∘ x) (Episode.momentIn r d n) r (digital L p) * mag (D.m ∘ x) (Episode.momentIn r d n) r (digital L q):= by
 simp_rw [map_sub,map_mul,divideUp,Sync.available J t P L Q w U hJ up h,_root_.map_mul (digital L)]
 exact Episode.experience (Engine J t P L Q w U h) _ x y r d n C O A D ha hd hs he hc _ hp hq
end YM.FormalOPE.RG10.Sync
