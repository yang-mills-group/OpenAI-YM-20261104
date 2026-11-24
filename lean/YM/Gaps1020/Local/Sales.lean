import YM.Gaps1020.Local.Leaf
import YM.Gaps1020.Local.Launch
import YM.RG12.Burst.Wardrobe
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

-- after CostAttic's timing. Follow the white headcount inflated polynomial
-- ticket of RG12.Burst. Keep a second inflation from the WarnBudget, so
-- full differentiated means of an exceptional-warning carrier can be
-- purchased alongside all Taylor grades. K & path counts remain physical.
open YM.PhysicalNext.Repeat.Daisy.Charity
open Gas Multiple Mixed -- avoid degree clash
local notation "Roots" => Trees.degreePrice

def invoice (Q:ConnectedActivityE6.Target G P)(L:Side)(μ s B ρ:ℝ)(j k K M:ℕ):= Q.goal L s + (2^j * (M+2:ℝ) * packets j K M * B)*(PhysicalNext.Repeat.Daisy.Charity.RG12.white Q L μ s ρ k)

private lemma hot {ρ:ℝ} (Ξ:Utopia H j v d r C' χ) (k:ℕ) (hs:0<ρ) (hp:Roots (radiusB s) (ρ*(Q.costs L μ 1 s 0).rootHit) Q.δ≤1/2)(z:ℝ)(hz:z≤Q.exp) : Ac.Hit H.smallAt (radiusB s) (fun p=> ρ^p.val.card * Ξ.meant p.val k) z (PhysicalNext.Repeat.Daisy.Charity.RG12.white Q L μ s ρ k):=by
  have hh:= Coupons.collect S Q.halo (radiusB s) (Q.costs L μ R.beta s C') H.birth Ξ.flair (ConnectedActivityE6.lengths T R) _ Ξ.lives Ξ.accrues hs hp (by norm_num) 0 k 0 0
  rw [Nat.cast_zero,mul_zero] at hh; change Ac.Hit H.unionP (radiusB s) (fun p=> ρ^p.card * Ξ.meant p k) Q.exp _ at hh
  intro i; have ht:= budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (hh i)
  refine budget_mono ht (fun p=>?_) (fun p=>?_)
  · split; exact mul_nonneg (mul_nonneg (pow_nonneg hs.le _) (Ξ.meant_nonneg _ _)) (Real.exp_pos _).le; rfl
  split
  next h=> dsimp only; rw [if_pos (show i∈H.unionP p.val from h)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg _))) (mul_nonneg (pow_nonneg hs.le _) (Ξ.meant_nonneg _ _))
  next h=> exact ht.1 _

lemma sold (p:Captain H j C' d v Y A b r B q k χ)(M K:ℕ)(Z:ℝ)(h : WarnBudget Z p.conduit)(hZ:1≤ Z)(hr:0<ρ)(hh:0<betaF G s L)
   (Γ: Target.Expense Q)(a:ℝ)(ha:0<a)(he:Γ.earn+a+a≤ Q.exp)(hv : Roots (radiusB s) (ρ*(Q.costs L μ 1 s 0).rootHit) Q.δ≤1/2)
   (hd: Roots (radiusB s) (invoice Q L μ s B ρ j k K M) a≤1/2):
   Trees.Ready H.smallAt (radiusB s) (fun i=>2^j*Thermal1020.total p K M ρ Z i) (Γ.earn+a) (invoice Q L μ s B ρ j k K M) a (1/2):= by
   let X:=pump h hZ
   let c₀:=(2^j * (M+2:ℝ) * packets j K M * B); have hc:0 ≤ c₀:=by unfold c₀; have hv:=p.balance; have hp:0≤packets j K M:=zero_le_one.trans (package ..); positivity
   have ht:= hot (pump h hZ) k hr hv _ he
   let o:=PhysicalNext.Repeat.Daisy.Charity.RG12.white Q L μ s ρ k
   have hK:0 ≤ o:= budget_nonneg (ht (0:Lattice.Site c)); have hQ:0<Q.goal L s:=Real.rpow_pos_of_pos hh _
   refine ⟨add_pos_of_pos_of_nonneg hQ (mul_nonneg hc hK),ha,hd,by norm_num,fun i=>?_,fun i=>?_⟩
   · unfold Thermal1020.total; apply mul_nonneg (by positivity); exact mul_nonneg (by positivity) (reserve₀ p i Z (zero_le_one.trans hZ) M ρ hr.le K)
   refine budget_loosen (C:=c₀*o) ?_ (le_add_of_nonneg_left hQ.le)
   convert! budget_scale hc (ht i) using 2 with u
   dsimp only; split
   next=> rw [pump_meant]; unfold Thermal1020.total reserve c₀; ring
   next=> rw [mul_zero]

abbrev ray : ℝ:= 7/16
-- For any M fixed Taylor order; additionally buy larger interaction order
-- internally for every prescribed remainder power downstream. Support and
-- derivative through at least actual budget are included in this gate.
def cutK (M:ℕ):ℕ:=3+4*(M+1) -- RG01 `gradeCap`
def cutLength (M:ℕ)(s:ℝ):= ((1+2*(M+1):ℕ):ℝ)*Pressure.Stores.till s

def horizonRadius (G:Gauge)(L:Side)(s:ℝ):= betaF G s L ^ ray
theorem sizeLength (G:Gauge)(L:Side)(M:ℕ): Rate G L 0 (cutLength M):= by
  have he : Rate G L 0 (fun x : ℝ=> (till x:ℝ)) := by
    apply Rate.radius_price.compare; filter_upwards with x; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; gcongr; exact Nat.div_le_self _ _
  exact he.mul_left _
section rate
variable (Q:ConnectedActivityE6.Target G P)(L:Side) (μ:ℝ) (hm:0<μ) (B r:ℝ→ℝ) (hb:Rate G L 0 B)(hr: Rate G L 0 r) (hg: ray+Q.rate<0)
local notation "sX" => horizonRadius G L
open PhysicalNext.Repeat.Daisy.Charity.RG12
include hb hm
lemma revenue (n m k : ℕ): Rate G L (ray+Q.rate) (fun x=> invoice Q L μ x (B x) (sX x) n k (cutK m) m):= by
  have hs:= (root10 Q L μ hm sX (b:=ray) Rate.power).1
  have hP Q L {g:ℝ→ℝ}(hg : Rate G L (ray+(Q:ConnectedActivityE6.Target G P).rate) g) : Rate G L (ray+Q.rate) (fun x=> Reserves.extract Q.ε k 0 0 * Reserves.treeYield (g x) (1/2) 0):= by
    unfold Reserves.treeYield; rw [pow_zero]; simp only [mul_one]; exact (hg.mul_right _).mul_left _
  have hA:= ((hb.mul_left (2^n * (m+2:ℝ)*packets n (cutK m) m)).mul (hP _ _ hs)); rw [zero_add] at hA
  exact (Rate.power.weaken (le_add_of_nonneg_left (by norm_num [ray]))).add hA
omit hm hb
include hr hg
lemma compass (M j:ℕ): ∀ᶠ s:ℝ in atTop,charge Q L s (r s) j (cutLength M s)≤ (sX s)⁻¹:=by
  let f:= fun s=>charge Q L s (r s) j (cutLength M s)
  have h: Rate G L Q.rate f:= by unfold f charge; have h:= hr.mul ((sizeLength G L M).mul_left 2); rw [zero_add] at h; simpa only [zero_mul,add_zero] using! (Rate.power.mul (((Rate.const 1).add h).pow j))
  filter_upwards [((Rate.power (a:=ray)).mul h).below hg 1 zero_lt_one,Delay.shift_pos G L] with s hs ht
  have hv:0<sX s:=Real.rpow_pos_of_pos ht _
  change f s≤_; rw [← one_div,le_div_iff₀ hv,mul_comm]; exact (le_abs_self _).trans hs
omit hr hg
lemma radiusLarge (L:Side):∀ᶠ x:ℝ in atTop, 2 ≤ horizonRadius G L x := by
  have h := (tendsto_rpow_atTop (by norm_num [ray]:0<ray)).comp (YM.Work.E09.betaF_growth G L)
  exact h.eventually_ge_atTop 2
end rate
end YM.ConnectedActivityE6.Blaze.Thermal1020
