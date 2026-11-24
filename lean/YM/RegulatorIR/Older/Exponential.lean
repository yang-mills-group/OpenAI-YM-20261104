import YM.RegulatorIR.Older.Trunk

/-!
# Polynomial cost consumption of sequences

Order N, κ windows etc variable. Never compare two continuum choices with independent
subsequences without a separate bridge. Supply mode coefficient-wise, marked Horizon-zero.
Lengths in real units. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Older
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Capture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I U: Type}{q u b p a i j e k d m r s:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{C D J K:Choice M}

-- ordinary limits chosen when exist.
def ceilingAt (f:ℕ→ℝ):ℝ:= limUnder atTop f
lemma adjacent {f:ℕ→ℝ}{u r:ℝ}(h : r<1)(hp : ∀ i:ℕ, ‖f (i+1)-f i‖ ≤ u*r^i) : Tendsto f atTop (𝓝 (ceilingAt f)) ∧ ∀ i, ‖ceilingAt f-f i‖ ≤ u*r^i/(1-r):=by
 have hs i : dist (f i) (f (i+1))≤ u*r^i:=by rw [dist_comm,dist_eq_norm]; exact hp i
 have ht:Tendsto f atTop (𝓝 (ceilingAt f)) := (cauchySeq_of_le_geometric r u h hs).tendsto_limUnder
 exact ⟨ht,fun i=> by rw [← dist_eq_norm,dist_comm]; exact dist_le_of_le_geometric_of_tendsto r u h hs ht i⟩

structure CaseW (I:Type) where
 key : I
 stepS: ℕ
 foil: ℕ

def topple (w:CaseW I): CaseW I:= ⟨w.key,w.stepS,w.foil+1⟩ -- adjacent older case
/-- extent = (I,spacings age, entry k, stencil/coupling scheme data etc) relative to t. foil n means old age, *not* period. Need derivative & analytic caps recorded independently. -/
structure Dials (I:Type)(W:Type) where
 reach : CaseW I→ W
 bill : I→ℝ
 prime : ∀ i, 1 ≤ bill i
 H:ℝ
 V:ℝ
 HP:1<H -- λ_j grows
 warm : 0<V
 V₀: V<1 -- ε_N≤ V^N
namespace Dials
variable (R:Dials I W)
include R
-- upper cap convenience using real meter

def counter (i:CaseW I):ℝ:= R.bill i.key*(1+i.stepS+i.foil)
lemma counterOne (i): 1 ≤ R.counter i:=by have h:= R.prime i.key; unfold counter; nlinarith [show (i.stepS:ℝ)≥0 from by positivity,show (i.foil:ℝ)≥0 from by positivity]
lemma bill_pos (i):0<R.bill i:= lt_of_lt_of_le zero_lt_one (R.prime i)
def counterF (i:CaseW I):ℝ:= R.bill i.key*(1+i.foil)
lemma tallP (i):1≤R.counterF i:=by have h:=R.prime i.key;unfold counterF;nlinarith [show (i.foil:ℝ)≥0 from by positivity]
lemma supports (i): R.counterF i ≤ R.counter i:=by
 have hz:= R.bill_pos i.key; unfold counterF counter;gcongr; exact le_add_of_nonneg_right (by positivity)
lemma sheets (i: I)(j:ℕ): R.counterF ⟨i,j,j+1⟩≤ R.counter ⟨i,j,j+1⟩:= supports R _
lemma parallel (i:I)(j p:ℕ): R.counter ⟨i,j,j+1⟩^p ≤ R.bill i ^p*(2:ℝ)^p*(j+1:ℝ)^p:=by
 unfold counter;dsimp only; rw [← mul_pow,← mul_pow];push_cast;apply le_of_eq;congr 1;ring
end Dials
lemma cost_V {r s:ℝ}(hR:0<r)(h:r<s)(k:ℕ) :∃ c:ℝ,0≤c∧∀ n:ℕ, (n+1:ℝ)^k*r^n≤c*s^n:=by
 let y:=r/s;have hS:=hR.trans h;have hp:0<y:=div_pos hR hS;have hq:y<1:= (div_lt_one hS).mpr h
 let f (n:ℕ):= (n+1:ℝ)^k *y^n
 have he:Tendsto f atTop (𝓝 0):=by
    have hv := ((tendsto_pow_const_mul_const_pow_of_lt_one k hp.le hq).comp (tendsto_add_atTop_nat 1)).div_const y
    rw [zero_div] at hv
    convert hv using 1
    ext n; change _= ((↑(n+_) :ℝ)^k * y^(n+_))/y; simp only [f,pow_succ,Nat.cast_add, Nat.cast_one]; field_simp
 obtain ⟨N,hN⟩:= eventually_atTop.mp (he.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)))
 let c:= (1:ℝ)+∑ i∈Finset.range N, f i; have hv n:0 ≤ f n:= by unfold f; positivity
 have hC:1≤c:=le_add_of_nonneg_right (sum_nonneg fun i _=> hv i); refine ⟨c,zero_le_one.trans hC,fun n=>?_⟩
 rw [← div_le_iff₀ (pow_pos hS n), mul_div_assoc,← div_pow];change f n≤c; cases le_or_gt N n with
 | inl hx=> exact (show f n<1 from hN n hx).le.trans hC
 | inr hx=> exact (Finset.single_le_sum (f:=f) (fun i _=> hv i) (Finset.mem_range.mpr hx)).trans (le_add_of_nonneg_left zero_le_one)

section Cloud
variable {L:Meter W}{S:Heir n G}{R:Reel S}

-- λ_j can vary with N. pin lower exponent. UV estimate across overlap uses $kmu$ computed or assumed from RG08. Inverse mesh decay enough for Norms, strengthened schedules in Section k. Needs actual scale plan to supply.
structure Region (B:Dials I W)(J: Choice M)(S:Heir n G)(L:Meter W): Prop where
 limitF (x:CaseW I): S.ε (B.reach x) ≤ B.V ^ x.stepS
 elderF (x:CaseW I): B.H^x.foil ≤ S.l (J.choose (B.reach x))
 poker :∃ c:ℝ,∃ u:ℕ,0≤c∧∀ x:CaseW I,(L.val (B.reach x)).toReal ≤ c*B.counter x^u

variable {Q:Dials I W}
structure Reeds (Z: W→ℝ)(B:Dials I W) (S: Heir n G)(ξ:ℝ): Prop where
 -- bound in counter (allow losses in k+log L+log P); no dependence N'
 positive : 0< ξ
 estimate: ∃ c:ℝ, ∃ d:ℕ,0 ≤ c∧∀ i:I, ∀ k j v:ℕ,k ≤ j → let w:CaseW I:= ⟨i,k,v⟩;let w':CaseW I:=⟨i,j,v⟩;‖Z (B.reach w)-Z (B.reach w')‖ ≤ c*(B.counterF w)^d * S.ε (B.reach w) ^ ξ
-- projected RG08 formal UV theorem
variable (B: Dials I W)
variable {F: W→ ℝ}{ξ:ℝ} (hB: Region B J S L)

-- scoping sensed

def sheetCost (Z:W→ℝ)(B:Dials I W)(i:I)(j:ℕ)(a:ℕ):ℝ := Z (B.reach ⟨i,a,j⟩)
def UV_point (B:Dials I W)(Z:W→ℝ)(i:I)(v:ℕ):= ceilingAt (sheetCost Z B i v)
variable (V : Reeds F B S ξ)
include hB V
omit hB in
lemma VP : 0< B.V^ξ ∧ B.V^ξ <1:= ⟨Real.rpow_pos_of_pos B.warm _, Real.rpow_lt_one B.warm.le B.V₀ V.positive⟩
lemma heatRay (x:CaseW I):S.ε (B.reach x)^ξ ≤ (B.V^ξ)^x.stepS:=by rw [Real.rpow_pow_comm B.warm.le]; exact Real.rpow_le_rpow (S.hl _).le (hB.limitF x) V.positive.le
lemma UV_leg (i:I)(j:ℕ): Tendsto (sheetCost F B i j) atTop (𝓝 (UV_point B F i j)):=by
 obtain ⟨K,d,hk,H⟩:=V.estimate
 let f:= sheetCost F B i j
 let C:= K*B.counterF ⟨i,0,j⟩^d;let s:= B.V^ξ; have hx : CauchySeq f:=by
    apply cauchySeq_of_le_geometric s C (VP B V).2; intro n; rw [dist_eq_norm];exact (H i n (n+1) j (by omega)).trans (mul_le_mul_of_nonneg_left (heatRay B hB V _) (mul_nonneg hk (pow_nonneg (B.tallP _|> zero_le_one.trans) _)))
 exact hx.tendsto_limUnder
lemma speed_UV : ∃ c:ℝ,∃ d:ℕ,0≤c∧∀ w:CaseW I,‖F (B.reach w)-UV_point B F w.key w.foil‖≤ c*(B.counterF w)^d*S.ε (B.reach w)^ξ:=by
 obtain ⟨K,d,hk,H⟩:=V.estimate; refine ⟨K,d,hk,fun w=>?_⟩
 exact le_of_tendsto (tendsto_const_nhds.sub (UV_leg B hB V w.key w.foil)|>.norm) ((eventually_ge_atTop w.stepS).mono (fun u he=> H w.key w.stepS u w.foil he))
end Cloud
end YM.RegulatorIR.Older
