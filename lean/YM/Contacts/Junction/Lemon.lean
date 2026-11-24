import YM.Contacts.Junction.Golden
/-! # Physical Receipt. This sampling is virgin products with Model Emitted substituted AT ALL
 flag-healthy field patches. Reorganization required after publication in Pace.
 Crown. Cost.Weight.
 -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a:ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
namespace StagePort
variable (p:StagePort G U P X k L σ C M n)
local notation "D" => p.dew
abbrev wook (j:ℕ):= book k p.budget p.importB (D).T.high (D).T.up (f:=(D).f) j
def poll (u:Config G (D).f): ℝ:= -(D).β * ∑ i∈ Finset.range (k+1), (D).grad^i * Trio.froth (p.wook i) u -- notation D macro
-- pragmatically `max/min`. no lower support cut hidden.
def quake (u:Config G p.dew.f): ℝ:= min (Real.exp 1) (max (Real.exp (-1)) (Real.exp (p.poll u)))
def flareV : Config G (D).f→ℝ:= fun u => (Pane.virgin p.dew.T p.budget p.dew.β).eval u * Real.exp (p.poll u)
def notion (x:(D).X)(u:(D).B.Slice G):= overall (D).B (D).T p.budget (D).β (ship x) u
abbrev traceK (x:p.dew.X) (u:p.dew.B.Slice G): ℝ:= p.notion x u * p.quake (p.dew.B.drape u)
abbrev push (x:p.dew.X):= p.dew.S.push p.dew.β p.flareV (ship x)
-- External shape letters read later.
lemma qual (p:StagePort G U P X k L σ C M n)(u:Config G p.dew.f): p.quake u∈ Set.Icc (Real.exp (-1)) (Real.exp 1):= ⟨le_min (by apply Real.exp_monotone; norm_num) (le_max_left ..), min_le_left ..⟩
variable {p} (hp:Up p d a j)
include hp
lemma gates : Envelope p.quake ∧ GaugeInvariant p.quake:= by
    have he:= hp.lit; constructor; · have h (i:ℕ)(hi:i≤k): Measurable (Trio.froth (p.wook i)):= Buyer.eval_meas he hi; exact ⟨Measurable.min measurable_const (Measurable.max measurable_const ((Measurable.const_mul (Finset.measurable_fun_sum _ fun i hi=> ((h i (by simp only [Finset.mem_range] at hi; omega)).const_mul _)) _).exp)), _, fun u=> (Real.norm_of_nonneg ((Real.exp_pos _).le.trans (qual _ u).1)).trans_le (qual _ u).2⟩ -- meas order
    intro s y; unfold quake; have hh: poll p (gauge s y)=poll p y:= by unfold poll; apply congr_arg; apply sum_congr rfl; intro i hi; apply congr_arg; unfold Trio.froth; apply sum_congr rfl; intro z _; exact (he i (by rw [Finset.mem_range] at hi; omega)).sector _ z|>.symmetry s y
    rw [hh]
lemma billsV (x:p.dew.X): Envelope (p.notion x) ∧Envelope (p.traceK x) := by
   have he : Envelope (p.notion x):= (Fare.amt (D).B (D).T p.budget _ _ U (hp.truePE.intake) (ship x)).1; have hg:= (gates hp).1; exact ⟨he,he.mul ⟨hg.meas.comp (D).B.continuous_drape.measurable,hg.cost.choose,fun v=> hg.cost.choose_spec _⟩⟩ -- notation?
lemma fiscal (hQ : ∀ x:Config G p.dew.f, flags p.budget.threshold x=∅ → |p.poll x|≤1) (y:p.dew.X):
     p.push y=∫ u, p.traceK y u ∂p.dew.B.order G:= by
   let D':=p.dew; let M:= Pane.virgin D'.T p.budget D'.β; have he : p.flareV=M.eval * p.quake:= by
       ext1 x; by_cases hv: flags p.budget.threshold x=∅; · unfold flareV quake; rw [Pi.mul_apply,max_eq_right (Real.exp_monotone (abs_le.mp (hQ _ hv)|>.1)),min_eq_right (Real.exp_monotone (abs_le.mp (hQ _ hv)|>.2))];
       change M.eval x *_= M.eval x *_; unfold M; rw [Pane.sparkling,if_neg hv]; ring
   have hs:= hp.truePE; have h:= hs.intake.cap; have hv : GaugeInvariant p.flareV:= by rw [he]; intro i x; simp only [Pi.mul_apply, (gates hp).2 i x, (show M.eval (gauge i x)= _ from Presented.lawful_gi h i x)]; rfl
   have hb:= hs.stitches.large; have hI:=D'.S.isKernel hb.1 D'.β; have hZ : Envelope p.flareV:= by rw [he]; exact (M.envelope h).mul (gates hp).1 -- casts
   let U:=ship y; change _= ∫ u, _ ∂D'.B.order G; unfold StagePort.push; change D'.S.push D'.β _ U=_; rw [D'.B.pushing hI p.flareV U hv (hZ.integrable _) (fun k U'=>D'.S.covary hb.1 k D'.β U' U)]; apply integral_congr_ae; filter_upwards with a; unfold traceK notion; rw [he,Fare.total]; change D'.S.density D'.β (D'.B.drape a) U * (M.eval (D'.B.drape a) * _) = _; exact (mul_assoc _ _ _).symm -- param shape
omit hp
lemma awake (x:p.dew.X)(u:p.dew.B.Slice G):0≤p.notion x u := Fare.rays _ _ _ _ _ x
lemma actual_both (x:p.dew.X)(u:p.dew.B.Slice G): 0≤p.traceK x u ∧ Real.exp (-1)*p.notion x u ≤ p.traceK x u ∧ p.traceK x u ≤ Real.exp 1*p.notion x u:= by
   let D':=p.dew; let s:= p.quake (D'.B.drape u); have hs:= qual p (D'.B.drape u); have hv:=awake (p:=p) x u; rw [traceK,mul_comm]; exact ⟨mul_nonneg ((Real.exp_pos _).le.trans hs.1) hv,mul_le_mul_of_nonneg_right hs.1 hv,mul_le_mul_of_nonneg_right hs.2 hv⟩
end StagePort
namespace Travel
variable (p:Travel N Q Φ)(hk:2≤k)(hp:G.Simple)(hP:LocalRatio P)(hn:k≤n)
local notation "Fν" => (γC (ι))
local notation "θ" => (fun i=> Dew.β (ι i))
include p hk
lemma quake_model : ∀ᶠ i in atTop,∀ u: Config G (Φ i).dew.f, flags (Φ i).budget.threshold u=∅ → |(Φ i).poll u|≤1 := by
    obtain ⟨d,a,j,_,ha,H⟩:= p.ship; have ht:=p.parameter; have hf:= volume_count p.dawn p.scale p.plaza p.ferry;
    let c(i:ℕ)(n:ℕ):= N.pow (vow*hero n+a i) i; let b(i:ℕ):ℝ:= Fintype.card (Site (Φ i).dew.f); have hb:N.Rush 0 b:= Rush.bb p.scale (p.dawn.mono fun i hi=> ⟨Nat.cast_nonneg _, hi.stitches.finalP⟩)
    let t(u:ℕ)(i:ℕ):= (θ i)* Fν i^u * (b i*c i u); have he (j:ℕ): N.Rush (-1) (t j):= by
       have ht' : N.Rush (vow*hero j) (fun i=>c i j):= (Meter.Rush.any (p:=vow*hero j)|>.times ha (add_zero _)).take (N.eventual.mono fun i hi=>Real.rpow_add hi _ _)
       have hx:= (hf.2.1.times (ht.forward.powers j) rfl).times (hb.times ht' (zero_add _)) rfl;
       have hh (J:ℕ)(hj:3≤ J) : (1:ℝ) + - (1/2:ℝ)*↑J + vow * hero J ≤ - (1:ℝ):= by have hp : (3:ℝ)≤(J:ℝ):= Nat.cast_le.mpr hj; have hz:2≤(hero J:ℝ):= Nat.cast_le.mpr (owned J); unfold vow; linarith
       apply hx.mono; by_cases hj:3≤j; · exact hh j hj
       interval_cases j <;> norm_num [hero,vow]
    let u:ℝ:=k+1; have hU:u>0:= by unfold u; positivity
    filter_upwards [((eventually_all_finset (Finset.range (k+1))).mpr fun i _=> Meter.sliding (he i) (by norm_num) _ (inv_pos.mpr hU)), H,ht.pos,hf.1,p.plaza,N.eventual] with i hi hx hQ hh hz hv x hy
    let y:=Φ i; let φ:= y.dew; change |(-φ.β) * _| ≤ _; erw [abs_mul,abs_neg, abs_of_pos (show 0<φ.β from hh.1)]; let t' j:= (φ.grad)^j * Trio.froth (y.wook j) x;
    have hw j (hj:j≤k): φ.β*|t' j| ≤ u⁻¹ := by
       have hp:= (hx.2.lit j hj); let V:= Trio.froth (y.wook j); have h (g:Site φ.f): ‖y.wook j g x‖ ≤ c i j:= by rw [show c i j= _ from (show c i j=(betaF G y.pearlRide L) ^ (vow*hero j+a i) from congr_arg (fun x:ℝ=>x^(vow*hero j+a i)) hz)]; exact (hp.funds _ hx.2.vast g).2 x (by rw [RG.Healthy,hy]; exact Finset.disjoint_empty_right _) [] (by simp) (by simp)
       have ht : ‖V x‖ ≤ b i * c i j:= (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> h i)).trans_eq (by simp only [sum_const,nsmul_eq_mul,card_univ]; rfl)); rw [show t' j = φ.grad ^ j * (V x) from rfl, abs_mul,abs_of_nonneg (pow_nonneg (show 0≤φ.grad from hQ.le) _)]; change _≤ _; rw [← mul_assoc]; exact (mul_le_mul_of_nonneg_left ht (mul_nonneg (show 0≤φ.β from hh.1.le) (pow_nonneg (show 0≤φ.grad from hQ.le) _))).trans ((le_abs_self (t j i)).trans (hi j (mem_range.mpr (by omega))).le)
    change φ.β * |(∑ i∈Finset.range (k+1), t' i)|≤1; apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (show 0≤φ.β from hh.1.le)).trans; rw [Finset.mul_sum]; exact (Finset.sum_le_sum (fun x hx=>hw x (Nat.le_of_lt_succ (mem_range.mp hx)))).trans_eq (by rw [Finset.sum_const,nsmul_eq_mul,card_range]; push_cast; exact mul_inv_cancel₀ hU.ne')
end Travel
end Provision
end YM.Contacts.Junction
