import YM.OPE.Compatible.Streams.Flow
/-! # sunlight bond -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}{R:Patch}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier Hark
variable {u d s r l k m:ℕ}{W I E:Type}{τ:Phase→ℕ}
lemma enoughAway (R:Patch)(c:Side): Tendsto (fun i:ℕ=>(CountL c R.L i).val) atTop atTop:= by
    apply StrictMono.tendsto_atTop; apply strictMono_nat_of_lt_succ; intro i; change _< (CountL c R.L i).val * R.L.val; exact lt_mul_of_one_lt_right (CountL c R.L i).pos (Jac.mount R)
lemma polyZ (p':ℕ→E)[NormedAddCommGroup E]{t a:ℝ}(hp:0 < t)(ht:∃ c:ℝ,∀ᶠ i in atTop,‖p' i‖≤ c*t^i) (ha:t<a): Thick a p':=by
     obtain ⟨c,hc⟩:=ht; obtain ⟨N,H⟩:=eventually_atTop.mp hc; let v(i:ℕ):=‖p' i‖/t^i; let b':=∑ i∈Finset.range N,v i; refine Thick.hex ⟨max b' c,fun i=>?_⟩ hp.le ha; by_cases h:N ≤ i; · exact (H _ h).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
     exact (div_le_iff₀ (pow_pos hp i)).mp ((single_le_sum (f:=v) (fun i _=> (by unfold v; positivity)) (mem_range.mpr (by omega : i<N))).trans (le_max_left b' c))
variable {K:Sponsor G}{S:Seasons K}{t:ℝ}(A: Alps K S s t)(hr:LocalRatio P)(hp:4 ≤ s)(hs:G.Simple)(hv:0 ≤ t){n:Side}(x y:Site n)(H:Even n.val)
local notation "M!"=> CountL n R.L
local notation "Y!"=> solar G d τ
abbrev WQ (p q:solar G d τ) (j:ℕ):Token:=PriceZ.Warp A (evenBoot K R H j) hp hs (spikeS K R x j) (spikeS K R y j) p q P -- fix argument.name
section money
variable [Fintype I]
variable (e:RootEdge)(f:Libra.Keys G I→G.Color)(D:I→RootEdge)(a:Bool)(p:solar G d τ)
local notation "T!"=>WTax (d+2) d
abbrev StencilTax (d k:ℕ):=WTax (d+2) d+k
-- uniform eventual invoice exact only order chosen but terminal.
include hr hv
lemma GrowthP (hF:r≤d)(hΘ:∀ i,StencilTax d k ≤ τ i)(hA:ContDiffAt ℝ ω f 0)
     (he:∀ i,Variance.Cand r (f∘dip D (M! i) (spikeS K R x i)))
     (he':Holds p (fun n x=> Cake (sett n x e) a (Dune A) (Rh A) (f∘ dip D n x) r))
     (hx:Pins K R x y) (ψ:Phase)(q:solar G d τ) : ∃ b:ℝ,∀ᶠ i in atTop, ‖((WQ (P:=P) (R:=R) A hp hs x y H p q i).seq ψ.val)‖ ≤ b*((βX R k)^i):=by
       let N(i):= M! i; have ht:= enoughAway R n; obtain ⟨s,hs'⟩:=eventually_atTop.mp he'; obtain ⟨v,hv',H'⟩:=hx
       let M:= max s.val (max 8 (Scent D e)); let U:Type:= { i:ℕ // M≤ (N i).val}; let t:U → Side:=fun i=> N i.val; have hy(i:U):Scent D e ≤ (t i).val:= by have h:=i.property; unfold M at h; exact (le_max_right ..|>.trans (le_max_right ..)).trans h
       have hC(i:U):8 ≤ (t i).val:=by have h:=i.property; unfold M at h; exact (le_max_left ..|>.trans (le_max_right ..)).trans h
       have hV(i:U):s≤ t i:=(le_max_left s.val _).trans i.property
       let X:=spikeS K R x; let Y:=spikeS K R y; have hp:= Gift A hp hs hr hv t (fun i=>evenBoot K R H i.val) (fun i=> X i.val) (fun i=> Y i.val) D f (fun _=>a) e (fun _=>p) (fun _=>q) hF hΘ v (le_trans (by norm_num) hv') hA hC hy (fun i=>he _) (fun i=>congr_fun (hs' (t i) (hV i)) _) (fun i=> H' _) ψ
       obtain ⟨b,hb,B⟩:= hp; refine ⟨b*((n.val:ℝ)⁻¹)^k*‖q‖,?_⟩; filter_upwards [ht.eventually (eventually_ge_atTop M)] with i hi; let v:ℝ:= (N i).val; have hc:0 < v:= Nat.cast_pos.mpr ((N i).pos); apply (B ⟨i,hi⟩).trans_eq; change b*v^(T!)* (v⁻¹^(T!+k)*‖q‖)=_; rw [pow_add _ (T!) k,show v⁻¹^k= _ from (show v⁻¹^k= _ from hostV ..)]; change b*_*((v⁻¹^_*(((n.val:ℝ)⁻¹)^k*(βX R k)^i))*‖q‖)= _; rw[inv_pow v (T!)]; field_simp
end money
end YM.OPE.Variance
