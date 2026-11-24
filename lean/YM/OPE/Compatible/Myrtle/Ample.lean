import YM.OPE.Compatible.Myrtle.Tune
/-! # talent upkeep. rotary reps and Bevel. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Raucous.Host
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix Exterior
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra GaussianScore Metric Limn Cinders
variable {G:Gauge}{c f:Side}{I:Type*}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin Votive Stationary
variable {i m j:ℕ} {s t r R e d b b' v u z x a C:ℝ}
open Zeph Dew
variable {K:Sponsor G}{T:Seasons K}
variable {N:ChartRatio G} (hN: LocalRatio N) (H:StackP N r R t)
namespace Craft
variable {L:I→ Host K T}{Y:∀ i, Studio (L i)}{l:Filter I}{V ε B A T' :I→ℝ}
variable (h:Craft Y l V A s b e u C)(hx:Bevel Y l V ε B r a)
abbrev PayΦ (Y:∀ i,Studio (L i))(ε B:I→ℝ)(s b t:ℝ)(A:I→ℝ)(i:I):=(Y i).PayT s b (A i) t (ν Y ε B i)
include h hx
set_option quotPrecheck false
local notation "O!"=> fun i=>(Y i).omS (ε i) (B i) r
local notation "μ"=> fun i=>(Y i).μφ
local notation "Q!"=> PayΦ Y ε B s b t A
local notation "W"=> RateLE l V
lemma PayZ (t:ℝ): RateLE l V (PayΦ Y ε B s b t A) 0:=by
        let p(i):=paying (Y i).Y (ν Y ε B i) s; have hz:= costsν h hx; have hk(x:ℝ): W (fun _=>x) 0:= RateLE.const x h.light; have hp: W p 0:= (h.XP.mul (hz.mul (hk (Premium.overall s)))).mono (by norm_num); have hc(k:ℕ): W (fun i=> p i^k) 0:= (hp.pow k h.light).mono (by simp); have hg(k:ℕ): W (fun i=>(ν Y ε B i)^k) 0:= (hz.pow k h.light).mono (by simp); let f i:= (Y i).heel s b (A i) t (ν Y ε B i); have hf: W f 0:= ((((hk b).mul (hc 3)|>.mono (by norm_num)).add ((h.IP.mul ((hk t).mul (hg 2))).mono (by norm_num)) h.light).add (((hk b).mul (hc 4)).mono (by norm_num)) h.light).add ((h.wage.mul (hc 2)).mono (by norm_num)) h.light
        let g i:= labor (L i).Z (L i).ForestQ (Y i).X s b (A i) t (Y i).Y (ν Y ε B i); have hp': W g 0:= ((((hk b).mul (hc 5)).mono (by norm_num)).add ((h.wage.mul (hc 3)).mono (by norm_num)) h.light).add ((h.IP.mul ((hk t).mul (hg 3))).mono (by norm_num)) h.light; exact hf.norm.add hp'.norm h.light
include hN H
lemma cashOut : Large (O!) l V (fun i p=>(Y i).Hx p) 0 ∧ Large (O!) l V (fun i p=>(Y i).Ux N p) 0:=by
       let p:= Q!; have hk:∀ᶠ i in l,∀ x∈ (Y i).omS (ε i) (B i) r, ‖(Y i).Hx x‖+‖(Y i).Ux N x‖ ≤ ‖p i‖ :=by
            filter_upwards [hx.presents,h.enters,h.covers] with i hi he ht x hx; exact (Studio.axleP hN H (Y:=Y i) (y:=x) he.1 h.served.1 h.served.2.1 h.served.2.2 he.2 hi.2.1 hi.1 hi.2.2 hx (ht ((Y i).boat x))).trans (Real.le_norm_self _)
       exact ⟨⟨p,h.PayZ hx _, hk.mono (fun i hi=>fun x hp=> (le_add_of_nonneg_right (norm_nonneg _)).trans (hi _ hp))⟩,⟨p,h.PayZ hx _,hk.mono (fun i hi=>fun x hp=> (le_add_of_nonneg_left (norm_nonneg _)).trans (hi _ hp))⟩⟩
lemma licenses (hp:G.Simple) : Playbook (O!) l V (fun i=>(Y i).glow N) ε (fun i=>(Y i).will N (ε i)) (3*a):=by
          have hT:= h.light; have hz(x:ℝ):=RateLE.const x hT; obtain ⟨hf,hZ⟩:= h.cashOut hN H hx; constructor
          · intro i; fin_cases i
            · exact Large.fromR _ (hz 1)
            · exact hf
            let p:= (hf.times hf|>.times (Large.fromR _ (hz ((2:ℝ)⁻¹)))) -- wrong exponent applied Rate.LE
            refine (hZ.added (p.grow (by norm_num)) hT).hMono ?_; filter_upwards with i x hx; change ‖(Y i).Ux N x+(Y i).Hx x^2/2‖≤‖(Y i).Ux N x+(Y i).Hx x*(Y i).Hx x*2⁻¹‖; rw [div_eq_mul_inv,sq]
          let f(i):= Q! i; have hv: W f 0:= h.PayZ hx t; have hh: W (fun i=>duesR (f i)) 0:= (((((hz _).mul hv).pow 3 hT).mono (by norm_num)).add ((((hz _).mul (hv.pow 2 hT)).mono (by norm_num)).add hv hT) hT)
          refine ⟨fun i=>duesR (f i)*ε i^3,(hh.mul (hx.pays.pow 3 hT)).mono (by norm_num),?_⟩; have hε := hx.pays.mul (h.costsν hx)|>.tends (by rw[add_zero];exact hx.beats) hT; have hk:= ((hz 2).mul hv).mul hx.pays|>.tends (by rw[add_zero,zero_add];exact hx.beats) hT
          filter_upwards [h.enters,h.covers,hx.reads,hx.presents,hε.eventually (gt_mem_nhds h.served.2.2), (hx.pays.tends hx.beats hT).eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1)),hk.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1))] with i hi he hy hP hR hx ht x hX; exact (Studio.tunesP hN H (Y:=Y i) (y:=x) hi.1 h.served.1 h.served.2.1 h.served.2.2 hi.2 hP.2.1 hP.1 hP.2.2 hX (he ((Y i).boat x)) hp hy hR hx ht).trans (Real.le_norm_self _)
end Craft
end YM.OPE.Raucous.Host
