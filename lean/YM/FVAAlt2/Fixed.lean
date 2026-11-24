import YM.FVAAlt2.Stencil
import YM.FormalOPE.RG10.InversionTop

/-! Top inversion quotient bridge (`FormalOPE.RG10` uses this integral) to
`MS.Fleet.PhysicalSum`. Real products; comparisons through all ranks and g powers.
`AtomCert`s certify these as actual O, not solving from effective-action estimates.
No other coupling conversion yet than the one IN the MS.Tide/Dial engines.
Quantitative limit machinery not used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
namespace Fixed
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Native.Studio MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom Swirl.Near MS.Fleet
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog Convolve Program
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open PertExtension.Chart PertExtension Precision Ends AtomCert
open scoped PowerSeries ContDiff
variable {G:Gauge}{n:Side}{W:Type}[LinearOrder W]
variable {P:ChartRatio G} (R:LocalRatio P)
local notation "N"=> Wilson.Config G n
local notation "F'"=> Dot G Cover
local notation "V"=>Land G n
local notation "cR"=>PowerSeries.C (R:=ℝ)
local notation "cC"=>PowerSeries.C (R:=ℂ)
local notation "C₀" => PowerSeries.coeff (R:=ℂ)
local notation "Z"=>PowerSeries ℂ
variable {ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))
set_option linter.unusedSectionVars false

include b in
lemma ray_mark {x:Site n}{w:F'}{O:N→ℝ}{d:ℕ} (h:AtomCert x w d O)(a:V): valS4 A a (h.atomSeries A)* PowerSeries.X^d= fitR (μy O) a:= by
 rw [mul_comm,← valSeriesInk A _ h.stood4, ← advance A b h, map_mul]; unfold valS4; rw [map_pow,PowerSeries.map_X]

variable (s: Finset W) {F: W→ Dot G Cover}{O: W→Wilson.Config G n→ℝ}{d:W→ℕ}{x:W→Site n}(hn: Admissible n)
variable (h:∀ i,AtomCert (x i) (F i) (d i) (O i))

include h in
lemma cert_joint: Watching (∏ i∈s,O i):= by
 have hG(v:Site n→G.El)(hv:∀ x,v (-x)=v x)(u:N): (∏ i∈s,O i) (Lattice.gauge v u)=(∏ i∈s,O i) u:= by rw [Finset.prod_apply,Finset.prod_apply]; exact Finset.prod_congr rfl fun i _=> (h i).watching.gauge v hv _
 refine ⟨hG,?_⟩; simp only [Function.comp_def,Finset.prod_apply]; exact contDiffAt_prod fun i _=> (h i).watching.tame

def total (h:∀ i,AtomCert (x i) (F i) (d i) (O i))(s:Finset W) := ray A (∏ i∈s,(h i).atomSeries A) -- variable shadow
include b in
lemma ray_shift : total A h s * (fun _ => PowerSeries.X^(∑ i∈s,d i)) = fitR (μy (∏ i∈s,O i)):= by
 funext y; change valS4 A y (_)*PowerSeries.X^_= _; rw [map_prod]
 rw [ ← Finset.prod_pow_eq_pow_sum (s:=s) (f:=d)]; rw [← Finset.prod_mul_distrib]; simp_rw [ray_mark A b]
 have hu : μy (∏ i∈s,O i)=fun y=>∏ i∈s,μy (O i) y:=by ext z; exact Finset.prod_apply ..
 rw [hu,AnalyticJets.valProd y s _ (fun i _=> (h i).stood4)]
include R hn
lemma readLand (O: Wilson.Config G n→ℝ)(h:Watching O): Lentry (fitR (μy O)) = Lam.raise (PowerSeries.mk (Orb.diagonalWith P (Orb.restrictedO O))):=by
 let μ:=chosen G n; let g(y:V):= μy O y; let S: V→ℝ:= Pert.Orb.action G n ∘ g0 G n; let K:= priceAll ∘ g0 G n
 have H: Lentry (fitR (μy O))=Lam.raise (PipeL (chosen G n) O):=by
    rw [LAND_entry]; change Lam.choir μ S K (fitR g)=Lam.raise (Local.Realm μ S K _)
    have he: ContDiffAt ℝ ∞ (μy O) 0:= ContDiffAt.comp (f:=g0 G n) 0 (by rw [map_zero]; exact h.tame) (ContinuousLinearMap.contDiff (E:=Land G n) (F:=Potential G n) (𝕜:=ℝ) (g0 G n)).contDiffAt
    rw [show fitR g=ChartC (fun x=>(g x:ℂ)) from funext (fun i=> (chart_line he i).symm)]; apply choir_face; exact ContDiffAt.comp (f:=g0 G n) 0 (by rw [map_zero]; exact priceAll_smooth.of_le le_top) (ContinuousLinearMap.contDiff (E:=Land G n) (F:=Potential G n) (𝕜:=ℝ) (g0 G n)).contDiffAt; exact VL_weight; unfold K; simp only [Function.comp_apply,map_zero,priceAll,jacobian_flat,FP_flat,one_mul]; exact one_pos; exact he
 rw [H,pipeL_color _ P R hn h,tree_color]
include b in
lemma assembled : PowerSeries.X^(∑ i∈s,d i) * Lentry (total A h s)=Lam.raise (PowerSeries.mk (Orb.diagonalWith P (Orb.restrictedO (∏ i∈s,O i)))):= by rw [← Lentry_scale (P:=total A h s) (ray_ready _ _),mul_comm (fun _=>_),ray_shift A b,readLand R]; exact hn; exact cert_joint s h -- order args

def treeMom (P:ChartRatio G)(F:N→ℝ)(d:ℕ) (j:ℕ):ℝ:= Orb.diagonalWith P (Orb.restrictedO F) (j+d)
include b in
lemma per (k:ℕ): C₀ k (Lentry (total A h s))= (treeMom P (∏ i∈s,O i) (∑ i∈s,d i) k:ℂ):= by
 let i:=∑ i∈s,d i; obtain H:=congrArg (C₀ (k+i)) (assembled R A b s hn h); rw [PowerSeries.coeff_X_pow_mul',if_pos (show i≤k+i by omega), show k+i-i=k from (by omega),cscale,PowerSeries.coeff_mk] at H; exact H

variable (c:W→ Cover)(o:Cover)
open PertExtension.Series.Tested FormalOPE.RG10.InversionTop
open scoped Classical
variable (hc:∀ i∈s,Continuous (O i))
include h
include hn
omit R in
lemma preT (hc:∀ i∈s,Continuous (O i)): Orb.PreTest (∏ i∈s,O i):= by
 have hh : Continuous (∏ i∈s,O i) := by rw [funext (fun x:N=> Finset.prod_apply (g:=O) x s)]; exact continuous_finsetProd _ hc
 let O':= ∏ i∈s,O i; have H:= cert_joint s h; exact ⟨H.gauge,⟨hh.comp Orb.continuous_links,watch_slick (hp:= even_iff_two_dvd.mpr hn.2) H⟩,hh⟩
omit R in
lemma RG10_at (hc:∀ i∈s,Continuous (O i))(m : ℕ) :
    let he:= even_iff_two_dvd.mpr hn.2; let O':= Orb.restrictedO (∏ i∈s,O i)
    C₀ (m + ∑ i∈s, d i) ((feed he).step (vertices G n) (raw O'))=(treeMom (Orb.tray G) (∏ i∈s,O i) (∑ i∈s,d i) m:ℂ):= by intro he O'; rw [tree_agreement he (preT s hn h hc).curved, into_coeff, PowerSeries.coeff_mk];rfl

-- compare leading **relative powers after stripping true Laurent prefactor** by using lower rank proof from L vs tree. all hypotheses cost. Here no IR uniform!
include A b
lemma preExpectation (hc:∀ i∈s,Continuous (O i)): Aspiration (fun r:ℝ=> r⁻¹^(∑ i∈s,d i)* Orb.preExpectation (∏ i∈s,O i) r) (treeMom P (∏ i∈s,O i) (∑ i∈s,d i)) := by
 let l:=∑ i∈s,d i; let f:=∏ i∈s,O i; have Hp:= preT s hn h hc; have he:= Orb.before_tree_formula (even_iff_two_dvd.mpr hn.2) R Hp
 have H(k:ℕ)(hk:k<l): Orb.diagonalWith P (Orb.restrictedO f) k=0:=by
    have H:= congrArg (C₀ k) (assembled R A b s hn h); rw [ cscale,PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',if_neg (show ¬ l≤k from not_le_of_gt hk) ] at H; exact Complex.ofReal_eq_zero.mp H.symm
 have hh (k:ℕ): treeMom P (∏ i∈s,O i) l k=Orb.diagonalWith P (Orb.restrictedO f) (l+k):=by rw [treeMom,add_comm]
 rw [funext hh]; exact he.shift H
lemma unique (hc:∀ i∈s,Continuous (O i))(a:ℕ→ℝ)(H': Aspiration (fun r:ℝ=> r⁻¹^(∑ i∈s,d i)* Orb.preExpectation (∏ i∈s,O i) r) a): a=treeMom P (∏ i∈s,O i) (∑ i∈s,d i):= H'.unique (preExpectation R A b s hn h hc)
omit A b h hn R
lemma levelsSymm (F:F')(h:Symm Draft.DotFlip F.val)(d i:ℕ): Symm Draft.DotFlip (Book.levels d F i).val:=by
  intro l a b r; simp_rw [Book.levels,Book.mask_s]; by_cases he:(l.length+(r.length:ℤ)+2)=(i:ℤ)+d <;> (first| solve | rw [enough _ (by simp; omega),enough _ (by simp; omega)]; exact h _ _ _ _ | rw [strange _ (by simp; omega),strange _ (by simp; omega),mul_zero])

-- Real, pre-frame
variable (t:Team) (z:ℝ)
def marks (F: W→ Dot G Cover) (d:W→ℕ)(v:W) (x:ℝ) := substitute (shift t x) (Book.levels (d v) (F v)) -- overloaded name?

include h hn R A b
lemma calibrated (he:∀ i,x i=wrap n (o+c i)): PhysicalSum G t z n true s c o (marks t F d) (substitute (shift t z) (fun k=> (↑(treeMom P (∏ i∈s,O i) (∑ i∈s, d i) k):ℂ))) := by
 let ℓ(i:W):= (h i).atomSeries A
 rw [ show (fun k=> (↑(treeMom P _ _ k):ℂ))= _ from funext (fun i=> (per R A b s hn h i).symm) ]; -- ambiguous
 apply shifted_points A b t z c o _ s ℓ (fun v=> Book.levels (d v) (F v)) (fun i=>rfl) (fun i=>?_) hn
 · intro w k; unfold marks; rw [rules,sum_stack]; apply Symm.sum; intro j _; exact (levelsSymm _ (h w).sym _ _).smul _
 · intro w k; unfold marks; refine ⟨(k:ℤ)+d w,?_⟩; rw [rules,sum_stack]; apply Limit.sum; intro i hi; exact Limit.smul _ (Limit.up ( Limit.mod _ ((i:ℤ)+d w)) (by simp at hi; omega))
 rw [← he]; exact (h i).ptS A b
end Fixed
end YM.FVAAlt2
