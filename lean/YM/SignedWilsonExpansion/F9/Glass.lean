import YM.Next.WARD_BIN.Vectors
import YM.WilsonCoeffUV.Root.Step.OnLattice
/-!
# One rooted stencil area in real group fields

Full matrix analytic local function (sufficient for supplying exact Ward
inputs); initial linear Taylor requirement priced on every finite log-link ray.
Finite WCU lifts and orbit versions will both read from this ONE cover column.
Local on edges ENDS not on the reporter-cells. Support demands only at fixed
inversion stages. `Lens.cover` takes edge-set testimony to any such locations.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {n:Side}{d i k j:ℕ}{G:Gauge}{F: Labels.Frame G d}

section matrix
variable {E F V:Type*}{U : CoverConfig G} [NormedAddCommGroup E] [NormedSpace ℝ E]
   [NormedAddCommGroup V] [NormedSpace ℝ V] {f g:CoverConfig G→E}

abbrev Scope := Finset (Edge Cover)
abbrev scopeShadow (G:Gauge)(S:Scope):= ↥S → G.Mat
def body (U: CoverConfig G)(S:Scope):scopeShadow G S:= fun i=>G.mat (U i)
def Capsule (S:Scope)(g:CoverConfig G → E): Prop:= ∃ f:scopeShadow G S→ E, ContDiff ℝ ω f ∧ ∀U,g U=f (body U S)
lemma Capsule.bigger {S T:Scope}(p:T⊆S)(h:Capsule T f): Capsule S f:=by
    let Q:scopeShadow G S→ scopeShadow G T:= fun A x=> A ⟨x.val,p x.property⟩; obtain ⟨f,hf,h⟩:=h; exact ⟨f∘ Q, hf.comp (contDiff_pi.mpr fun i=>contDiff_apply ..),h⟩
def Maskable (f: CoverConfig G → E) := ∃ S:Scope,Capsule S f
namespace Maskable
lemma applies (hf:Maskable f)(L:E→ V)(h:ContDiff ℝ ω L): Maskable fun U=> L (f U):=by
   obtain ⟨S,x,hx,g⟩:=hf; exact ⟨S,L∘x,h.comp hx,fun U=> congr_arg L (g U)⟩
lemma pairMap (hf:Maskable f){g:CoverConfig G→V}(h:Maskable g): Maskable fun U=>(f U,g U):=by
   obtain ⟨S,G⟩:= hf; obtain ⟨T,H⟩:=h; obtain ⟨F,hF,q⟩:=G.bigger (S:=S∪T) Finset.subset_union_left; obtain ⟨x,hx,x'⟩:= H.bigger (S:=S∪T) Finset.subset_union_right; exact ⟨_,_,hF.prodMk hx,fun i=>Prod.ext (q i) (x' i)⟩
lemma flat (c:E):Maskable (fun _:CoverConfig G=> c):= ⟨∅,fun _=>c,contDiff_const,fun _=> rfl⟩
lemma plus (hf:Maskable f)(h:Maskable g): Maskable (f+g):=(hf.pairMap h).applies _ (contDiff_fst.add contDiff_snd)
lemma diff (hf:Maskable f)(h:Maskable g): Maskable (f-g):=(hf.pairMap h).applies _ (contDiff_fst.sub contDiff_snd)
lemma bind {K:Type*}[NormedRing K][NormedAlgebra ℝ K]{a b:CoverConfig G→K}(p:Maskable a)(q:Maskable b): Maskable (a*b):=(p.pairMap q).applies _ (contDiff_fst.mul contDiff_snd)
lemma μ (hf:Maskable f)(c:ℝ): Maskable (c• f):= hf.applies _ (contDiff_id.const_smul c)
lemma stock {X: F→CoverConfig G→ E}{S:Finset F}(p:∀ i∈ S,Maskable (X i)): Maskable (∑ i∈S,X i):=by
    induction S using Finset.induction_on with
    | empty=> rw [Finset.sum_empty]; exact flat _
    | @insert i S h ih=> rw [Finset.sum_insert h]; exact (p i (Finset.mem_insert_self ..)).plus (ih (fun i hi=>p i (Finset.mem_insert_of_mem hi)))
lemma piM [Fintype F]{V:F→Type*}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)](X:(i:F)→CoverConfig G→V i)(h:∀ i,Maskable (X i)): Maskable fun U a=> X a U:=by
    choose S x hx H using h; let T:= Finset.univ.biUnion S; choose G hG hK using fun i=> Capsule.bigger (S:=T) (Finset.subset_biUnion_of_mem S (Finset.mem_univ i)) (show Capsule (S i) (X i) from ⟨x i,hx i,H i⟩)
    exact ⟨T,fun u i=> G i u,contDiff_pi.mpr hG,fun U=> funext (fun i=>hK i U)⟩
lemma longer (p:Maskable f){F':CoverConfig G→CoverConfig G}(h:∀ i,Maskable fun U=>G.mat (F' U i)): Maskable (f∘F'):=by
    obtain ⟨S,L,hL,H⟩:= p; have hf:f∘F'= fun U=> L fun i=> G.mat (F' U i.val):=funext fun i=>H (F' i); rw [hf]; exact (piM (F:=↥S) (V:=fun _ : S=>G.Mat) _ (fun i=>h i.val)).applies L hL
lemma matP (G:Gauge)(i:Edge Cover): Maskable (fun U:CoverConfig G=> G.mat (U i)):=by
    let u:({i}:Scope):= ⟨i,Finset.mem_singleton_self _⟩; exact ⟨{i},fun x=> x u,contDiff_apply ..,fun _=>rfl⟩
lemma mat_flip {f:CoverConfig G→ G.El}(hf:Maskable fun U=> G.mat (f U)): Maskable fun U=> G.mat (f U)⁻¹:=hf.applies _ (starL' ℝ (A:=G.Mat)).contDiff
lemma stepM (x:Cover)(i:Lattice.Step): Maskable (fun U:CoverConfig G=>G.mat (i.read U x)):=by unfold Lattice.Step.read; split; exact mat_flip (matP ..); exact matP ..
lemma passageM (G:Gauge)(x:Cover)(w:Walk): Maskable (fun U:CoverConfig G=>G.mat (travel U x w)):=by
   induction w generalizing x with
   | nil=> exact flat _
   | cons a w ih=> simp only [travel,G.mat_mul]; exact (stepM x a).bind (ih _)
lemma revolveS (c:Maskable f)(s:Signed): Maskable (f∘ Lattice.pull s 0):= c.longer fun i=> stepM (affine s 0 i.1) _
lemma walkS (c:Maskable f)(x:Cover): Maskable (f ∘ Lattice.translate x):=c.longer fun i=>matP G _
lemma cur (f:CoverConfig G→G.El)(h:Maskable (G.mat∘ f)): Maskable (G.curvature ∘ f):=by
    exact ((h.diff (mat_flip h)).μ (1/2:ℝ)).applies _ G.projectColor.toContinuousLinearMap.contDiff
lemma colorAct {f:CoverConfig G→ G.Color}(h:Maskable f){g:CoverConfig G → G.El}(p:Maskable (G.mat ∘ g)): Maskable fun U=> G.adjoint (g U) (f U):=
 (((p.bind (h.applies _ G.colorMat.toContinuousLinearMap.contDiff)).bind (mat_flip p))).applies _ G.projectColor.toContinuousLinearMap.contDiff
lemma displaced (e:Edge Cover)(x:G.Color)(hf:Maskable f): Maskable (slope e x f):=by
    obtain ⟨S,L,hL,H⟩:= hf; let Q (v:scopeShadow G S) (t:ℝ): scopeShadow G S:= fun i=>if i.val=e then G.mat (G.lieExp (t•x))*v i else v i
    have hq: ContDiff ℝ ω (uncurry Q):=by
        apply contDiff_pi.mpr; intro i; unfold uncurry Q; have hm: ContDiff ℝ ω (fun y: scopeShadow G S × ℝ=> y.1 i):= (contDiff_apply ..).comp contDiff_fst; split; exact (G.exp_jet.comp (contDiff_snd.smul contDiff_const)).mul hm; exact hm
    let V(v:scopeShadow G S)(t:ℝ):=L (Q v t); let W(v:scopeShadow G S):= fderiv ℝ (V v) 0 1
    have hv:ContDiff ℝ ω (uncurry V):= hL.comp hq
    have ht (t:ℝ)(U:CoverConfig G): body (slide e U (t• x)) S= Q (body U S) t:=by
        funext i; unfold body slide Q; split
        next h=> rw [h,update_self,G.mat_mul]; simp only [h]
        next h=> rw [update_of_ne h]
    refine ⟨S,W, (show ContDiff ℝ ω _ from (ContDiff.fderiv hv (g:=fun _=>0) contDiff_const (by simp)).clm_apply contDiff_const),fun U=>?_⟩; unfold WardBin.slope; simp_rw [H,ht]; rfl
protected lemma cont (h:Maskable f):Continuous f:=by obtain ⟨S,X,h,p⟩:= h; rw [funext p]; exact h.continuous.comp (continuous_pi fun _=>(G.continuous_mat).comp (continuous_apply ..))
def ends (S:Scope): Finset Cover:= S.image Prod.fst ∪ S.image (fun e=>e.1+ Lattice.step e.2)
lemma sees {S:Scope}(p:Capsule S f): LocalOn (ends S) f:=by obtain ⟨x,h,t⟩:=p; intro A B v; rw [t A,t B]; apply congr_arg x; funext i; exact congr_arg G.mat (v i.val (Finset.mem_union_left _ (Finset.mem_image_of_mem _ i.property)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ i.property)))
lemma cover (p:Maskable f): ∃ S:Finset Cover,LocalOn S f:=by obtain ⟨s,h⟩:=p; exact ⟨ends s,sees h⟩
end Maskable
end matrix

abbrev Fabrication (G:Gauge):= Edge Cover→G.Color
def roof (v: Fabrication G) (t:ℝ): CoverConfig G:= fun a=> G.lieExp (t•v a)
-- transfer the actual Affordable estimate to arbitrary log-link rays, no pure gauge requirement
open scoped ContDiff
section
open Set
variable {S:Finset Cover} {E V:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f:CoverConfig G→ E}
lemma thinRaySink (v:Fabrication G)(q:Site n): ∃ c:ℝ,0<c∧∀ᶠ t in 𝓝[>] (0:ℝ), flags (c*t) (above q (roof v t))=∅:=by
    let F(t:ℝ):= above q (roof v t)
    have hv (e:Edge (Site n)) : ∃ c:ℝ,0≤c∧∀ᶠ t in 𝓝[>] (0:ℝ), G.chord (F t e) ≤ c*t:=by
       let r:=v (Lattice.lift (e.1-q),e.2); let U (t:ℝ):=G.mat (G.lieExp (t • r)); let X:=G.colorMat r
       have hx : HasDerivAt U X 0:=by simpa [U,X,WardBin.left] using! matLeft_zero r (1:G.El)
       have he := ((WardBin.value_scale (hx.sub_const 1) (show U 0-1=0 from by simp [U])).norm.eventually (ge_mem_nhds (show ‖X‖< ‖X‖+1 by linarith)))
       have hp:0<G.colorScale:= G.colorScale_pos; refine ⟨(‖X‖+1)/G.colorScale,by positivity,?_⟩
       filter_upwards [he,self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with t ht h; have he':0<t:=h; rw [div_mul_eq_mul_div]
       change ‖U t-1‖/G.colorScale ≤ _; change ‖t⁻¹ • (U t-1)‖≤‖X‖+1 at ht; rw [norm_smul, Real.norm_of_nonneg (by positivity),inv_mul_eq_div] at ht; exact div_le_div_of_nonneg_right ((div_le_iff₀ he').mp ht) hp.le
    choose c hC h using hv; let z:=1+∑ i,c i; have hz:0<z:=by unfold z; exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _=>hC _)
    refine ⟨4*z,by positivity,?_⟩; filter_upwards [eventually_all.mpr h,self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with t ht he; apply RG.voids ?_ le_rfl; intro i _; refine (ht i).trans ?_; rw [show 4*z*t/4=z*t by ring]; exact mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun i _=>hC i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) (show 0<t from he).le

def rayCap (k:ℕ)(f:CoverConfig G→ E): Prop:=∀ v:Fabrication G, ∃ C:ℝ,0≤ C∧∀ᶠ t in 𝓝[>] (0:ℝ), ‖f (roof v t)‖≤ C*t^k
lemma byStamp {k:ℕ}(p:Affordable S (k:ℤ) f): rayCap k f:=by
    intro v; obtain ⟨n,h⟩:= someFits S; let q:= (0:Site n); obtain ⟨c,hc,H⟩:= thinRaySink v q; obtain ⟨b,hb,hr⟩:= p.paid 0 2
    refine ⟨b*c^k,by positivity,?_⟩; have hx : Tendsto (fun t : ℝ => c*t) (𝓝[>] (0:ℝ)) (𝓝 (c*0)) := (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [H,hx.eventually (ge_mem_nhds (show c*0<1 by simp)), self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ))] with t hv hu t0; have ht:0<t:= t0
    let u:= Affordable.test (c*t) (by positivity) hu; let U:=above q (roof v t); have hl: Healthy u.threshold (footprint S q) U:= by
        unfold Healthy; rw [show flags u.threshold U=∅ from hv]; exact disjoint_bot_right
    have hp := (hr _ h u rfl q).bound [] le_rfl (by simp) U hl; change ‖places q f U‖≤ b *(c*t)^(k:ℤ)*(1:ℝ)^0 at hp; unfold U at hp; rw [fromAbove p.uses h,zpow_natCast,mul_pow,←mul_assoc,pow_zero,mul_one] at hp; exact hp
lemma rayCap_spin (p:rayCap k f)(s:Signed)(o:Cover): rayCap k (f ∘ Lattice.pull s o):=by
    intro v; let w (u:Axis):=(posDir u).rotate s; let V (u:Edge Cover):= let p:= affine s o u.1; if (w u.2).neg then -(v ((w u.2).used p)) else v ((w u.2).used p)
    have h(t:ℝ): Lattice.pull s o (roof v t)=roof V t:=by
       funext i; unfold Lattice.pull Lattice.Step.read; change (if (w i.2).neg then _ else _)=_; by_cases hp:(w i.2).neg=true; · simp only [hp,↓reduceIte,V,roof,smul_neg]; exact (Work.F03.exp_neg_color _).symm
       simp only [V,roof,hp,↓reduceIte,Bool.false_eq_true]; rfl
    obtain ⟨C,hC,he⟩:= p V; exact ⟨C,hC,he.mono fun i hi=>by rw [Function.comp_apply,h i]; exact hi ⟩
lemma rayZero (h:Maskable f): rayCap 0 f:=by
    intro v; let X(t:ℝ):=f (roof v t); let C:= ‖X 0‖+1
    have hx:Continuous X:= h.cont.comp (continuous_pi fun _=>(show Continuous (fun t:ℝ=> G.lieExp (t • v _)) from G.lieExp_cont.comp (continuous_id.smul continuous_const)))
    refine ⟨C,by unfold C; positivity,?_⟩; filter_upwards [((hx.norm.continuousAt.mono_left nhdsWithin_le_nhds).eventually (ge_mem_nhds (show ‖X 0‖< C by unfold C; linarith)))] with t ht; rw [pow_zero,mul_one]; exact ht
lemma ray_leading {q:ℕ}(V:ℝ→ E)(u:ContDiffAt ℝ (↑q) V 0)(p:q<k)(C:ℝ)(h:∀ᶠ t in 𝓝[>] (0:ℝ), ‖V t‖≤ C*t^k): WardBin.leading q V=0:=by
     apply WardBin.leading_of_lim u
     rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) (g:=fun t=>C*t^(k-q)) ?_ ?_; swap
     · simpa only [zero_pow (Nat.sub_ne_zero_of_lt p),mul_zero] using ((show Continuous (fun t:ℝ=>C*t^(k-q)) from by fun_prop).tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi _))
     filter_upwards [h,self_mem_nhdsWithin (s:= Set.Ioi (0:ℝ))] with t ht he; have hv:0<t:=he; change ‖(t^q)⁻¹ • V t‖≤ _; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_left ht (show 0≤(t^q)⁻¹ by positivity)); rw [show t^k=t^(k-q)*t^q by rw [← pow_add,Nat.sub_add_cancel p.le]]; exact le_of_eq (by field_simp)
end
structure Pill (G:Gauge) where
    f : CoverConfig G→ℝ
    valid : Maskable f
    inv : GaugeInvariant f
    rank : ℕ
    bound : rayCap rank f
namespace Pill
variable (p:Pill G)
def spins (s:Signed): Pill G:=⟨p.f ∘ pull s 0,p.valid.revolveS s,fun x U=>by rw [Function.comp_apply, Function.comp_apply, Work.G06.pull_gauge_zero]; exact p.inv _ _,p.rank,rayCap_spin p.bound s 0⟩
end Pill
end YM.WilsonCoeffUV.Mer.Xa
