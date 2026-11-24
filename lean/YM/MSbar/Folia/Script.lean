import YM.MSbar.Folia.Master
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {α:Type}[MeasurableSpace α]{c f:Side}{S:StepData c f}{p a :ℕ}{T W A B t s u β : ℝ}
variable {ι:Type}[Fintype ι][DecidableEq ι]
variable (v: LinkArray G ι→ α)(u: LinkArray G ι) (Ñ:ChartRatio G)(g:LocalRatio Ñ)
    (m: Prices G ι) (C: Matrix (ι × G.ColorIndex) (ι × G.ColorIndex) ℝ)
    (X:Set α)(f F:α→ℝ)
def spruce (t:ℝ)(m:Prices G ι)(w:Prices G ι):= release u (tape (m+t •w))
def portM (G:Gauge) (ι:Type)(U: LinkArray G ι) : Prop:=True
local notation "I"=> LinkArray G ι
local notation "Y"=> LogArray G ι
local notation "V"=> Prices G ι
local notation "E!"=> v ∘ spruce u t m
local notation "H"=>fieldLaw C

def ribbonD (X:Set α)(w:ℝ):Set (Prices G ι) := {x:Prices G ι| v (release u (tape (m+w•x))) ∈X ∧ tape (G:=G) (m+w•x)∈mouth Ñ}
local notation "R"=> ribbonD v u Ñ m X t

def clipT (t:ℝ) (F : α→ℝ)(z:Prices G ι) := F (v (release u (tape (m+t•z))))+ Real.log (pay Ñ (tape (m+t•z)))+ dotProduct z (C⁻¹ *ᵥ z)/2
local notation "U!"=>Portal.purse (ribbonD v u Ñ m X t) (clipT v u Ñ m C t F)
-- spec generic.Core normalization helper
noncomputable def palette (X:Set α) (v: LinkArray G ι→ α)(F f :α→ℝ)(t:LinkArray G ι) := X.indicator (fun x=> Real.exp (F x)*f x) (v t)
variable (hc:C.PosDef)
include g hc
local notation "B!"=> palette X v F f
local notation "Tλ"=> (fun y:LogArray G ι=> pay Ñ y • palette X v F f (release u y))
lemma pulled_G(w:V) : (mouth Ñ).indicator (fun y:LogArray G ι=> (pay Ñ y) • palette X v F f (release u y)) (tape (m+t • w))= modeCost C*(lawPDF C w * (U! w * f ((E!) w))):=by
   let y:= tape (G:=G) (m+t•w); let a:= v (spruce u t m w)
   change (mouth Ñ).indicator Tλ y= _; by_cases h:y∈mouth Ñ
   · rw [Set.indicator_of_mem h]; change pay Ñ y* _= _; unfold palette; by_cases he:a∈X
     · let r:= Real.log (pay Ñ y); rw [Set.indicator_of_mem (show v (release u y)∈X from he)];
       unfold Portal.purse; rw [Set.indicator_of_mem (show w∈R from ⟨he,h⟩)]; unfold lawPDF
       let D:= modeCost C; let x:= dotProduct w (C⁻¹*ᵥ w)/2
       have hp:0< pay Ñ y:= Finset.prod_pos fun i _=>mul_pos g.scale (g.pos _ (h _ (Set.mem_univ _)))
       change pay Ñ y*(Real.exp (F a)*f a)= D*(D⁻¹*_* (Real.exp (F a + Real.log (pay Ñ y) +x) * f a))
       rw [neg_div,Real.exp_neg,Real.exp_add,Real.exp_add,Real.exp_log hp]; have hc0:D≠0:= (modeCost_pos hc).ne'
       unfold x; field_simp
     rw [Set.indicator_of_notMem (show v (release u y)∉X from he)]; rw [show U! w=0 from Set.indicator_of_notMem (show w∉R from fun p=> he p.1) _, zero_mul,mul_zero,mul_zero,mul_zero]
   rw [Set.indicator_of_notMem h, show U! w= 0 from Set.indicator_of_notMem (show w∉R from fun p=>h p.2) _,zero_mul,mul_zero,mul_zero]
lemma exposed (hm: MeasurableSet X)(hv : Measurable v)(hF:RG.Envelope F)(hf:RG.Envelope f)(he: v⁻¹' X⊆ covered Ñ u)(ht:0<t):
    Integrable (fun w=> U! w*f (v (spruce u t m w))) H ∧
    (∫ s, B! s∂piHaar G ι)=t^(Fintype.card (ι × G.ColorIndex))*modeCost C *(∫ w,U! w* f ((E!) w)∂H):=by
   let F₀:=B!; have hB : RG.Envelope (B!):=by
       let p(x):= (Real.exp (F x))*f x; have hp : RG.Envelope p:= (hF.exp.mul hf); have hi : RG.Envelope (X.indicator p):= RG.Envelope.piece hm hp (RG.Envelope.const _)
       exact backdrop hi hv
   obtain ⟨hx,hH⟩:=release_integral g u (palette X v F f) hB.meas.stronglyMeasurable (fun t ht=> Set.indicator_of_notMem (show v t∉X from fun he'=>ht (he he')) _)
   let p: LogArray G ι→ℝ := (mouth Ñ).indicator Tλ; have hp: Integrable p:= hx.mp (hB.integrable _)
   let q:= p ∘ tape; have hq: Integrable q:= (tape_volume (G:=G) (ι:=ι)|>.integrable_comp_emb tape.measurableEmbedding).mpr hp
   obtain ⟨hg,h⟩:= Further.GaussianScalar.moves t ht m hq; let κ(w):= U! w* f ((E!) w)
   have ht(w:V) : q (m+t •w)=modeCost C * (lawPDF C w * κ w):=pulled_G v u Ñ g m C X f F hc w
   have hx : Integrable κ H:=by
      apply (integrable_law hc κ).2; simp_rw [ht] at hg; have hd:= modeCost_pos hc
      have hm:=hg.const_mul (modeCost C)⁻¹; simp_rw [inv_mul_cancel_left₀ hd.ne'] at hm; exact hm
   refine ⟨hx,?_⟩; rw [hH]; rw [show (∫ i,p i)=(∫ i,q i) from (tape_volume (G:=G) (ι:=ι)|>.integral_comp' p).symm,h]; simp_rw [ht]; rw [integral_const_mul, ←integral_law hc κ]; change _*(_*_)=_*_*_; ring
end YM.MSbar.Bakery.Film
