import YM.OPE.Compatible.Parch.Chit
/-!
# Constructing cry of field including ext.Weight Lens Lift
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}{o:Cover}
section
lemma shin {X E F: Type}[NormedAddCommGroup X][NormedAddCommGroup F][NormedAddCommGroup E][NormedSpace ℝ X][NormedSpace ℝ F][NormedSpace ℝ E] (S:X→L[ℝ] F)(w:E→X)(g:F→ℝ)(z:E)(y:X)(h:ContDiffAt ℝ ω w 0)(hp:ContDiffAt ℝ ω g 0)(he:w 0=0)(hg: HasDerivAt (fun t:ℝ=> w (t • z)) y 0) (hx:∀ t:ℝ,∀ i:F,g (t • i)=t^r*g i): Tendsto (fun t:ℝ=> (t^r)⁻¹ • g (S (w (t • z)))) Tested.germ (𝓝 (g (S y))):=by
       let f(t:ℝ):= w (t • z); let F₀:= fderiv ℝ w 0; have ht:y=F₀ z:=hg.unique (Push.side w (h.differentiableAt (by simp)) _); have H:Tendsto (fun t:ℝ=>t⁻¹ • f t) Tested.germ (𝓝 y):= ht.symm ▸ Cascade.Grid.slopeZ z (h.of_le le_top) he
       -- g continuous any x from hom
       have hC:g= Claw.rank g r:=by
              funext x; unfold Claw.rank; rw [← WardBin.leading_tensor x g (hp.of_le le_top)]; rw [show (fun t:ℝ=>g (t • x))=(fun t:ℝ=>(t^r) • g x) from funext fun i=> hx i x, WardBin.lead_monomial,if_pos rfl]
       have hg: Continuous g:= (hC.symm ▸ 
                (show Continuous (Claw.rank g r) from ((Tensor.diag_smooth _ ω).continuous)))
       apply ((hg.tendsto (S y)).comp ((S.continuous.tendsto y).comp H)).congr; intro i; unfold Function.comp; rw [map_smul, hx,inv_pow];rfl
-- simultaneous glint maps
end
namespace Prom
variable (P:Prom S o m) (b:ℕ)
variable (hp:S⊆Lattice.box b)(hb:Board n b)
noncomputable abbrev dressQ :=jetK G (crossV S) (cross_mono hp) hb
lemma bling {p:Finset (Edge Cover)}(h:p⊆bark b)(u:G.El)(x:Keys G (↥p)):jetK G p h hb (glint _ u x)=glint _ u (jetK G p h hb x):=by
       let W:=mote hb h; funext i; by_cases he:i∈ Set.range W
       · obtain ⟨t,rfl⟩:=he; change dyeL G W (glint _ u x) (W t)=G.adjoint u (dyeL G W x (W t)); rw [dye_e,dye_e]; rfl
       change dyeL G W _ i=G.adjoint u (dyeL G W x i); rw [dye_off _ _ _ _ he,dye_off _ _ _ _ he,map_zero]
local notation "W'" => Tray G S
local notation "Q"=> Bid.Dir G n
noncomputable def Oasis {X:Type}(g:Bid.Dir G n→X): W'→ X:=fun x=>g (dressQ (G:=G) b hp hb (P.brood x))
lemma schoolC {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:Q→ E)(hf:ContDiff ℝ ω f):ContDiff ℝ ω (P.Oasis b hp hb f):= hf.comp ((dressQ b hp hb).contDiff.comp (bliss P G))
lemma rankPure (p:Q→ℝ)(v:Side)(u:Site v)(hf:∀ (g:G.El)(i:Q),p (glint _ g i)=p i):
       insured (tor v) (Oasis P b hp hb p ∘ dip (fun i:↥(crossV S)=>i.val) v u) :=by
       refine ⟨fun i j s h=>?_⟩; let Z:=dressQ b hp hb (G:=G); let G₁: Cover→G.El:=fun i=>s (wrap v i+u); unfold Oasis; simp only[Function.comp_apply,hots,← show Lattice.gauge s (represent i)= _ from ((Mar_ord ..).1 h)]; rw [expandAt_gauge, glow,show Z (glint _ _ _)= _ from bling b hb (cross_mono hp) (G₁ o) _,hf] -- bling order
lemma boardS (p:Q→G.Color)(v:Side)(u:Site v)(e:RootEdge)(hP:e.1=o)(hf:∀ (g:G.El)(i:Q),p (glint _ g i)=G.adjoint g (p i)) : rooted (sett v u e) false (tor v) (Oasis P b hp hb p ∘ dip (fun i:↥(crossV S)=>i.val) v u):=by
       refine ⟨fun i j s h=>?_⟩; let Z:=dressQ b hp hb (G:=G); let G₁: Cover→G.El:=fun i=>s (wrap v i+u); unfold Oasis; simp only[Function.comp_apply,hots,← show Lattice.gauge s (represent i)= _ from ((Mar_ord ..).1 h)]; rw [expandAt_gauge, glow,show Z (glint _ _ _)= _ from bling b hb (cross_mono hp) (G₁ o) _,hf]; have hx: G₁ o=s ((tor v).start (sett v u e,false)):=by change s (wrap v o+u)=s (u+wrap _ e.1); rw[hP,add_comm]
       exact congr_arg (fun t=> G.adjoint t _) hx
lemma OasisT (f:Q→ℝ)(h:f=Claw.rank f r) (hz:Crisp (crossV S) f)(hv:∀ i:Q,∀ v:Site n→ G.Color,f (i+gillS (tor n) v)=f i)(x:Bid.Dir G n): Tendsto (fun t:ℝ=> (t^r)⁻¹ • Oasis P b hp hb f (BlurD G (crossV S) n (t • x))) Tested.germ (𝓝 (f x)):=by
       obtain ⟨v,hv'⟩:=markJ P b hp hb x; let U:=BlurD G (crossV S) n; let y:= x+gillS (tor n) v; let z:=dressQ (G:=G) b hp hb
       have hu : f (z (U y))=f x:= by rw [show f _=f y from (hz.pack _ _ hb f y).symm]; exact hv x v
       have hf: ContDiffAt ℝ ω f 0:= ((Tall.tag le_rfl h).neat.contDiffAt); let g: Bid.Dir G n→W':= P.brood ∘ U; have h: ∀ t:ℝ,∀ i: Bid.Dir G n,f (t • i)=t^r*f i:=fun t i=> (congr_fun h (t • i)).trans ((Tensor.homogeneous ..).trans (congr_arg _ (congr_fun h i).symm))
       exact hu ▸ shin z g f x (U y) (((P.bliss _).comp U.contDiff).contDiffAt) hf (by unfold g; rw [Function.comp_apply,map_zero,air]) hv' h -- dependent family
end Prom
end YM.OPE.Merchant
