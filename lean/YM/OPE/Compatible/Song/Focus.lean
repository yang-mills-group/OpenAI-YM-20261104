import YM.OPE.Compatible.Parch.Lease
/-!
# Chamber preparation. Eventual contracts. Cube profile for Mark.S with
arbitrary exterior valuation costs
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
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}
structure Shader (r:ℕ)(B:ℕ)(n:Side) :Prop where
       wide :r<B
       board :Board n B
       money :Board n (r+1)
section
-- Elementary portfolio.Tall constructors
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma TallProd {f g:E→ℝ} (h:Tall f d)(hp:Tall g l) : Tall (f*g) (d+l):=by
       obtain ⟨P,hP⟩:= Tall.stock h; obtain ⟨Q,hQ⟩:=Tall.stock hp; rw [hP,hQ,sum_mul]; refine Tall.sums _ _ fun i (hi:i∈range (d+1))=>?_ ;rw[mul_sum]; refine Tall.sums _ _ fun j (hj:j∈ range (l+1))=>?_; have hz:Tall (Tensor.diagonal (P i)*Tensor.diagonal (Q j)) (i+j):= Tall.homish ((Tensor.diag_smooth ..).mul (Tensor.diag_smooth ..)) fun x t=> by simp only [Pi.mul_apply,Tensor.homogeneous,smul_eq_mul,pow_add];ring
       apply hz.mono; have h:= mem_range.mp hi; have hk:= mem_range.mp hj; omega
end
lemma Crisp.further {X:Type}{U V:Finset (Edge Cover)} (q:Bid.Dir G n→X) (h:Crisp U q)(hx:U⊆V): Crisp V q:=by
       refine ⟨fun i j he=>h.jury _ _ ?_⟩; funext x; let y:↥V:=⟨x.val,hx x.property⟩; have ht:= congr_fun he y; rw [echoP,echoP] at *; exact ht
section
variable {I W:Type}
-- Lower Epoch volumes; potential generalized future
abbrev Forge (G:Gauge)(n:I→Side):= (i:I)→ ScriptJ (Bid.Dir G (n i))
abbrev GlyphQ (G:Gauge)(n:I→ Side):= (i:I)→Bid.Dir G (n i)→ ℝ
variable (B:I→ Finset (Edge Cover)) {N:I→ Side}{φ:Filter I}{Z:I→ℝ}
structure Filμ (φ:Filter I) (Z:I→ℝ) (p:GlyphQ G N) (k:ℕ): Prop where
       here :∀ᶠ i in φ, Crisp (B i) (p i)
       tariff:∀ᶠ i in φ, Tall (p i) k
       loud : Bills φ Z p
variable (he:Tendsto Z φ atTop)
namespace Filμ
variable {B}{p q:GlyphQ G N}
include he
lemma empty : Filμ (G:=G) (N:=N) B φ Z 0 k:=⟨Eventually.of_forall fun _=>⟨fun _ _ _=>rfl⟩, Eventually.of_forall fun _=> Tall.bread0,Bills.zeroB he⟩
omit he
lemma care (h:Filμ B φ Z p k)(hp:k≤d): Filμ B φ Z p d:= ⟨h.here,h.tariff.mono fun _ hi=>hi.mono hp,h.loud⟩
lemma congress (h:Filμ B φ Z p k)(hV:∀ᶠ i in φ,p i=q i): Filμ B φ Z q k:=⟨(h.here.and hV).mono fun _ hi=>hi.2 ▸ hi.1,(h.tariff.and hV).mono fun _ hi=>hi.2 ▸ hi.1,h.loud.merge hV⟩
lemma wider (h:Filμ B φ Z p k) {Y:I→ Finset (Edge Cover)}(hv:∀ i,B i ⊆ Y i):Filμ Y φ Z p k:=⟨h.here.mono (fun i hi=> Crisp.further _ hi (hv i)),h.tariff,h.loud⟩
include he
lemma strike (h:Filμ B φ Z p k)(hp:Filμ B φ Z q k):Filμ B φ Z (p+q) k:=by
       refine ⟨(h.here.and hp.here).mono fun _ hi=>⟨fun x y hx=>?_ ⟩,(h.tariff.and hp.tariff).mono fun i hi=>Tall.blend hi.1 hi.2,Bills.add he h.loud hp.loud⟩; exact congr_arg₂ (·+·) (hi.1.jury x y hx) (hi.2.jury x y hx)
lemma minus (h:Filμ B φ Z p k)(hp:Filμ B φ Z q k):Filμ B φ Z (p-q) k:=by
       refine ⟨(h.here.and hp.here).mono fun _ hi=>⟨fun x y hx=>?_ ⟩,(h.tariff.and hp.tariff).mono fun i hi=>Tall.bite hi.1 hi.2,Bills.bite he h.loud hp.loud⟩; exact congr_arg₂ (·-·) (hi.1.jury x y hx) (hi.2.jury x y hx)
omit he in lemma mult (h:Filμ B φ Z p k)(hp:Filμ B φ Z q m):Filμ B φ Z (p*q) (k+m):=by
       refine ⟨(h.here.and hp.here).mono fun _ hi=>⟨fun x y hx=>?_ ⟩,(h.tariff.and hp.tariff).mono fun i hi=> TallProd hi.1 hi.2,?_⟩; · exact congr_arg₂ (·*·) (hi.1.jury x y hx) (hi.2.jury x y hx)
       obtain ⟨b,hb,h⟩:=h.loud; obtain ⟨c,hc,hp⟩:=hp.loud; exact ⟨_,(hb.mul hc).mono (by norm_num),(h.and hp).mono fun i hi x hx=> (norm_mul_le (p i x) (q i x)).trans (mul_le_mul (hi.1 x hx) (hi.2 x hx) (norm_nonneg _) ((norm_nonneg _).trans (hi.1 x hx)))⟩
lemma totals (p:W→ GlyphQ G N)(A:Finset W) (h:∀ i∈A,Filμ B φ Z (p i) k): Filμ B φ Z (∑ i∈A,p i) k:=by
       induction A using Finset.induction_on with
       | empty=> rw [sum_empty]; exact empty he
       | insert i s hi ih=> rw [sum_insert hi]; exact strike he (h _ (mem_insert_self ..)) (ih (fun i hi=>h _ (mem_insert_of_mem hi)))
end Filμ
noncomputable abbrev eyeR (p:Forge G N) (s: Phase): GlyphQ G N:=fun i x=> (p i x).seq s.val
structure PlaneQ (φ:Filter I)(Z:I→ℝ)(p:Forge G N)(k:ℕ): Prop where
       roll (s:Phase): Filμ B φ Z (eyeR p s) (k+s.val)
structure Divining (φ:Filter I)(p:Forge G N): Prop where
       he :∀ᶠ i in φ,(tor (N i)).Marbles (p i)
end
end YM.OPE.Merchant
