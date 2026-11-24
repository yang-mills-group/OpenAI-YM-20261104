import YM.MSbar.Lodge.Tooth
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
variable {σ ι M:Type}[Fintype σ][Fintype ι][MeasurableSpace M]{μ:MeasureTheory.Measure M}[MeasureTheory.IsProbabilityMeasure μ]
open MeasureTheory Set Metric
local notation "Π"=>Positions σ
local notation "Λ"=>Positions ι
variable {k p s:ℕ}{a c C w B V ε:ℝ}{n:Side}{F:Positions σ→ℝ}(P:Positions ι→L[ℝ]Positions σ)
variable {m:ℕ}{D:ℝ}
variable {f:ℝ→ℝ}(h:Hat k w V f)(hs:Vase F k B w)(W: M→ Positions σ) (hW:Measurable W)(x: Positions ι) (hv:0≤ w)(hu:1≤V)
local notation "Z"=> F ∘ Clamp f
local notation "Y"=> (fun v:M=> W v+P x)
variable (i:ι)(L:List ι)(T: Positions ι→L[ℝ]Positions σ) (hT:L.length ≤k)
include h hs hv hW hT
local notation "S"=> Clamp f ∘Y
lemma patch : let g(y:M):= roc F ((L.map (@bolt ι)).map T) (S y)
         Integrable g μ ∧ (∫ v,g v∂μ)= waltz T μ F S L :=by
     let v:= fun j i=> T (bolt i) j; let K(l:List σ)(y:M):= buoy F (S y) l* beads v l L; have hg(l:List σ)(he:l.length=L.length): Integrable (K l) μ:= (lake P h hs W hW x hv l (he.trans_le hT)).mul_const _
     have hx:=(castled K hg); intro g; have he: g=(fun x=>Yarn L.length (fun l=> K l x)):=funext (fun y=> moss T _ _ (hs.smooth _ (peak h hv _)) hT); rw [he]; refine ⟨hx.1,hx.2.trans ?_⟩; unfold waltz shaft; refine stitch _ fun l hl=> ?_; unfold K pearl; rw [integral_mul_const]
omit hT
local notation "H"=>waltz P μ F S
variable (hp:∀ A:σ, μ.real {i:M|w/2≤|W i A + (P x) A|} ≤ ε)
variable (hL:L.length+1≤k)(hd:0 ≤D)(hD:∀ i:ι,∑ v:σ, |P (bolt i) v| ≤ D) (hE:∀ i:ι,∑ v:σ, |T (bolt i) v| ≤ D)
include hL hd hD hE hu hp
lemma flowing (he:0 ≤ ε)(hC:0≤C) (hF:∀ y:Positions σ, y∈ Metric.closedBall 0 w→ ∀ v:ι,∀ t: List σ,t.length=L.length→|roc F ((P (bolt v)-T (bolt v))::(t.map Uniform.bolt)) y| ≤ C):
      |buoy (shore μ P W (F ∘ Clamp f)) x (i::L)- waltz T μ F S (i::L)| ≤ boltω L.length ε V B*D^(L.length+1)+(L.length+1:ℕ)*(D^L.length*C):=by
    apply le_trans (abs_sub_le _ (H (i::L)) _); apply add_le_add (rates P h hs W hW x hv hu L i hL hp hD hd he); obtain ⟨hf,hg⟩:=Lodge.patch (μ:=μ) P h hs W hW x hv (i::L) P hL; obtain ⟨hx,hy⟩:=Lodge.patch (μ:=μ) P h hs W hW x hv (i::L) T hL; rw [←hg,←hy, ← integral_sub hf hx]; refine (norm_integral_le_integral_norm _).trans <| le_trans (integral_mono (hf.sub hx|>.norm) (integrable_const (μ:=μ) ((L.length+1:ℕ)*(D^L.length*C))) ?_) (by simp); intro y; exact stroke P T (hs.smooth _ (peak h hv _)) hD hd hE hL hC (hF _ (peak h hv _)) _ rfl
end YM.MSbar.Lodge
