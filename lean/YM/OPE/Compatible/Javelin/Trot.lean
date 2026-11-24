import YM.OPE.Compatible.Javelin.Struck
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {W:Type}{v b:W→ℝ}
-- regular voyages, auxiliary mobility.Link.
variable {x:ℝ}{X: Seasons K}
-- launch.Seam billing in Φ before reflections and Energy embedding.
variable {u v w:W→ℝ}{U:(i:W)→Boxes G P K.K}{A:∀ x:W,Alps K X i (u x)}{D:∀ x:W,Alps K X j (v x)}{n':W→Side}
namespace Rise
variable (Y:Rise A D U R w)
local notation "L!"=>solar G d τ
variable (h:∀ i,Even (n' i).val)(hx:∀ i,barrier P≤ (n' i).val)(hi:4 ≤ i)(hj:4 ≤ j)(hS:G.Simple)(hρ:0 ≤ u)(hz:0 ≤ v)
variable (hr:LocalRatio R) (Kq:Aware d τ)
local notation "Lσ" i=> χ' (K:=K) (n' i) P
-- seam.CP.Op norm earliest mobility comes from physical clock later. use all N in launch.Alignment.F
include hx
abbrev stamp' (e:ℕ)(G:Gauge)(k:ℕ):= Scape.Setup G e + k
lemma beacon (hv:Y.Hiked (stamp' d G k) R)(hp:∃ z:ℝ,∀ i,‖Y.chant hS hr Kq i‖≤z)(a b:(i:W)→ Site (n' i))(z:ℝ)(hH:2 ≤ z)(hs:∀ i,Settle (a i) (b i) z)(hh:∀ i,stamp' d G k+44 ≤ τ i)(p:Phase):
    let f:= Plume (τ:=τ) (d:=d) (fun i=>even_both (Lσ i) (h i)) A (fun i=>(Lσ i).embed (a i)) (fun i=>(Lσ i).embed (b i)) hS hi hr hρ p
    let g:= Plume (τ:=τ) (d:=d) h D a b hS hj hr hz p
    Cash n' 0 (Scape.gDump n' k) fun i=> ‖f i- pullD (Y.spireX hS hr Kq i) (g i)‖:=by
        intro f g; let Z:= W × L! × L!; let B:= Scape.gDump n' k; let d':=stamp' d G k; let q: Z→ L!:=fun p=> p.2.1; let r: Z→L!:=fun p=> p.2.2; let X':=fun u:Z=>u.1; let θ':Rise (u:=u∘X') (v:=v∘X') (fun j=>A j.1) (fun j=>D j.1) (fun j=>U j.1) R (w∘X'):=⟨fun i=>Y.fee _⟩; have hp': θ'.Hiked d' R:=by obtain ⟨⟨a,b,c,h₁,h₂,h₃,h₄⟩,⟨x,hx⟩,H⟩:=hv; exact ⟨⟨a,b,c,h₁,h₂,h₃,fun i=>h₄ i.1⟩, ⟨x,fun i=>hx _⟩,H.up X'⟩
        obtain ⟨u₁,Hu⟩:=hp; have hh':= θ'.rubbing (fun i=>h i.1) (fun i=>hx i.1) hi hj hS hr Kq hp' ⟨u₁,fun i=> Hu i.1⟩ q r (fun i=> a i.1) (fun i=> b i.1) z hH (fun i=> hs i.1) hh (fun i=> bramble _) (fun i=> bramble _) p
        obtain ⟨c,hc,F⟩:=hushP hh'; refine ⟨c,hc,fun i=>?_⟩; let P:=f i-pullD (Y.spireX hS hr Kq i) (g i); change ‖‖P‖‖ ≤ c* _^0*(B i); rw [Real.norm_of_nonneg (norm_nonneg P),pow_zero,mul_one]; apply segmentD P _ (mul_nonneg hc (Scape.gDuty _ _ i)); intro x y; let Q:=Y.spireX hS hr Kq i; change ‖f i x y-(g i (Q x) (Q y))‖≤ _; rw [show f i x y=_ from lanceZ .., show g i (Q x) (Q y)=_ from lanceZ ..,← Scape.cupDiff]; apply (F (i,x,y)).trans_eq; simp only [pow_zero,mul_one]; change c * (‖x‖*‖y‖*B i) = _; ring
end Rise
end YM.OPE.Quit.PriceZ
