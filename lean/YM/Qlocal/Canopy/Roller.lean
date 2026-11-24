import YM.Qlocal.Canopy.Button -- enough without Deline
/-! # Power-shift merge for the actual normalized exponent tags.
 No combining coupler marker exponent costs manually. Uses sqrt-scale Taylor
 sign. Keep full FSM mask/width elsewhere (*dormant* analytic, not a cut or
 moved countable family here). -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
variable (F:Forest S.ratio)
namespace Flute
variable {K R : reed G n} (h:Flute R q)(h':Flute K r) (y:ℝ)
include h h'
lemma pair : Flute (R*K) (q+r):= ⟨fun u p x=>by dsimp only [Pi.mul_apply]; rw [h.byfield _ _ _,h'.byfield _ _ _], fun u=> Envelope.mul (h.envelope _) (h'.envelope _), h.zeroAt.mul h'.zeroAt⟩
omit h h'
lemma one : Flute (1:reed G n) 0:= ⟨fun u p x=>rfl,fun t=> Envelope.const _, GradeAt.unchecked (contDiffAt_const (c:= (1:ℝ)))⟩
variable {ι:Type*} (W:ι→ reed G n) (k:ι→ℕ)
def bill (U:Finset ι): reed G n:= ∏ i∈U, W i
abbrev size (p:Finset ι):=∑ i∈p,k i
lemma roof (p:Finset ι)(hx:∀ i∈p,Flute (W i) (k i)) : Flute (bill W p) (size k p):= by
   induction p using Finset.induction_on with
   | empty=> simp [bill,size, one]
   | insert i p hi ih=> have hp:=hx i (mem_insert_self ..); rw [size,sum_insert hi,bill,Finset.prod_insert hi]; exact Flute.pair hp (ih fun j hj=> hx j (mem_insert_of_mem hj))
end Flute
namespace Roller
open StampCo
variable {X Y : Word ℝ}
lemma diary : dialect (plus X Y)=dialect X*dialect Y:= by ext i; unfold dialect; rw [PowerSeries.coeff_mk]; rfl
lemma holy (h₁: roll (fold X q) q=X) (h₂: roll (fold Y r) r=Y): fold (plus X Y) (q+r)=plus (fold X q) (fold Y r):= by
  suffices h : plus X Y= roll (plus (fold X q) (fold Y r)) (q+r) by rw [h]; exact back
  apply reversible; rw [rolling,diary,diary,pow_add, ← mul_mul_mul_comm (dialect _) (PowerSeries.X ^ q) (dialect (fold Y r)), ← rolling, ← rolling, h₁, h₂] -- check
-- mark exponent product, t^pole turns measure before mask estimates.
variable (F:Forest S.ratio){ι:Type*} (W:ι→ reed G f) (k:ι→ℕ){O:ChartRatio G}{B0:ℝ→ Config G f→ℝ}{t:S.Choices} (D:Desk F O B0 t)
    (u: Apex c G × Poll.Body (Precision.Key F G)) {P:Finset ι}
abbrev poem (f:reed G f)(v:ℕ) := fold (someJ (Schema.coda F f D u)) v
local notation "Ω"=> poem F D u
variable (hx:∀ i∈P,Flute (W i) (k i))
lemma lull : Ω (1:reed G f) 0 = just 1:= funext fun i=> (Act.static (n:=i) (1:ℝ)).writes i le_rfl
include hx
-- booking as formal word with normalized marker poles (coupler negative powers)
lemma export_tape : dialect (Ω (Flute.bill W P) (Flute.size k P))=∏ i∈P,dialect (Ω (W i) (k i)):= by
 induction P using Finset.induction_on with
 | empty=> rw [Flute.bill, Flute.size, Finset.prod_empty, Finset.sum_empty,Finset.prod_empty, lull]; ext i; rw [PowerSeries.coeff_one]; exact PowerSeries.coeff_mk _ _
 | insert i s hi ih=>
   have he:= hx i (mem_insert_self ..); have hk:= fun k (hk:k∈s)=> hx k (mem_insert_of_mem hk); let a:= W i; let v:= Flute.bill W s
   have hh:= Flute.roof _ _ _ hk; let f₁:= Schema.coda F a D u; let f₂:= Schema.coda F v D u; have hc: Schema.coda F (a*v) D u=f₁*f₂:=rfl
   rw [Finset.prod_insert hi,← ih hk, show Flute.bill W (insert i s)= a * v from Finset.prod_insert hi, Flute.size,Finset.sum_insert hi,poem,hc,some_mul (Schema.solo_brief F a D he u) (Schema.solo_brief F v D hh u), holy (h₁:=(Schema.glance F a D he u).symm) (h₂:=(Schema.glance F v D hh u).symm), diary]
open Canopy Canopy.Button
-- powerSeries semantics (real vacuum scales & physical occupations)
variable {V:Type} [DecidableEq V] {R:Census V}
omit hx in
lemma legend (K:Multi.Hot R)(w:Word ℝ): Glyph.wire K w=realCurve R w* PowerSeries.C (Poly.send K.val 1):= by
  ext i u; rw [PowerSeries.coeff_mul_C, realCoeff, Poly.product_bead, Glyph.wired,Poly.part_smul,Poly.part_send]; split_ifs <;> simp
-- project complete contributions via canonical serialized product. Order needs loyalty in all (not just t-degree). Reads all marker ring occupations simultaneously.
variable (K:ι→Multi.Hot R)
lemma forest : ∏ i∈P,(Glyph.wire (K i) (Ω (W i) (k i)))= realCurve R (Ω (Flute.bill W P) (Flute.size k P)) * PowerSeries.C (∏ i∈P, Poly.send (K i).val 1):= by
 rw [Comparison.RG02.Assembly.realCurve, show (PowerSeries.mk _ : PowerSeries ℝ)= ∏ i ∈ P,dialect (Ω (W i) (k i)) from export_tape F W k D u hx,map_prod,map_prod]; simp_rw [legend]; exact Finset.prod_mul_distrib
end Roller
end YM.Qlocal.Bind
