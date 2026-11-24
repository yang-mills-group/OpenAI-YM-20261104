import YM.QuadraticLocal.Echo.Sara
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι:Type} {V:Type}[Fintype V] [DecidableEq V]{G:Gauge} {k j e d i l:ℕ} {a σ Z τ b C ε₀:ℝ} {n f:Side}
open Aperture Poetry Work.G05 Toggle Aux Aux.Name
open Spot Trace
namespace Sara
variable (P:Patch)(K:KernelChoices)
open Kinetic Kinetic.Port
variable {p:Clip}{N:ℕ} (O: ChartRatio G)[Nonempty ι] (x:ι→PathData G)(L:ι→ℝ)(Q:Push.Uniform.Before G a C P.J K (N+3))(hx:∀ i,(x i).Bounds p a C (L i))(hO:LocalRatio O)
variable (F:ι→ candidates P K G)(h:proofC P K p x Q F)(A:ι→Layout G)(T:Finset Age)(hA:∀ i,Legal T (A i))(Γ:ι→ℝ)
variable (I:V→Sunrise.Loan)(s:ι→∀ j:V, Atom G (I j).r) (y:ι→V→Site P.L)(u:V→Site n)(hU: (univ:Finset V).Nonempty)
variable {U:ℕ→ι→ Poetry.Roll G V}{X:ℕ→ι→ Ink.Field (Coarse G⊕V)}
open Sunrise Sunrise.Aviary Comparison.RG02 Kinetic Kinetic.Port
local notation "Hℓ"=> (univ:Finset V)
set_option quotPrecheck false
local notation "δ₀"=> (fun i n=> I)
local notation "T'"=> trees P K n
variable {o:V} (hc: Painted (Ad G P K) I Γ (univ:Finset V) ε₀ k l X (Aviary.window P K p O x L Q hx hO F h A T I s y (univ:Finset V))) (hZ:Agenda.Shelled (univ:Finset V) o I X U Γ l (k+1) b)
local notation "Ŵ"=> (Aviary.window P K p O x L Q hx hO F h A T I s y (univ:Finset V))
local notation "ρ"=> F
local notation "θ"=> (tint G (Exterior.Body 1 n))
variable {κ:Type*}{D:Catch.Clock κ}{r:Stage}{N' u':ℕ}{b':ℝ→ℝ}
variable (Wξ : Push.Uniform.Before G r.width r.paths P.J K ((N'+3)+3))
variable (W:κ→ Aux.Name G P K b' u' r (N'+3) Wξ)
variable (S:∀i, Page (W i) I)(w:κ→ι)
local notation "A₁"=> (fun i=>(W i).price)
local notation "Φ" i:max => (W i).Θ
local notation "n₁" i:max=> (W i).c
local notation "K₁" i:max=> (W i).tube.up
set_option quotPrecheck false
local notation "ℓ₁"=> D.rail
local notation "A₀"=> (fun i j=> U j (w i))
local notation "Θ"=> D.Meter
-- equality anchors all roots vs spectral seats. requires rising side (`radiusB(...)` is actual cheapest field polynomial size.B allowance); discharge later when constructing Ω.
structure Scene (i:κ): Prop where
    matchShape : (W i).shape=A (w i)
    matchAge: Aux.scope u'= T
    clip: (W i).tube.high = p
    matchBundle: (S i).mark=s (w i)
    matchBench : (S i).path=Sara.seat P (W i).data (W i).step (y (w i))
    matchP : (W i).tube.up=x (w i)
    regular : ∀ j:V,(s (w i) j).Invariant
    rising : radiusB (W i).due ≤ (W i).c.val -- can refine by before-L fixed factor; use integer nat
namespace Scene
variable (hW:Aux.Name.Proper W D)
include hW
lemma crowded : Θ (fun i=> (n₁ i |>.val:ℝ)) 0:= by
 refine (Proper.loam W hW).smaller (Eventually.of_forall fun i=>?_); let c:Side:= n₁ i; let f:=(W i).f; have h : c.val≤ f.val:= by
    rw [show f.val=c.val * (W i).data.patch.L.val from (W i).data.sizes]; exact Nat.le_mul_of_pos_right _ (W i).data.patch.L.pos
 rw [abs_of_nonneg (Nat.cast_nonneg _)]; apply le_trans _ (le_abs_self _); exact_mod_cast (h.trans (show f.val≤ Fintype.card (Site f) from (by rw [site_card];exact le_self_pow₀ f.pos (by decide))))
variable (ht:∀ᶠ i in D.rail,Scene P K («p»:=p) x A T I s y Wξ W S w i)
include ht
lemma wind (ha:0<σ)(a:ℝ): Θ (fun i=> Real.exp (-σ*(↑(W i|>.c.val):ℝ))) a:= Function.const _ (Function.const _ (Function.const _ (by
 apply (Looks.melt hW.look a ha).smaller -- order?
 filter_upwards [ht] with i hi; rw [abs_of_nonneg (Real.exp_pos _).le,abs_of_nonneg (Real.exp_pos _).le]; apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr ha.le); exact_mod_cast hi.rising
  ) (inferInstance : Fintype V)
  ) (inferInstance : DecidableEq V)
  ) (inferInstance : Nonempty ι)
omit hW ht
variable (hV: D.Meter (Γ∘w) 0)
include hV
lemma credits {u:ι→ℝ} (h: CreditF Γ l u): D.Meter (u ∘ w) 0:= Function.const _ (by
 obtain ⟨c,hc,h⟩:=h; refine (((((Meter.const D 1).add hV.ab).pow l).lscale c).weak (by simp)).smaller (Eventually.of_forall fun i=> ?_); rw [Function.comp_apply, abs_of_nonneg (h _).1]; exact (h _).2.trans (le_abs_self _)
  ) (inferInstance : Nonempty ι)
include hW
lemma norms {z:ι→Side→ℝ}(h:Weight Γ l z): D.Meter (fun i=> z (w i) (n₁ i)) 0:= by
 obtain ⟨a,h,hx⟩:=h; refine (((credits Γ w hV h).mul ((crowded P K Wξ W hW).pow l)).weak (by simp)).smaller (Eventually.of_forall fun i=>?_); rw [abs_of_nonneg (hx _ _).1]; exact (hx _ _).2.trans (le_abs_self _)
set_option quotPrecheck false
local notation "Ak"=> (fun i=>Kinetic.Port.exteriorL G (W i).c)
-- Actual fixture C': all kernel primitive inputs including φ.
variable (K':∀ i,Comparison.RG02.Bulk.Kernel (W i).data (W i).tube.high (W i).tube.up O)
variable (hv:0 < b)
omit hW hV
lemma within (h:(univ:Finset V).Nonempty) (η:Agenda.Booked (univ:Finset V) o I (U i) Γ i b l)(hi:i≤k): Agenda.Shelled (univ:Finset V) o I X U Γ l (k+1) b → ∃ u:ι→ℝ,CreditF Γ l u ∧ ∀ d:ι,(U i d).Faith (univ:Finset V) o (Agenda.guard I univ k) b (u d):= Function.const _ (Function.const _ (by
 rintro hp; obtain ⟨z,hz,h⟩:=η; exact ⟨z,hz,fun i'=>⟨fun j=> ⟨((h i').1.pinned j).tall.trans (by unfold Agenda.guard Aviary.plusK; omega), ((h i').1.pinned j).considered, ((h i').1.pinned j).owns⟩,(h i').1.price⟩⟩
  ) (inferInstance : Nonempty ι)
  ) (h)
include hW hV hA hc hv ht hZ hU
set_option maxHeartbeats 200000
lemma leaps : Wake.Supply W I S (fun i j=> U j (w i)) o K' D k (Agenda.guard I (univ:Finset V) k) b:= by
 constructor
 · intro i hi; obtain ⟨z,hz,h⟩:= within Γ I hU (hZ.booking i (Nat.lt_succ_of_le hi)) hi hZ; exact ⟨z ∘ w,credits Γ w hV hz, Eventually.of_forall (fun i => h (w i))⟩
 intro d hd; obtain ⟨p,hp,hp'⟩:=Aviary.bindingRate P K p O x L Q hx hO F h A T hA Γ I s y Hℓ hU hc hZ hv hd; let e f:= Agenda.guard I univ f; let z i:=dearth ε₀ (n₁ i)
 refine ⟨e d,fun i=> p (w i) (W i).c*z i*2^e d,fun a=> ((((norms P K Γ Wξ W w hW hV hp).mul (wind P K x A T I s y Wξ W S w hW ht hc.pos a)).rscale (2^(e d):ℝ))).weak (by simp),ht.mono ?_⟩
 intro i hi x'; let A':= W i; let n':Side:= A'.c; let y':= A'.tulip x'
 exact sponsor P K O x L Q hx hO F h A T hA Γ I s y (S i).root hU hc hZ (w i) A'.price hd hv hi.regular A'.data A'.step A'.rates p A'.tube.up A'.tube.high A'.shape _ _ _ A'.loom.large hi.matchP hi.clip hi.matchShape hi.matchAge hi.matchBench hi.matchBundle (K' i) A'.forest A'.choices (hp' (w i)) y'
end Scene
end Sara
end YM.QuadraticLocal.Echo
