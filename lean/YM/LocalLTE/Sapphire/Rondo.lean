import YM.MergeProof.MixLaw
import YM.MergeProof.Appl


/-!
# Exact consumable record of the signed unmarked branch and switching probes
-/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0)

variable [Fintype V] (ho : ∀ i, (z i).part B.quiet=0)

variable {kr:ℝ}{I':Type} (F':I'→ Config G c→ Ways ι)
    (h:Pays A.activities A.p K kr A.p.supportExponent)
    (hB:∃ a:I'→ℝ,Summable a∧∀ i,Paid (F' i) (a i))
    (ht':∀ i U,F' i U 0 ∅=0)
    (hL: ∀ U (t:ℝ)(p:Finset ι), t∈Set.Icc 0 1 → Real.exp (A.exponent U)*Real.exp (∑' i,F' i U t p)* (black A.activities (K t p)).gas A.p U=S.push R.beta (Palette.buy M (Palette.ways rA t p) S) U)
local notation "f0"=> F' 
include ho h hB ht' hL Y hZ
lemma whistler (U: Config G c) : (Real.exp (A.exponent U):ℂ) • (Poly.pass (∑' i,sound z (f0 i U))*∑' p,fronts A.activities (fun i=> sound z (fun t p=>K t p i U)) U A.p p) = S.push R.beta (given (S:=S) M rA B z) U :=by
   obtain ⟨f,hF,hp⟩:=hB
   let u (p : I')(t:ℝ)(V:Finset _):=f0 p U t V
   let L: Ways ι:=fun t p=> ∑' i,u i t p
   have hp' p: Paid (fun _:Unit=> u p) (f p):=Paid.toPoint _ (hp p) _
   have hh : HasSum (fun i=>sound z (f0 i U)) (sound z L):= soundSum z u hp' hF (fun _ _ _=>rfl)
   have ht : Paid (fun _: Unit=>L) (∑' i,f i):= (Switch.issue hp' hF).1
   have h0 : (sound z L).part B.quiet=0:=by rw [Switch.sunset (fun _:Unit=>L) ht z () ho]; unfold L; simp only [u]; simp [ht']
   let E: Ways ι:=fun t p => Real.exp (L t p); let V:Ways ι:=fun _ _=>Real.exp (A.exponent U)
   let t i (u:ℝ)(p:Finset ι):= tomes A.activities K (P:=A.p) i U u p
   let Z : Ways ι:=fun s p=> ∑' i,t i s p
   obtain ⟨b,hb,hB⟩:= tomes_budget _ _ h;
   have hZ': Paid (fun _:Unit=>Z) (∑' i,b i) := (Switch.issue (fun i=>show Paid (fun _:Unit=> t i) _ from (hB i).toPoint _ U) hb).1
   let a:=Real.exp (A.exponent U)
   have hv : Paid (fun _:Unit=>V) ‖a‖:=Switch.constant _ (norm_nonneg a) (fun _=>le_rfl)
   rw [which M Y, hh.tsum_eq, (Photo.holds z hZ A.activities K h U).tsum_eq, ← GridRenewal.Rain.passes (sound z L) h0]
   change (↑a:ℂ) • (cyclone (sound z L)*sound z Z)=sound z _
   rw [← show sound z (V*(E*Z))= sound z (fun t p=> S.push R.beta (buy M (ways rA t p) S) U) from congr_arg (mapScores B z) (Switch.cong (Switch.approached.mono fun i hi=> funext fun j=> (by rw [← hL _ i j ⟨hi.1.le,hi.2⟩]; change a*(_* _) = a *_* Z i j; ring))) ]
   have hE : Paid (fun _:Unit=>E) _:=ht.exponential
   rw [mul_sounds z hZ (show Models V _ from (hv.works ()).choose_spec) (show Models (E*Z) _ from ((hE.mul hZ').works ()).choose_spec),mul_sounds z hZ (show Models E _ from (hE.works ()).choose_spec) (show Models Z _ from (hZ'.works ()).choose_spec), show sound z E= _ from soundExp z hZ ht,const_sounds,Poly.product_bead]
end YM.Merge.Photo
