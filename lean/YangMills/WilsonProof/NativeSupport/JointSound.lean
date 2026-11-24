import YangMills.WilsonProof.NativeSupport.JointStage
import YM.MergeProof.Appl

/-! Coherent square-zero substitution for the genuine tagged marked push. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.SelectedKernel
open Merge Merge.Photo JointLeaves
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Supply
open PhysicalNext.Repeat Mallow Lotus Ovens Motion Switch Merge.Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι:Type}[Fintype ι]{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ: Chi) (A:Rep G c) (marks : ι→Finset (Bond c)) (test : ι→Bond c→ℝ→ℝ) (rA:ι→ℝ) (K:ℝ → Finset ι → Code G c)

open Marker GridRenewal.Rain Filter
variable {V:Type}[DecidableEq V] (B : Marker.Census V) (z:ι→Poly B)(hZ:∀ i,z i*z i=0) {y' ex dk:ℝ}(h: Usable M Y χ A marks test rA K dk ex y')

def given (U : Config G c) : Poly B :=
  ∑ I : Tickets (Palette.sign M S),
    ((JointPhysical.push S (bonds marks I.val) (probe marks test I.val) R.beta (team M I).cicada U *
      ∏ j∈I.val,rA j : ℝ) : ℂ) • ∏ j∈I.val,z j

theorem which (U : Config G c) :
    given (S:=S) M marks test rA B z U =
      sound z (fun t p=>physical (S:=S) M marks test U (ways rA t p) R.beta) := by
  let fee (I : Tickets (Palette.sign M S)) := JointPhysical.push S (bonds marks I.val)
    (probe marks test I.val) R.beta (team M I).cicada U * ∏ j∈I.val,rA j
  let g (I : Tickets (Palette.sign M S)) := click I.val (fee I)
  have pay (t : ℝ) (p : Finset ι) : physical (S:=S) M marks test U (ways rA t p) R.beta =
      ∑ I,g I t p := by
    unfold physical
    refine sum_congr rfl fun I _=>?_
    rw [amplitudes]
    unfold g fee click
    split_ifs <;> simp_all; ring
  rw [show (fun t p=>physical (S:=S) M marks test U (ways rA t p) R.beta) = ∑ I,g I from
      funext fun t=>funext fun p=>by rw [pay]; simp only [Finset.sum_apply],
    Switch.summed z univ g (fun I=>‖fee I‖) (fun I _=>paidClick _ (norm_nonneg _) (fun _=>le_rfl))]
  unfold given
  refine sum_congr rfl fun I _=>?_
  rw [show g I=click I.val (fee I) from rfl,gather]

include h hZ
variable [Fintype V] (ho : ∀ i, (z i).part B.quiet=0)
local notation "f0"=> SelectedKernel.tones M Y χ marks test rA
include ho
lemma acts (U: Config G c) : (Real.exp (A.exponent U):ℂ) • (Poly.pass (∑' i,sound z (f0 i U))*∑' p,fronts A.activities (fun i=> sound z (fun t p=>K t p i U)) U A.p p) = given (S:=S) M marks test rA B z U :=by
   obtain ⟨f,hp,hF,hc⟩:=h.exponent
   let u (p : Y.fragrances)(t:ℝ)(V:Finset _):=f0 p U t V
   let L: Ways ι:=fun t p=> ∑' i,u i t p
   have hp' p: Paid (fun _:Unit=> u p) (f p):=Paid.toPoint _ (hp p) _
   have hh : HasSum (fun i=>sound z (f0 i U)) (sound z L):= soundSum z u hp' hF (fun _ _ _=>rfl)
   have hL : Paid (fun _: Unit=>L) (∑' i,f i):= (Switch.issue hp' hF).1
   have h0 : (sound z L).part B.quiet=0:=by rw [Switch.sunset (fun _:Unit=>L) hL z () ho]; unfold L; simp [u,SelectedKernel.tones]
   let E: Ways ι:=fun t p => Real.exp (L t p); let V:Ways ι:=fun _ _=>Real.exp (A.exponent U)
   let t i (u:ℝ)(p:Finset ι):= tomes A.activities K (P:=A.p) i U u p
   let Z : Ways ι:=fun s p=> ∑' i,t i s p
   obtain ⟨b,hb,hB⟩:= tomes_budget _ _ h.gas;
   have hZ': Paid (fun _:Unit=>Z) (∑' i,b i) := (Switch.issue (fun i=>show Paid (fun _:Unit=> t i) _ from (hB i).toPoint _ U) hb).1
   let a:=Real.exp (A.exponent U)
   have hv : Paid (fun _:Unit=>V) ‖a‖:=Switch.constant _ (norm_nonneg a) (fun _=>le_rfl)
   rw [which M marks test rA B z U, hh.tsum_eq, (Photo.holds z hZ A.activities K h.gas U).tsum_eq, ← GridRenewal.Rain.passes (sound z L) h0]
   change (↑a:ℂ) • (cyclone (sound z L)*sound z Z)=sound z _
   rw [← show sound z (V*(E*Z))= sound z (fun t p=> physical (S:=S) M marks test U (ways rA t p) R.beta) from congr_arg (mapScores B z) (Switch.cong (Switch.approached.mono fun i hi=> funext fun j=> (by rw [← h.closed _ i j ⟨hi.1.le,hi.2⟩]; change a*(_* _) = a *_* Z i j; ring))) ]
   have hE : Paid (fun _:Unit=>E) _:=hL.exponential
   rw [mul_sounds z hZ (show Models V _ from (hv.works ()).choose_spec) (show Models (E*Z) _ from ((hE.mul hZ').works ()).choose_spec),mul_sounds z hZ (show Models E _ from (hE.works ()).choose_spec) (show Models Z _ from (hZ'.works ()).choose_spec), show sound z E= _ from soundExp z hZ hL,const_sounds,Poly.product_bead]

end YM.Integration.InletSusceptibility.SelectedKernel
