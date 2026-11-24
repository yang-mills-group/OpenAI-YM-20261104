import YM.FormalOPE.RG10.OpenSlots.Banker
/-!
 # Move layer costs past the cover pair. Here cover pair means full quotient orbits
 extension, not the lattice cover estimates. All results in fixed inversion trusses.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S: StepData c f} {L: Fabric G c} {P:Inside S.ratio}
variable {H:S.patch.Branches S.kernel G} {hf:_root_.Even f.val}{t:S.Choices} {C:Cloth L}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ω"=> Field (Cloth.choose T0)
local notation "F"=> Cross (G:=G) S P
local notation "B"=> Field C.choose
local notation "κ"=> exchange (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "π"=> spool (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Γ"=> layer S H t hf L
open Quadratic
lemma withinOne : cost_core T0 (some none)= substep P t ∘ κ:= by
 ext1 u; obtain ⟨⟨x,y⟩,rfl⟩:= (d).surjective u; rw [comp_apply,trade]; unfold substep
 rw [←moored (t:=t) (H:=H) (hf:=hf) (P:=P) x (C:=C) y, accord_top, accord_top]
 apply congr_arg (BlockGauge.penalty S t ((Γ).principal (realTop T0 _))) ?_; exact congr_arg L.principal (Line.future_eq ..) -- check
lemma withoutOne (i:L.Cost) : cost_core T0 (some (some i))= cost_core C (some i) ∘ π:= by
 ext1 u; obtain ⟨⟨x,y⟩,rfl⟩:= (d).surjective u; rw [comp_apply,spinning]; exact congr_arg (fun u=> L.regional u i) (Line.future_eq ..)
-- decomp
-- use explicit binders. type issues Fintype across Γ.Cost and Options. C!
lemma remaining (z:(layer S H t hf L).Cost→PowerSeries ℝ)(x y):
 remainderQ T0 z (d (x,y))=(genesis (z none) (substep P t)).flourish (x,castAt C y)+ remainderQ C (z∘some) y:= by
 unfold remainderQ; change ((∑ i:Option L.Cost,_)=_); rw [Fintype.sum_option,withinOne,← payments κ _ _ (subReady P t H), trade]; congr 1
 apply Finset.sum_congr rfl; intro i _; rw [withoutOne, ← payments π _ _ (show ContDiffAt ℝ ω (cost_core C (some i)) 0 from (punctual L C.choose _).smooth), spinning]; rfl
lemma stocked (z:(layer S H t hf L).Cost→PowerSeries ℝ): remExponent T0 z= boost κ (chip (z none) (substep P t))* Ancestor (remExponent C (z∘some)):= by
 unfold remExponent; change ((∏ i:Option L.Cost,_)=_); rw [Fintype.prod_option,withinOne,←pullPay κ _ _ (subReady P t H)]; congr 1
 · unfold Ancestor; rw [map_prod]; refine Finset.prod_congr rfl fun i _=>?_; rw [withoutOne, ← pullPay π _ _ (show ContDiffAt ℝ ω (cost_core C (some i)) 0 from (punctual L C.choose _).smooth)]; rfl

-- empty
lemma done {n:Side}{h:_root_.Even n.val} {T:(Fabric.endcap (G:=G) n h).loom.Truss} (z:(Fabric.endcap n h (G:=G)).Cost→PowerSeries ℝ) (x): remainderQ (Cloth.floor n h T) z x=0:= by unfold remainderQ; change (∑ i:Empty, _)=_; simp
lemma off {n:Side}{h:_root_.Even n.val} {T:(Fabric.endcap (G:=G) n h).loom.Truss} (z:(Fabric.endcap n h (G:=G)).Cost→PowerSeries ℝ): remExponent (Cloth.floor n h T) z=1:= by unfold remExponent; change (∏ i:Empty, _)=_; simp
end YM.FormalOPE.RG10.OpenSlots
