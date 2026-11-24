import YM.FormalOPE.RG10.OpenSlots.Matrix
/-!
 # Full-field unmarked gauge evaluation scaffolding. Hessians are not assumed nondegenerate off-slice.
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
namespace Quadratic
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 def recordQ (Λ:Law E): Quadratic E:=⟨Λ.P,Λ.turns⟩
lemma biplus (Q:Quadratic E)(x y:E) : Q.flourish (x+y) = Q.flourish x + Q.flourish y+ 2* Q.P x y:= by unfold flourish; rw [map_add]; simp only [LinearMap.add_apply,map_add, Q.side y x]; ring
lemma constant0 (Q:Quadratic E) : Q.flourish 0=0:= by unfold flourish; rw [map_zero] -- works
lemma records (Q R:Quadratic E)(h:∀x,Q.flourish x=R.flourish x): Q.P=R.P:= by
 ext x y; have he:=Q.biplus x y; simp_rw [h] at he; linarith [R.biplus x y]
 def RespectsPrice (Q:Quadratic E): Prop:= ∃ P: Law E,Q.P=P.P
namespace RespectsPrice
 def inner {Q: Quadratic E}(h: Q.RespectsPrice): Law E:= h.choose
lemma pinpoints {Q: Quadratic E}(h: Q.RespectsPrice){P: Law E}(hp:Q.P=P.P): inner h=P := by
 have he:h.choose.P=P.P:= Eq.trans h.choose_spec.symm hp
 unfold inner; generalize hh: h.choose=L at *; cases L; cases P; congr
end RespectsPrice

variable (Q:Quadratic (E×F))
variable [FiniteDimensional ℝ E]
 def core (Q:Quadratic (E×F)):= Quadratic.drag (LinearMap.inl ..) Q
 def changing : F →ₗ[ℝ] Module.Dual ℝ E:= LinearMap.compl₂ (Q.P.comp (LinearMap.inr ℝ E F)) (LinearMap.inl ℝ E F)
 def skew (h:(core Q).RespectsPrice) : F→ₗ[ℝ] E:= -(h.inner.inverse ∘ₗ changing Q)
 def reduced (h:(core Q).RespectsPrice) : Quadratic F:= drag ((skew Q h).prod LinearMap.id) Q
end Quadratic

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
-- stage one decomposition.
 def gated (P: Inside S.ratio)(U:Unmasked G f)(t:S.Choices)(w:PowerSeries ℝ): Quadratic ((Cross (G:=G) S P) × Flats G c):= addOn (drag (blankRight P) U.Q) (genesis w (substep P t))
-- bank layer and pop notation.Use explicit binders where macro precheck off
namespace Bank
variable {J:ChartRatio G}{U:Unmasked G f}
-- proofs with layout
lemma well {z:(layer S H t hf L).Cost→PowerSeries ℝ}{Λ: Law Ω}{V:Ticket Ω}
 (h:Bank T0 J z U Λ V)(x y) : (recordQ Λ).flourish (d (x,y))= (gated P U t (z none)).flourish (x,castAt C y)+remainderQ C (z ∘ some) y:= by
 unfold recordQ flourish; rw [h.main, moored, remaining]; change _ = ((U.Q.flourish _)+ _) + _; rw [← add_assoc]; rfl
lemma rad {z:(layer S H t hf L).Cost→PowerSeries ℝ}{Λ:Law Ω}{V:Ticket Ω}(h:Bank T0 J z U Λ V): (core (gated P U t (z none))).P=(fast Λ d).P:= records _ (recordQ (fast Λ d)) (fun x=> by
    have he:= h.well x 0; rw [map_zero, show remainderQ C (z ∘ some) 0=0 from Finset.sum_eq_zero (fun i _ => constant0 _),add_zero] at he; exact he.symm)
lemma respects {z:(layer S H t hf L).Cost→PowerSeries ℝ}{Λ:Law Ω}{V:Ticket Ω}(h:Bank T0 J z U Λ V): (core (gated P U t (z none))).RespectsPrice:= ⟨fast Λ d,h.rad⟩
-- so mean agrees when coarse fields sliced.
lemma interference {z:(layer S H t hf L).Cost→PowerSeries ℝ}{Λ:Law Ω}{V:Ticket Ω}(h:Bank T0 J z U Λ V) (y:B)(x:F): changing (gated P U t (z none)) (castAt C y) x= mixed Λ d y x:= by
 let Q:=gated P U t (z none); let R:=recordQ Λ; let p:=castAt C y; let e u:= remainderQ C (z ∘ some) u
 have he : R.flourish (d (x,0)) = Q.flourish (x,0):= by change ((fast Λ d).P x) x=((core Q).P x) x; rw [h.rad] -- inspect orientation
 have hf:R.flourish (d (0,y))=Q.flourish (0,p)+e y:= h.well _ _
 have hh:R.flourish (d (0,y) + d (x,0)) = Q.flourish ((0,p)+(x,0))+e y:= by rw [← map_add]; simpa only [Prod.mk_add_mk, zero_add,add_zero] using h.well x y
 rw [biplus,biplus,he,hf] at hh; change Q.P (0,p) (x,0)=R.P (d (0,y)) (d (x,0)); linarith
lemma score {z:(layer S H t hf L).Cost→PowerSeries ℝ}{Λ:Law Ω}{V:Ticket Ω}(h:Bank T0 J z U Λ V)(y:B): skew _ h.respects (castAt C y)= pin Λ d y:= by
 let Q:=gated P U t (z none)
 change -(h.respects.inner.inverse (changing Q _))=-((fast Λ d).inverse (mixed Λ d y)); rw [RespectsPrice.pinpoints _ h.rad]; congr 2; exact LinearMap.ext (h.interference y) -- h reused
lemma lower {z:(layer S H t hf L).Cost→PowerSeries ℝ}{Λ:Law Ω}{V:Ticket Ω}(h:Bank T0 J z U Λ V)(y:B): (rest Λ d).P y y= (reduced _ h.respects).flourish (castAt C y)+ remainderQ C (z ∘ some) y:= by
 change (recordQ Λ).flourish (shaft Λ d y)= (gated P U t (z none)).flourish (skew _ h.respects (castAt C y),castAt C y) + _; rw [namely,h.score,h.well]
end Bank
end YM.FormalOPE.RG10.OpenSlots
