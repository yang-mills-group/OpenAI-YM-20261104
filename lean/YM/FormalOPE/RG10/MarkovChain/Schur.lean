import YM.FormalOPE.RG10.MarkovChain.Bills
/-!
 # Schur evolution. If initial precision rests on Marking staircase, each Schur
 retains additive bands; proper mean is determined only by adjacent coarser **gauge-fixed**
 field. No assumption of the winding estimates.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Line
variable {G:Gauge}{c f n:Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
 def Actual {L:Fabric G n}(T:Cloth L) (Λ: Law (Field T.choose)) := Roof T fun x=> Λ.P x x
namespace Actual
local notation "T0" => Cloth.inLayer (b:=H) (t:=t) (h:=hf) P C
local notation "M"=> P.join C.choose H t hf
local notation "Ω"=> Field M
local notation "d"=> sector S H t hf L P C.choose
variable (Λ: Law (Field (P.join C.choose H t hf)))
local notation "Y"=> (fun (x:Field M)=> Λ.P x x)
lemma turns (h:Actual T0 Λ) (y z: Field C.choose) (hv:send C.choose y=send C.choose z) : mixed Λ d y=mixed Λ d z:= by
 apply LinearMap.ext; intro x
 unfold Actual Roof at h -- expands at tail.S
 have he:= h.1 x y z hv
 change Y (d (x,y))-Y (d (0,y))= Y (d (x,z)) - Y (d (0,z)) at he
 have ha (w: Field C.choose): Y (d (x,w)) = Y (fine d x)+Y (d (0,w)) +2*(mixed Λ d w x):= by
    dsimp only; rw [show d (x,w)= fine d x+d (0,w) from by change d (x,w)= d (x,0)+d (0,w); rw [←map_add]; simp]
    simp only [map_add,LinearMap.add_apply]; rw [Λ.turns (fine d x) (d (0,w))]; change _= _+2*(Λ.P (d (0,w)) (fine d x)); ring
 dsimp only [mixed,LinearMap.compl₂]; rw [ha y,ha z] at he
 change mixed Λ d y x=mixed Λ d z x; linarith
lemma spans (h:Actual T0 Λ): Heads C.choose (pin Λ d):= by
 intro y z hv; change -_ = -_; exact neg_inj.mpr (congr_arg ((fast Λ d).inverse) (turns Λ h y z hv))
lemma revenue (h:Actual T0 Λ): Actual C (rest Λ d):= by
 let Q:= enduring S H t hf P (T:=C.choose) Y
 let R:= fun (x:Field C.choose)=> Y (shaft Λ d x)-Q x
 have he: Heads C.choose R:= by
   intro x y hv; dsimp only [R]; unfold Actual Roof at h; change Y _-_=Y _-_
   have hk:pin Λ d x=pin Λ d y:=spans Λ (show Actual T0 Λ from by unfold Actual Roof; exact h) x y hv
   rw [namely,namely,←hk]; exact h.1 _ x y hv
 have hh:Roof C Q:= by unfold Actual Roof at h; exact h.2
 unfold Actual; rw [show (fun x:Field C.choose=> (rest Λ d).P x x)=R+Q from funext (fun x=> (sub_add_cancel (Y (shaft Λ d x)) (Q x)).symm)]
 exact Roof.add (Roof.head he) hh

lemma credible {L:Fabric G n}(T:Cloth L) (w:L.Accounts→PowerSeries ℝ)(hw:∀ i,0<term (w i) 0): Actual T (evidence _ (enough L T.choose w hw).entire):= by
 set A:= model L T.choose w
 have hh: A.Ready:= enough L T.choose w hw
 let a:= A.target∘ expLinks G _
 have he (x): (evidence (H:=hh.entire) _).P x x = 2*jet a 2 x:= by rw [← origin_p a]; change MultiGauge.Splice.polar a x x = 2*(MultiGauge.Splice.polar _ x x / 2); ring
 have ha: Roof T a:= Roof.habituate T (fun i=> term (w i) 0)
 unfold Actual; change Roof T (fun x=> (evidence (H:=hh.entire) _).P x x); rw [funext he]; exact Roof.smul (Roof.differentiated (a:=a) (hh.entire.smooth.of_le le_top) (ha) 2) (2:ℝ) -- signature smooth already omega; Roof differentiated ∞
end Actual
end YM.FormalOPE.RG10.MarkovChain
