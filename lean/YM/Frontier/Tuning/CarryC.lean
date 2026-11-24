import YM.Frontier.Tuning.HeldGate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paisley
import YM.Frontier.Tuning.Held
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Flotsam
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plateau

/-! Locality on the inherited palette, before selecting score determinants. No admissibility of the COMPLEX combined argument should be assumed or needed to switch chart entries. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.Frontier.Tuning.CarryC
open Held HeldGate
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster
open Eider Flux
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k k':Finset ℕ} {R A : Rep G f} {X : Coat T F} {e f':Payload G f} {l : ℕ}
variable {a W : ℝ}{τ:ℂ}{u u':Directions G f}{I I':Config G f}
variable {O:ChartRatio G}
variable {x y : Air f G}{Y : Support c}
variable {r s p q : ℂ} (ho : ∀ i y,e i y =r*R.activities.E i y+s*A.activities.E i y)
      (ht : ∀ i y, f' i y=p*R.activities.K i y+q*A.activities.K i y) (hf : Facing R A)
variable (hr : Intake P T X.x R) (ha : Intake P T X.x A) (hk : Room P S T X.x)
include ho ht hf hr ha hk
set_option maxRecDepth 7000 in
omit hk hr ha in
lemma carry (hh : Room P S T X.x) (h:Transfer X u u' (4*a*X.t)) (hp:0<a*X.t)(hQ:X.Noncrystal)(i:Head S) :
  emberC X R I u (sweepZ X R.beta u) O a W k τ l e f' i=emberC X R I u' (sweepZ X R.beta u') O a W k τ l e f' i:=by
  have hx (B:Rep G f) := Transfer.carries X h hp hh hQ I O B W l k i
  rcases i with j|j|j|j
  · change ite _ _ 0=ite _ _ (0:ℂ); split_ifs; swap;· rfl
    exact termAlign hf.pos j fun B _=> Transfer.outfit X h j hh hp O I W B k
  · rw [mix_K X R I u _ O _ _ k _ A ht hf, mix_K X R I u' _ O _ _ k _ A ht hf]
    rw [show sheath X a R u I j=sheath X a R u' I j from hx R,show sheath X a A u I j=sheath X a A u' I j from hx A]
  · apply congr_arg (fun h:ℂ=> Complex.exp h-1) (show comboLog _ _ _ u (sweepZ X R.beta u) O _ _ _ j=comboLog _ _ _ u' (sweepZ X R.beta u') O _ _ _ j from ?_)
    rcases j with (j|j)|j
    · have he (B:Rep G f) : logMoment X a B O u I (sweepZ X R.beta u) (.inl (.inl j))=logMoment X a B O u' I (sweepZ X R.beta u') (.inl (.inl j)):= by
        exact Real.exp_injective (sub_left_inj.mp (hx B))
      rw [mix_log X R I u _ _ _ _ A ho hf,mix_log X R I u' _ _ _ _ A ho hf, he R,he A]
    all_goals apply congr_arg (fun v:ℝ=> (if flips c f _ then τ/R.beta else 1:ℂ)*v) (Real.exp_injective (sub_left_inj.mp (hx R)))
  exact congr_arg Complex.ofReal (hx R)

variable {K K':ℝ}(C:Config G c)(hm : Canary G K K')
include hm
omit hk in
lemma thatches (h:Drivable X K K' C)(hp:0<a*X.t)(hv:8*a*X.t ≤ K/2)(hQ:(vary X C).Noncrystal) (hh:Room P S T X.x)
  (i:Head S)(z:Air f G)(g:Directions G f)(hg:g=worldZ X R.beta z): let Z:=vary X C; let w:=steer X K (fun i=>prune K (g i)) C; let y:= course X K R.beta z C
  emberC Z R (Z.input (worldZ Z R.beta y)) (worldZ Z R.beta y) y O a W k τ l e f' i=emberC Z R (X.input g) w (sweepZ Z R.beta w) O a W k τ l e f' i:=by
  intro Z w y
  generalize ht': worldZ Z R.beta y=u
  let n:=steer X K g C
  have hZ:u=n:=(show worldZ Z R.beta y=u from ht').symm.trans ((Silica.proceeds X K hr.positive z C).trans (congr_arg (steer X K · C) hg).symm)
  have hY:y=sweepZ Z R.beta u:= hZ.symm ▸ congr_arg (fun n=>sweepZ Z R.beta (steer X K n C)) hg.symm
  have hS : Armor Z a n (Z.input n) (X.input g):= plastic (conquered X hm C g h hp hv) hp
  have hS': Armor Z a u (Z.input u) (X.input g):=hZ.symm ▸ hS
  have hM : Transfer Z u w (4*a*X.t):= hZ.symm ▸ ⟨(fruit X hm C g (by nlinarith only [hv,hm.warm])).both⟩
  calc emberC Z R (Z.input u) u y _ _ _ _ _ _ _ _ _ = emberC Z R (X.input g) u y _ _ _ _ _ _ _ _ _ := reel ho ht hf (X:=Z) hr ha hh hS' i
       _ = _ := congr_arg (fun y=> emberC Z R (X.input g) u y O a W k τ l e f' i) hY |>.trans (carry ho ht hf (X:=Z) hh hM hp hQ i)
end YM.Frontier.Tuning.CarryC
