import YM.FVAAlt2.Aperture.Score
/-!
# Absolute chart actual-model comparison at any transported parameter value

Not a gauge identity away from properties. Era β trajectory not changed. `budget g` and
 `temperature (C.enter t)` retained; both positive wherever needed, true kernels. Section label χ slopes optional extra scalar. Pins.Herm all ranks. Later choose to t.p.Prop
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Aperture
open Set Filter Finset MeasureTheory Function Lattice RG Precision Wilson Exterior Tree Bid
open PertExtension.Series Bulk Adjacent Order Assembly Marker Multi YM.Next.SectorChange Integral Gaussian
open Work.F03
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure Actual
open scoped Topology ContDiff Classical Matrix BigOperators ENNReal NNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P:PathData G}{p:Clip}{O:ChartRatio G}{S:StepData c f}
variable (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(w:S.Choices)(C:UnitCost)
variable {V:Type} [DecidableEq V] {R:Census V}(W:Bulk.Colors R G f)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=>Bulk.Joint S F (G:=G)
local notation "L"=>Precision.Key F G→ℝ
local notation "ρ" => C.enter
local notation "H" => F.Slice G
local notation "Q" => K.covariance F w
open Classical
variable (t:ℝ) (x:fieldDir G c 1)
local notation "ζ"=> Bulk.translated K F x
local notation:max "β_" z:max=> temperature (ρ z)
local notation:max "V_" z:max => sample z x
local notation:max "weight_" z:max y:max => Integral.weight (ρ z) 0 y W p P

def swing (v:L):= starship F (t • ζ v)
abbrev coast (v:L): H:= release (1:F.Slice G) (swing K F t x v)
local notation:max "U_" g:max v:max => F.drape (coast K F g x v)
lemma signal (v:L): swing K F t x v=t • starship F (stage K F x)+ t • tape v:=by
   unfold swing;rw [map_smul];unfold Bulk.translated Assembly.translate; rw [map_add,smul_add]; congr 1
   rw [show starship F (Bulk.hinge F v)= tape v from ?_]
   funext i; rw [free_at, linearCopy]; split <;> exact (zero_add (tape v i))

def deposit := t • tape.symm (starship F (stage K F x))
lemma migrate (v:L) : swing K F t x v= displaced (deposit K F t x) t v:=by rw [signal]; unfold deposit displaced; change t • _ + t • gaugeCount v=gaugeCount (t • (gaugeCount.symm (starship F (stage K F x)))+t • v); rw [map_add,map_smul,map_smul,gaugeCount.apply_symm_apply]
@[fun_prop] lemma swing_cont : Continuous (swing K F t x):=by
   unfold swing; apply ( starship F ).continuous.comp; exact (Laplace.translated_cont K F x).const_smul t
lemma priceA (z:T): fineScore F w K z= mainTerm p P (opens F z)+ noiseTaylor S (represent z.2.1) (opens F z) w:=by unfold fineScore; rw [uniting_eq]; unfold opens; rw [uniting_eq];rfl
lemma rolled (v:L) : opens F (t • ζ v)= U_ t v:= (clamped F _).symm
variable (B : Bed)(hB : YM.FVAAlt2.Period.Rent.Right p P f B)
local notation "K'"=> Bulk.infrared S p P F w (K.b F) x
include hB
lemma all_cost (hW : Well W)(ht:0<t)(h:0<C.rating t)(v:L) :
   (0:ℝ)- K'+ Radial.higher (core K F w C W) t (ζ v)=
     force (Q) v/2 + Real.log (∏ i,O.J (swing K F t x v i)) - β_ t * noiseTaylor S ( sample t x ) (U_ t v) w + (0 - localClassic (ρ t) (U_ t v) W p P - loop P (U_ t v)) := by
     have hV :0<ρ t:= mul_pos ht h; have hp:(t • ζ v).1=t:= by rw [Integral.ribbon_eq]
     have hx:(t • ζ v).2.1=t • x:= by rw [Integral.ribbon_eq]
     let u:= U_ t v; let V':= V_ t
     let E:= force (Q) v/2; let J:= Real.log (∏ i,O.J (swing K F t x v i)); let y':=t • ζ v
     -- Hessian+exponent alignment with R'
     unfold Radial.higher; rw [← Assembly.jet_eq,scored K F w C W B hB hW]; unfold core adorn freshvac pillar reprc baseRatio; rw [priceA,rolled,hx,hp] -- all
     unfold localClassic; change 0 - K' + ( -_ / _ + _) = _; unfold temperature UnitCost.enter Integral.sample swing; field_simp; ring
omit hB
lemma mark_clock (v:L) : markedLog (ρ t) (U_ t v) W=Assembly.smoothMark W.power (scoreMark F C W) t (ζ v):=by
    unfold markedLog Assembly.smoothMark Assembly.divided
    apply congr_arg; funext i; unfold scoreMark;dsimp only; rw [rolled,Integral.ribbon_eq]; -- walk inside left changes
    change ((ρ t)^_)⁻¹ • _= (t ^ _)⁻¹ • ((C.rating t ^ _)⁻¹ • _); rw [UnitCost.enter,mul_pow,mul_inv,smul_smul]
section Haar
private lemma reorder {a b c d e r y z X' Υ Z:ℝ} (h : a+b=c+d-e*r+y) :
    Real.exp c*(X'*Real.exp d)*(Υ*(Z * Real.exp (-e*r))*Real.exp y)*z = Υ*(X'*Z*Real.exp a) * Real.exp b*z := by
    rw [show -e*r=-(e*r) by ring]; have he:= congrArg Real.exp h
    rw [sub_eq_add_neg] at he; simp_rw [Real.exp_add] at he; linear_combination -(Υ*X'*Z*z)*he
include hB
lemma funded (v:L)(ht:0<t)(h:0<C.rating t)(hw: Well W)(hm:swing K F t x v∈ mouth O) :
  let u := U_ t v
  Real.exp (force (Q) v/2)*pay O (swing K F t x v)* (taggedKernel S (temperature (ρ t)) w u ( V_ t )* weight_ t u)= (S.likelihood u w* standard K F w (ρ t) 0 x)*Real.exp (Radial.higher (core K F w C W) t (ζ v)):=by
    dsimp only; unfold taggedKernel; have hx:= (all_cost K F w C W t x B hB hw ht h v); let e:=prefactor S G (temperature (ρ t)); let y:= U_ t v
    rw [weight_formula]; rw [show pay O (swing K F t x v)=Integral.tab (O:=O) (F:=F)*Real.exp (Real.log (∏ i,O.J (swing K F t x v i))) from ?_]; swap
    · rw [Real.exp_log (Finset.prod_pos (fun i _=> K.ratio.pos _ (hm i (Set.mem_univ _))))]; unfold pay Integral.tab; rw [Finset.prod_mul_distrib]; simp
    simpa only [standard,calorie,Integral.weight,mul_one] using! (reorder (X':= Integral.tab (F:=F) (O:=O)) (Υ:= S.likelihood (U_ t v) w) (Z:=e) (z:=1) hx)
variable [Fintype V]
def dims (v:L): Poly R:= Assembly.numeric W.power (scoreMark F C W) (core K F w C W) t (ζ v)
lemma promised (v:L)(ht:0<t)(h:0<C.rating t)(hw: Well W)(hm:swing K F t x v∈ mouth O) :
    let u:= U_ t v
    Complex.ofReal (Real.exp (force (Q) v/2)*pay O (swing K F t x v)) • Actual.stack w (V_ t) (temperature (ρ t)) (model (ρ t) 0 W K) u=
       Complex.ofReal (S.likelihood u w* standard K F w (ρ t) 0 x) • dims K F w C W t x v := by
    dsimp only; unfold stack model; rw [mark_clock]; unfold dims Assembly.numeric; rw [Poly.product_bead]; simp_rw [smul_smul,← Complex.ofReal_mul]
    rw [funded K F w C W t x B hB v ht h hw hm]
end Haar
end YM.Comparison.RG02.FVAAlt2.Aperture
