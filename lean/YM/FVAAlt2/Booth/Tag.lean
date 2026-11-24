import YM.FVAAlt2.Booth.Primitive
import YM.FVAAlt2.Aperture.Register
import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Shadows
/-! # Actual planar log instructions from these supplied Prim.T. Trace exactly on every circle/fork, on real fixed-chart ratio chosen at **the same Chain**, not $Prim ratio$. Bound Exp.Goz. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth.Tape
open Function Finset MeasureTheory Filter Set Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Deck Motion Prim PertExtension Chart Lattice Tree Gauge Binding Diagram Diagram.Formal RG Wilson Oracle Geometry
open FreeResolvent (flatten PAC)
open Exterior
open Precision Bid Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix Matrix.Norms.Frobenius
variable {c f n:Side}{G:Gauge}{p: RG.Clip}{O:ChartRatio G}{U:PathData G}
variable (S:StepData c f)(F:Forest S.ratio) (L: Binding.Scale) (H:S.patch.Branches S.kernel G)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=> Comparison.RG02.Bulk.Joint S F (G:=G)
local notation "Q"=>Pins f c G

-- instantiate full projection. y includes all pin mask. z constant extra

def announceT (u: Work.F03.Logs G c f) : Pins f c G→ℝ:= Sum.elim (flatten u.2) (flatten u.1)
lemma traverseT (u: T) : announceT (Aperture.uniting F u)=Sum.elim (flatten (stretch F u.2)) (flatten u.2.1):=by rw [Aperture.uniting_eq];rfl
lemma pledged (d:Side)(z:Edge (Site d)): around d (hop d z)= z:= by unfold hop around; rw [wrap_lift]
lemma timberP (x:fieldDir G n 1)(j:Edge Cover)(t:ℝ) : timber G ((t • flatten x) ∘ imprint G n ) j= t • Exterior.collect G x (around n j):=by ext1 i;rfl
lemma panorama (x:fieldDir G n 1)(t:ℝ) : win G ((t • flatten x) ∘ imprint G n )= represent (t • x) ∘ around n:=by
   funext j; rw [Function.comp_apply,Work.F03.represent_link,win,timberP]; rfl
variable {V:Work.F03.Logs G c f}
local notation "V₁"=> (announceT V) ∘ joint G f c
-- Prim.Flank uses horizontal.Aff

lemma darb (i:Edge Cover)(t:ℝ) : flank (prism S F L (Sum.inr i)) (V₁) t = L.beta t*S.kernel.penalty*G.price (represent (t • V.1) (around c i)*(S.prediction (represent (t • V.2)) (Geometry.directive S) (around c i))⁻¹):=by
   unfold flank prism; dsimp only [Sum.elim_inr]; unfold opi; let U':=t • ( (announceT V) ∘ joint G f c ); have hf: U' ∘ Sum.inl= (t • flatten V.2)∘imprint G f:=rfl; have he: U'∘ Sum.inr=(t • flatten V.1)∘ imprint G c:=rfl; change L.beta t*_ * G.price (win G (U' ∘ _) i* (pond S.patch S.kernel (win G (U'∘ Sum.inl)) i)⁻¹)= _ -- inv grammar issue
   rw [hf,he,panorama,panorama, river ]; rfl
variable (V) (w: Geometry.Field.Square F)
include w
lemma savored (x:Edge (Site f))(t:ℝ): flank (prism S F L (Sum.inl (hop f x))) V₁ t= if x∈F.trunks then 0 else entry G (t • Exterior.collect G V.2 x):= by
    change carnal S F _ t _=_; unfold carnal; let A:=announceT V; rw [show resolve f (hop f x)=Orb.index x from congr_arg Orb.index (pledged ..),Field.bone w]; split
    next hx=> rfl
    next hx=> change entry G (timber G ((t • flatten V.2)∘ imprint G f) _)=_; rw [timberP,pledged]
omit w
open PowerSeries
include H
lemma outcomesR : ∑ i:Edge (Site c), Prim.tale (flank (prism S F L (Sum.inr (hop c i))) V₁)= Prim.tale (fun t:ℝ=> L.beta t*noiseTaylor S (represent (t • V.1)) (represent (t • V.2)) (directive S)):= by
    rw [← tale_sum]; swap; · exact fun i _=> (locally S H L _).some.smooth_v _
    apply congr_arg; ext1 t; rw [Finset.sum_apply]; simp_rw [darb, pledged]; unfold noiseTaylor; rw [←mul_assoc, Finset.mul_sum]
omit H
variable (K: Comparison.RG02.Bulk.Kernel S p U O)
local notation "J" => (Orb.tray G)
include K
lemma rootedO : ∀ᶠ x:G.Color in 𝓝 0, entry G x=Real.log (O.J x) := by
    have hv:= K.ratio -- O hardware.Parameter
    let H:= Orb.traySpec G
    let V':= (J).J
    have hS := MS.Bare.Maurer.real_ratio (G:=G) H
    have hu : (J).J=ᶠ[𝓝 0] O.J:= hS.trans (MS.Bare.Maurer.real_ratio K.ratio).symm
    filter_upwards [Prim.genuine G, hu, ( show ∀ᶠ x in 𝓝 (0:G.Color),0<(J).J x from by have hl := H.germ 0 (Metric.mem_ball_self H.patch); exact hl.continuousAt.eventually (lt_mem_nhds (show 0<(J).J 0 from H.anchored.symm ▸ zero_lt_one)) ) ] with i hi hz hl
    rw [hi]; unfold Prim.ent; rw [← hz]; unfold Chart.fee; rw [H.anchored,max_eq_left (mul_nonneg H.scale.le hl.le),mul_one,max_eq_left H.scale.le,mul_div_cancel_left₀ _ H.scale.ne'] -- check
variable (x: Comparison.RG02.Bulk.Joint S F (G:=G))
local notation "U'" => Aperture.uniting F x
local notation "Ξ"=> announceT (U')
local notation "E" => F.Free
local notation "R₁"=> Ξ ∘ joint G f c
abbrev haunt (_ :Comparison.RG02.Bulk.Kernel S p U O) (t:ℝ) (x':Comparison.RG02.Bulk.Joint S F (G:=G)):ℝ:= Real.log (∏ i, O.J (Aperture.starship F (t • x') i))
include w
lemma outcomesL : ∑ i:Edge (Site f),Prim.tale (flank (prism S F L (Sum.inl (hop f i))) R₁)= Prim.tale (fun t:ℝ=> haunt S F K t x):= by
    rw [← tale_sum]; swap; · exact fun i _=> (rooted (G:=G) S F _).some.smooth_v _
    let qT(t:ℝ):= ∑ i:F.Free, entry G ( Aperture.starship F (t • x) i )
    have he : ∀ᶠ t in 𝓝 (0:ℝ), haunt S F K t x=qT t:=by
       have hu(i:F.Free): Tendsto (fun t:ℝ=> Aperture.starship F (t • x) i ) (𝓝 0) (𝓝 0):= by simp_rw [map_smul,Pi.smul_apply]; simpa using (show Continuous (fun t:ℝ=> t • Aperture.starship F x i) from continuous_id.smul continuous_const).tendsto (0:ℝ)
       have hz : ∀ᶠ i : G.Color in 𝓝 0,0<O.J i:= (K.ratio.germ 0 ( Metric.mem_ball_self K.ratio.patch )).continuousAt.eventually (lt_mem_nhds (K.ratio.anchored.symm ▸ zero_lt_one));
       filter_upwards [eventually_all.mpr fun i=> (hu i).eventually ((rootedO S K).and hz)] with t ht
       unfold qT haunt; rw [Real.log_prod] -- arg
       · exact sum_congr rfl fun i _=> (ht i).1.symm
       exact fun i _=> (ht i).2.ne'
    have hp : ContDiffAt ℝ ∞ qT 0:= by rw [show qT= psyche F.Free G (Aperture.starship F x) by ext1 t; unfold qT; simp_rw [map_smul,Pi.smul_apply];rfl]; exact psyche_smooth _ _ _
    rw [tale_eq (f:=qT) hp he]; apply congr_arg; ext1 t; rw [Finset.sum_apply]; simp_rw [savored S F L U' w]; unfold qT
    rw [←Fintype.sum_subtype_add_sum_subtype (fun y=>y∉F.trunks) (fun i=> if i∈F.trunks then 0 else entry G _)] -- compute via Equiv.sumCompl if not
    rw [Finset.sum_eq_zero (f:=fun i:{e:Edge (Site f) // ¬ e∉F.trunks}=> if i.val∈ F.trunks then 0 else entry G (t • Exterior.collect G (U').2 i.val)) ?_,add_zero]; swap; intro i _; rw [ if_pos (Classical.not_not.mp i.property) ];
    apply sum_congr rfl; intro i hi; erw [if_neg i.property]; rw [_root_.map_smul];rfl
end YM.RegulatorIR.FVAAlt2.Booth.Tape
