import YM.Qlocal.Quipu.Spots
import YM.Qlocal.Quipu.Verge
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c f:Side} {S:StepData c f}{d t a v u C:ℝ}{R:Census V}
open Album Blaze
namespace Tale
open Lagger Binding Turbin Primitives.TwoWave Primitives.TwoWave.RealSlice AllOrder.Ker
variable (F:Forest S.ratio) (T:S.Choices) {b:Clip} {P:PathData G}{O:ChartRatio G} (W:Layout G)(T₀:Finset Age)
local notation "E"=> Apex c G
local notation "I"=> Leaf c V
local notation "Z"=> Precision.Key F G
local notation "Y"=> Poll.Body Z
local notation "L"=>E × rule V c
local notation "D"=>fieldDir G c 1
variable (U : Tale R G) (X: Tale.Decision U) {σ G' θ :ℝ} (A:Before G σ G' S.patch.J S.kernel (j+3))(ρ:fieldDir G c 1→ AxisChart G F) (h : Legal T₀ W) (K : Kernel S b P O)
variable (o:V→Site c) (φ:V→Site S.ratio.count)
local notation "Z'"=> U.mood X (assign S φ o) W T₀
local notation "Mℓ"=> viewed R o
set_option quotPrecheck false
local notation "W'"=> U.lag
variable [Fintype V]
local notation "Ξ"=> orbit (G:=G) F ρ
local notation "ψ"=> colorful (fderiv ℝ (Ξ) 0)
variable (s:Senses R)(t:Places s c)
variable (x:Apex c G) (y:Poll.Body (Precision.Key F G))
local notation "L'"=>activity F U X ρ φ
local notation "ν"=> translated K F (tint G _ x)
variable (hL : P.Bounds b σ G' θ)(hk:Bid.Larger (G:=G) S)(he:A.Service F b P ρ) (hp:U.Allows a C)(ha:0<a)
local notation "Φ"=> ContinuousLinearMap.inr ℝ (Apex c G) (rule V c)
local notation "G''"=> Wall.pole Φ Y
local notation "t₀"=> ((x,(0:rule V c)),y)
local notation "λ₀"=> Wall.polar G'' t₀
local notation "U'"=>U.markℓ X (assign S φ o)
open Comparison.RG02.Order.Join
local notation "Ωℓ"=>ν (weld Z y)
local notation "P'"=> geometric K F T Z'
local notation "Λ'"=> markFn S F (Z')
local notation "m'"=> boom U
local notation "startup★"=> Laplace.startup F O T P b A hk hL he K.ratio
local notation "w0"=> Floe.augment F W T₀ startup★ h
local notation "u₀"=> Floe.books F W T₀ startup★
local notation "S₀"=>Comparison.RG02.Assembly.affine m' Λ' P' Ωℓ
local notation "f'"=> Comparison.RG02.Assembly.curve m' Λ' Ωℓ
local notation "θ'" => Orbit.referendum F x (Mℓ)
include hp ha he h hL hk
lemma parity (k:ℕ): let r₀:= ν (weld Z y); markLetter m' Λ' s r₀ k= Complex.ofReal (Radial.jet (posed S F (U' s)) (m' s+k) ((Binding.gaugeL F) (ψ (x,y)))):=by
 intro r'; unfold markLetter; let m:ℕ:=m' s+k; let g:=U' s; let f:=posed S F g
 let Hv:= Comparison.RG02.Assembly.jet (Complex.ofRealCLM ∘ f) m (ν (weld Z y)); change Hv = _; have ht:ContDiffAt ℝ m f 0:= ( (joint_receipt S F ((quartile U s (assign S φ o) hp ha X).zeroAt)).smooth).of_le le_top; unfold Hv; rw [← jet_apply_left Complex.ofRealCLM f m ht,unity F K A ρ he]; rfl
lemma pension (r:ℕ) : season W' (series R r f')= series R r (θ' L' y):= by
 rw [jetting]; apply congr_arg; apply bills_equal
 intro k i; let L₀ := (ν (weld Z y)); let f₁:= λ₀ (L' k); rw [ask]; unfold cell Orbit.referendum Wall.orientation Comparison.RG02.Assembly.curve; simp_rw [PowerSeries.coeff_mk];
 have he0:wall Mℓ (f₁)=∑ s:Senses R, (if dues (lag U) s.val ≤ k then ((Radial.jet (posed S F (U' s)) (k-(essence s).card) ((Binding.gaugeL F) (ψ (x,y)))) • Poly.send s.val 1) else 0):= by
    unfold f₁ activity; rw [Wall.finite_path,pours (Mℓ) (univ:Finset (Senses R)) (fun s=> λ₀ (∑ t:Places s c, life F U X ρ φ s t k)) (fun l _=> Wall.granted _ _ _ (AllOrder.Fire.Rank.read (n:=k) (?_)))]; exact Finset.sum_congr rfl fun l _=> Tale.label ..; exact AllOrder.Fire.Rank.sum fun j _=> life_rank .. -- implicit params order
 change (if dues (U.lag) i≤ k then (Multi.lit R _).part i else 0)= _; rw [he0,Poly.part_sum]; let t(s:Senses R):=if dues W' s.val ≤ k then ((Radial.jet (posed S F (U' s)) (k-(essence s).card) ((Binding.gaugeL F) (ψ (x,y)))) • Poly.send s.val (1:ℂ)) else 0
 have hz0 (s:Senses R)(hs:s.val≠i):(t s).part i=0:= by
    unfold t; split; · change (↑(_ : ℝ):ℂ)* (Poly.send _ _).part i=_; rw [Poly.part_send,if_neg hs.symm,mul_zero]
    rfl
 by_cases ht:i.val.Nonempty
 · let s:Senses R:=⟨i,ht⟩; rw [Finset.sum_eq_single s]; swap
   · intro l _ h; exact hz0 l (fun H=> h (Subtype.ext H))
   swap; · simp
   rw [show (Multi.lit R _).part i = markLetter m' Λ' s L₀ (k-dues W' i) from part_lit _ s]; rw [parity F W T₀ U X A ρ h K o φ s x y hL hk he hp ha]; change _=(t s).part i; unfold t; change _=(if dues W' i ≤ k then (_:ℝ) • Poly.send i 1 else 0).part i; split
   next he=>
      let c:= Radial.jet (posed S F (U' s)) (k-(essence s).card) ((Binding.gaugeL F) (ψ (x,y))); have hh:= hence U s; change dues W' i= _ at hh; rw [show m' s+(k-dues W' i)=k-(essence s).card from (by omega)]; change ↑c=(↑c:ℂ)*(Poly.send i 1).part i; simp
   exact (Poly.part_nil ..).symm
 rw [show (Multi.lit R _).part i=0 from ?_]; simp_rw [ite_self]; symm; exact Finset.sum_eq_zero fun j _=> hz0 j (fun h=> ht (congr_arg Subtype.val h ▸ j.property))
 have he:i=R.quiet:=Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp ht); rw [he]; exact part_lit_quiet _
local notation "w'"=> (Orbit.husk (ι:=I) u₀)
local notation "H'"=> w'+L'
lemma birth : AllOrder.Fire.Clear w' ∧ AllOrder.Fire.Clear L':= by
 constructor ; ·
    let M := (Tilt.walkB : (L × Y)→L[ℝ] (E× Y)); intro k; unfold Orbit.husk
    have hv:AllOrder.Fire.Rank _ (k+2) (fun x => u₀ k (M x)):= ((show AllOrder.Fire.Rank _ (k+2) (u₀ k) from (by unfold Floe.books; exact AllOrder.Fire.impulse_rank ..)).lead M)
    exact hv.read
 intro i; exact (licensed ..|>.read)
lemma recorded (r:ℕ) : season W' (series R r (S₀))=series R r (θ' H' y):= by
 let A':ℕ→ℝ:=fun n=>u₀ n (x,y)
 have hz(k:ℕ):(λ₀ (w' k)) = (fun _=> A' k):= funext fun z=>by
    simp [Orbit.husk,Wall.polar,Wall.pole]; rfl
 have hS:= birth F T W T₀ U X A ρ h K φ hL hk he hp ha; let u:= (θ' w' y); have hv: u=realCurve R A' := by unfold u Orbit.referendum Wall.orientation; ext1 i; rw [PowerSeries.coeff_mk, realCoeff, hz, Turbin.sky_c]; rfl
 rw [Comparison.RG02.Assembly.affine,map_add,seasons,pension F W T₀ U X A ρ h K o φ x y hL hk he hp ha]; rw [show vacuumLetter P' Ωℓ=A' from funext fun k=> pulse F T W T₀ K Z' h rfl A ρ hL hk he x y k, jetting,Orbit.subliminal,← hv,← map_add]; apply congr_arg; ext1 i; unfold Orbit.referendum Wall.orientation; rw [map_add,PowerSeries.coeff_mk,PowerSeries.coeff_mk,PowerSeries.coeff_mk, Pi.add_apply, ← Wall.pre_a]; exact (pours_a Mℓ (Wall.granted _ _ _ (hS.1 i)) (Wall.granted _ _ _ (hS.2 i))).symm
lemma zenith (r:ℕ): let A':= Response.connected (castle (w0).hard (w0).quiet (w0).pay.steer) volume (X:= (Apex c G × rule V c)); season W' (logMarked (Fk K F T Z' ((tint G _) x) r))=series R r (Orbit.bedrock Mℓ x (A' H'- A' w')):= by intro A'; have hx:= (birth F T W T₀ U X A ρ h K φ hL hk he hp ha); refine Orbit.charcoal F T W T₀ K Z' h rfl A ρ hL hk he x Mℓ W' H' ((birth F T W T₀ U X A ρ h K φ hL hk he hp ha).1.add hx.2) ?_ (fun y=>recorded F T W T₀ U X A ρ h K o φ x y hL hk he hp ha r) hx.1; rw [Pi.add_apply, starts]; rw [show w' 0= 0 from funext (fun x=> by unfold Orbit.husk; rw [show u₀ 0= 0 from win0 _]; rfl),zero_add]
end Tale
end YM.Qlocal.Quipu.Sonnet
