import YM.RegulatorIR.Primitives.Faber
import YM.RegulatorIR.Quadratic.Plains

/-!
# Joint step higher-vertex alignment
Lift all Haar/bond costs to an independently checked primitive grove. No
normalization from marked reports. The canopy proof is only for germ of
predictor off arbitrary top: ZERO assertions at actual saddle. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Geometry.Field Chart Gauge RG Orb Laplace Tree Forest Step
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {I J X:Type}{G:Gauge}{f c:Side}
variable (S:StepData c f)(F:Forest S.ratio)(N:Scale)(Z:S.patch.Branches S.kernel G)
abbrev Branchix:= Edge Cover⊕Edge Cover -- left Haar right bond

def barkN : Branchix→ℕ := Sum.elim (fun _=>0) (fun _=>2)
def dry : Branchix→ℝ := Sum.elim (fun _=>1) (fun _=>-1)
def prism : Branchix→Micro (KFoot G) := Sum.elim (carnal S F) (opi S N)

-- arc genuine on every chosen Step.Coordinates

def Sphere (T:Branchix→Orders (KFoot G)):Prop:= ∀ i,Lab (barkN i) (dry i) (prism S F N i) (T i)
include Z
lemma gauss : ∃ T : Branchix→Orders (KFoot G), Sphere S F N T:=by
 have hp (i:Branchix) : Nonempty (Run (prism S F N (G:=G) i)) := by cases i <;> first| exact rooted .. | exact locally S Z N _
 choose T h using fun i=> (hp i).some.issues (dry i) (barkN i);exact ⟨_,h⟩

variable {l R P:ℝ}(h:Even f.val)(hi:l*f.val=P)(he:Even c.val)(hv:R*c.val=P)
local notation "F0" => Carto G l P h hi
local notation "F1" => Carto G R P he hv
local notation "F2" => Step.combine F0 F1
lemma cosmos {T:Branchix→Orders (KFoot G)}(HE:Sphere S F N T): Flight (prism S F N) T barkN dry F2 (unite (posMarch h) (posMarch he)):=by
 refine ⟨?_,HE,?_,?_,?_,?_⟩
 · intro d i w x; cases i <;> rename_i j
   · exact carnal_o S F h hi he hv d j w x
   exact footing S Z N h he hi hv d j w x
 · rintro (i|i); exact Nat.zero_le _; exact le_rfl
 · rintro d (i|i) <;> rfl
 · rintro d (i|i)<;>rfl
 rintro (i|i) x <;> first| exact carnal_z S F G i x | exact opi_zero S Z N i x

variable (w: Horizon G c)(y : Meadow G (Wind F))
-- background script. Use both species in joint chart. foresh even projection. Shift compatible t.
local notation "T" => joins S F y w
local notation "Z0" => bridge F2 (joins S F y w)
omit Z in
lemma fee_core (x:Wind F) (r:ℝ) : flank (prism S F N (Sum.inl (Geometry.position x.val))) Z0 r=entry G (r • y x):=by
 let v:= r • Z0;let i:= Geometry.position x.val
 change carnal S F i r v=_; unfold carnal
 rw [show resolve f i=x.val from Geometry.positioned _, if_neg x.property]
 apply congr_arg; ext1 j
 change r*(Geometry.shade f i * (injectX F y (resolve f i)) j)= _
 rw [show Geometry.shade f i=1 from Geometry.dawning _, show resolve f i=x.val from Geometry.positioned _,inject_access,one_mul];rfl

omit Z in
lemma fee_far (x:Field.Knot F) : flank (prism S F N (Sum.inl (Geometry.position x.val))) Z0=fun _=>0:=by ext1 r; unfold flank prism;change carnal S F (Geometry.position x.val) r (r • Z0)=0; rw [carnal,Geometry.positioned,if_pos x.property]

omit Z in
lemma opi_chill (t:ℝ)(e:OEdge c): flank (prism S F N (Sum.inr (Geometry.position e))) Z0 t = N.beta t * S.kernel.penalty * G.price (climb (t • w) e*(predictor S (climb (injectX F (t • y))) e)⁻¹):=by
 let V:=t • Z0; let A:=injectX F (t • y); let i:= Geometry.position e
 change N.beta t* _ * G.price (win G (V ∘ Sum.inr) i * (pond S.patch S.kernel (win G (V ∘ Sum.inl)) i)⁻¹)= _
 have ha : V ∘ Sum.inr=bridge F1 (paper G c (t • w)):=by
    ext1 p; rw [map_smul];change t*((F1).orient p * paper G c w ((F1).orbit p))= _*(t*_); ring
 have hh : V∘ Sum.inl=bridge F0 (paper G f A):=by
    ext1 p; unfold A; rw [map_smul,map_smul];change t*((F0).orient p*paper G f (injectX F y) ((F0).orbit p))=_*(t*_);ring
 rw [ha,hh,win_o h hi A,win_o he hv,Function.comp_apply,river (S:=S), Geometry.position_edge]; rw [show orbLift (climb (t • w)) e.val=_ from lift_at ..]; rfl
include Z
lemma opi_span :
 let z:=(y,(1:ℝ),w); inscription (priceMap (nextO S F N)) z= ∑ e:OEdge c, tale (flank (prism S F N (Sum.inr (Geometry.position e))) Z0):=by
 let f (e:OEdge c):= flank (prism S F N (Sum.inr (Geometry.position e))) Z0
 intro z;rw [← lore (nextF N S Z).smooth]
 have hp (u:OEdge c): ContDiffAt ℝ ∞ (f u) 0:= (locally S Z N (Geometry.position u)).some.smooth_v _
 change tale _=∑ u,tale (f u); rw [← tale_sum _ _ (fun i _=> hp i)]; apply congr_arg;ext t; rw [Finset.sum_apply]; simp_rw [f, opi_chill]; change N.beta (t*1)* Geometry.bond S _ _=_
 rw [mul_one]; unfold bond trouble; rw [← mul_assoc, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _
 rw [chart_commute]; rfl

omit Z in
lemma fee_span : psyche (Wind F) G y=∑ x: OEdge f, flank (prism S F N (.inl (Geometry.position x))) Z0:=by
 let L(x: OEdge f):= flank (prism S F N (.inl (Geometry.position x))) Z0
 ext1 t; rw [Finset.sum_apply]
 change _ = ∑ i,L i t
 let g:= Equiv.sumCompl (Field.branch F); rw [← g.sum_comp (fun k=>L k t),Fintype.sum_sum_type]
 simp_rw [show ∀ i:Field.Knot F,L (g (Sum.inl i)) t=0 from fun i=> congr_fun (fee_far S F N h hi he hv w y i) t, Finset.sum_const_zero,zero_add]
 exact Finset.sum_congr rfl fun i _=> (fee_core S F N h hi he hv w y i t).symm

-- higher log and meter propagation
open PowerSeries
variable {W: Branchix→Orders (KFoot G)}
variable (Y:GridStep (Carto G l P h hi) (Carto G R P he hv))
variable (H:Sphere S F N W) (C:Y.addon= many W)
include H C
lemma garden : flavor 2 (joins S F y w) (ScrollA Y)=tale (psyche (Wind F) G y)+logread (priceMap (nextO S F N)) (y,1,w) :=by
 have V:= cosmos S F N Z h hi he hv H
 
 have hh: ScrollA Y= Flight.foldO F2 W:=by ext1 i; ext1 j; unfold ScrollA;rw [C];rfl
 ext1 i; rw [hh,map_add]
 cases Nat.eq_zero_or_pos i with
 | inl hi'=> rw [hi',V.zero_transit,logbase,tale_base,psyche_zero,add_zero]
 | inr ht=>
    rw [V.transit T ht,Fintype.sum_sum_type]; apply congr_arg₂ (·+·)
    · rw [fee_span S F N h hi he hv w y, tale_sum]
      · rw [map_sum]; apply Finset.sum_congr rfl; intro j _; change 1*_=_;rw [one_mul];rfl
      intro j _; exact (rooted (G:=G) S F _).some.smooth_v _
    rw [logread,coeff_mk, Series.Radial.layers, if_neg ht.ne',add_zero]
    have hh:=opi_span S F N Z h hi he hv w y; change inscription _ _= _ at hh; replace hh:=congr_arg (PowerSeries.coeff (i+2)) hh; rw [inscription,map_sum,coeff_mk] at hh
    rw [hh,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro v _; change (-1:ℝ)*_= _;rw [neg_one_mul];rfl
lemma debut : Launch S F N Y:=by
 have V:= cosmos S F N Z h hi he hv H;have hh :ScrollA Y=Flight.foldO F2 W:=by ext1 i;ext1 j; unfold ScrollA;rw [C];rfl
 refine ⟨fun w y=>?_,hh.symm ▸ V.printed, hh.symm ▸ V.format⟩
 let x:Meadow G (Wind F) × ℝ × Horizon G c:=(y,1,w); let d:= psyche (Wind F) G y; let F':=nextO S F (G:=G) N
 rw [prints, garden S F N Z h hi he hv w y Y H C,timble_exp (show _= _ from (tale_base (f:=d)).trans (psyche_zero ..)) (logbase ..), next_color N S Z];
 rw [show inscription _ _= PowerSeries.C (morning G (Wind F))*expo (tale d) from ?_]; simp only [map_mul];ring
 let K:=aura (1:Hook G (Wind F) (OEdge c))
 have hs: ContDiffAt ℝ ∞ K 0:= contDiffAt_const.mul (((Chart.Ratio.jacobian_smooth (traySpec G)).of_le le_top).comp (f:=Prod.fst) (0: Angle (Wind F) (OEdge c) G) contDiffAt_fst)
 change inscription K x= _;rw [← lore hs x]
 rw [show (fun t:ℝ=>K (t • x))= fun t:ℝ=> jacobian (tray G) (t • y) from funext fun i=>one_mul _]; exact spirit ..
end YM.RegulatorIR.Prim
