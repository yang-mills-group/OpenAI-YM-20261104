import YM.SignedWilsonExpansion.Both
import YM.FVA2.Lambda.Scrap
namespace YM.SignedWilsonExpansion.Radial
/-! Six orientations for exact degree-four spherical quadrature on the actual bill. Need no untested vertex kernel. This Fubini justification uses the *marked* Taylor projection's integrable high-cutoff cost. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows AxisChoice
open Gaussian
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}(p:FourP)
local notation "Z" => Momentum.sq
local notation "Ω" => AxisChoice.disk
local notation "μ" => covMeasure Axis
local notation "F" => FourP
def c : ℝ:= Real.sqrt 2 / 2
lemma c2 : c^2=(1/2:ℝ):= by unfold c; rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]; norm_num
def twist (j:Fin 6)(k:F) : F:= ![
  (![k 0,k 1,k 2,k 3]:F), (![k 1,k 0,k 3,k 2]:F),
  ![c*(-k 0+k 1),c*(k 1+k 0),c*(k 2+k 3),c*(-k 3+k 2)],
  ![c*(-k 0-k 1),c*(k 1-k 0),c*(k 2-k 3),c*(-k 3-k 2)],
  ![c*(-k 0-k 2),c*(k 1+k 3),c*(k 2-k 0),c*(-k 3+k 1)],
  ![c*(-k 0+k 2),c*(k 1-k 3),c*(k 2+k 0),c*(-k 3-k 1)]
 ] j
@[local simp] lemma u00 (k:F): twist 0 k 0=k 0:= rfl
@[local simp] lemma u01 (k:F): twist 0 k 1=k 1:= rfl
@[local simp] lemma u02 (k:F): twist 0 k 2=k 2:= rfl
@[local simp] lemma u03 (k:F): twist 0 k 3=k 3:= rfl
@[local simp] lemma u10 (k:F): twist 1 k 0=k 1:= rfl
@[local simp] lemma u11 (k:F): twist 1 k 1=k 0:= rfl
@[local simp] lemma u12 (k:F): twist 1 k 2=k 3:= rfl
@[local simp] lemma u13 (k:F): twist 1 k 3=k 2:= rfl
@[local simp] lemma u20 (k:F): twist 2 k 0=c*(-k 0+k 1):= rfl
@[local simp] lemma u21 (k:F): twist 2 k 1=c*(k 1+k 0):= rfl
@[local simp] lemma u22 (k:F): twist 2 k 2=c*(k 2+k 3):= rfl
@[local simp] lemma u23 (k:F): twist 2 k 3=c*(-k 3+k 2):= rfl
@[local simp] lemma u30 (k:F): twist 3 k 0=c*(-k 0-k 1):= rfl
@[local simp] lemma u31 (k:F): twist 3 k 1=c*(k 1-k 0):= rfl
@[local simp] lemma u32 (k:F): twist 3 k 2=c*(k 2-k 3):= rfl
@[local simp] lemma u33 (k:F): twist 3 k 3=c*(-k 3-k 2):= rfl
@[local simp] lemma u40 (k:F): twist 4 k 0=c*(-k 0-k 2):= rfl
@[local simp] lemma u41 (k:F): twist 4 k 1=c*(k 1+k 3):= rfl
@[local simp] lemma u42 (k:F): twist 4 k 2=c*(k 2-k 0):= rfl
@[local simp] lemma u43 (k:F): twist 4 k 3=c*(-k 3+k 1):= rfl
@[local simp] lemma u50 (k:F): twist 5 k 0=c*(-k 0+k 2):= rfl
@[local simp] lemma u51 (k:F): twist 5 k 1=c*(k 1-k 3):= rfl
@[local simp] lemma u52 (k:F): twist 5 k 2=c*(k 2+k 0):= rfl
@[local simp] lemma u53 (k:F): twist 5 k 3=c*(-k 3-k 1):= rfl
theorem D6 (i:Fin 6): i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5:= (by decide:∀ i:Fin 6,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5) i
theorem D4 (i:Axis): i=0 ∨ i=1 ∨ i=2 ∨ i=3:= (by decide: ∀ i:Axis,i=0 ∨ i=1 ∨ i=2 ∨ i=3) i
lemma invol (j:Fin 6)(k:F): twist j (twist j k)=k:= by funext i; rcases D4 i with rfl|rfl|rfl|rfl <;> rcases D6 j with rfl|rfl|rfl|rfl|rfl|rfl <;> first| rfl| (simp; ring_nf; rw [c2]; ring)
def LE (j:Fin 6): F≃L[ℝ] F:= (LinearEquiv.toContinuousLinearEquiv ({
    toFun:= twist j, invFun:= twist j, left_inv:= invol j, right_inv:= invol j
    map_add':=fun x y=> by funext i; rcases D4 i with rfl|rfl|rfl|rfl <;> rcases D6 j with rfl|rfl|rfl|rfl|rfl|rfl <;> simp <;> ring
    map_smul':=fun t x=> by funext i; rcases D4 i with rfl|rfl|rfl|rfl <;> rcases D6 j with rfl|rfl|rfl|rfl|rfl|rfl <;> simp <;> ring
 }: F≃ₗ[ℝ]F))
lemma tw (j:Fin 6): ⇑(LE j)=twist j:= rfl
lemma money (j:Fin 6): MeasurePreserving (twist j) μ μ := by
    let U:= LE j; let m:F→ₗ[ℝ] F:= U.toLinearEquiv.toLinearMap
    have hx(t:F): m (m t)=t:= invol j t; have he: m*m=1:= LinearMap.ext hx
    have hm : LinearMap.det m * LinearMap.det m=1:= by rw [ ← map_mul, he,map_one ]
    have hz : |LinearMap.det m| =1:= by
       obtain he:= congr_arg abs hm; rw [abs_mul,abs_one] at he; have h:= abs_nonneg (LinearMap.det m); nlinarith
    refine ⟨ U.continuous.measurable,?_ ⟩; change Measure.map m μ=_; rw [ Measure.map_linearMap_addHaar_eq_smul_addHaar μ ( show LinearMap.det m ≠ 0 from fun h=>by rw [h,mul_zero] at hm; norm_num at hm ), abs_inv, hz ]; simp
macro "reduce_twist" : tactic => `(tactic| simp [ Momentum.sq,AxisChoice.disk, show Finset.univ (α:=Axis)={0,1,2,3} from rfl ])
lemma same (j:Fin 6): Z (twist j p)=Z p:= by rcases D6 j with rfl|rfl|rfl|rfl|rfl|rfl <;> first| (solve|reduce_twist)|(reduce_twist; ring_nf <;> (rw [c2]; ring))
lemma power₄ : c^4=(1/4:ℝ):= by rw [show c^4=(c^2)^2 from by ring,c2]; ring
lemma price1 : ∑ i:Fin 6, Ω (twist i p)= 3*Z p:= by
    rw [show Finset.univ (α:=Fin 6)= {0,1,2,3,4,5} from rfl]; reduce_twist; ring_nf; rw [ c2 ]; ring
set_option maxHeartbeats 800000 in
lemma price2 : ∑ i:Fin 6, Ω (twist i p)^2 =2*Z p^2:= by
    rw [show Finset.univ (α:=Fin 6)= {0,1,2,3,4,5} from rfl]; reduce_twist; ring_nf; simp only [ c2,power₄ ]; ring
def leader (h:ℝ→ℝ)(p:ℝ):ℝ:=80*p^2*h p-16*(h p)^2*p^4
lemma count_salary (h:ℝ→ℝ) : (∑ i: Fin 6,salary h (Z (twist i p)) (Ω (twist i p)))=6* Radial.leader h (Z p):= by
    simp_rw [ same ]; let W := h (Z p); let L:= Z p
    have he(i:ℝ): salary h L i =128*L^2*W- (96*L*W+96*(W*L)^2*L)*i + (96*(W*L)^2)*i^2 := by unfold salary W; ring
    dsimp only [L] at he; simp_rw [ he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,price1 p,price2 p]; unfold Radial.leader W; simp only [ Finset.sum_const, Finset.card_univ, Fintype.card_fin ]; ring

abbrev fee (G:Gauge)(t:ℝ)(k:F):ℂ:= ↑( ( G.casimir * Shells.hot t (Z k) *2 * Radial.leader (amp t) (Z k) ) )
lemma stroll (t:ℝ) : ∑ i: Fin 6,slopeQ (twist i p) G t=6*fee G t p:= by
    obtain he:= count_salary p (amp t); simp_rw [ same ] at he
    simp_rw [ slopeQ,AxisChoice.true_price,same,fee,← Complex.ofReal_sum,← Finset.mul_sum,he ]; push_cast; ring
variable (t:ℝ)
variable {B : Land.Booked (Press.portDeck G)}(M:Land.MS_Data G B)(simple:G.Simple) (A:G.ColorIndex)
include M simple A
lemma radial : (∫ k, slopeQ k G t∂μ) = ∫ k, fee G t k∂μ := by
    let D(i: Fin 6):F→ℂ:=fun k=> slopeQ (twist i k) G t
    have hp(i:Fin 6): MeasurableEmbedding (twist i):= by rw [← tw]; exact (LE i).toHomeomorph.measurableEmbedding
    have ht(i:Fin 6) : Integrable (D i) μ:= ( ( money i ).integrable_comp_emb (hp i) |>.mpr ( paid_price t M simple A ) )
    have hz(i): (∫ k,D i k∂μ)=(∫ k,slopeQ k G t∂μ):=(money i).integral_comp (hp i) (fun k=> slopeQ k G t)
    have he(p:F): ∑ i:Fin 6,D i p= 6* fee G t p:= stroll p t; let g:=fee G t
    have H:=( integral_finsetSum Finset.univ ( f:=D ) ( «μ»:=μ ) (fun i _=> ht i) ); simp_rw [he,hz] at H; rw [integral_const_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin] at H; linear_combination (-1/6:ℂ)*H
omit M simple A

local notation "E" => Real.exp
lemma capital (p:ℝ): amp 0 p*p^2=(1-(1+p)*E (-p))/2:= by
    unfold amp TreeLine.gain desk; simp only [ Real.exp_zero, one_pow ]; rw [ ← intervalIntegral.integral_mul_const ]; let f(t:ℝ):= -(1+t*p)* E (-(t*p)) / 2
    have hf(t:ℝ): HasDerivAt f ( src (t,p) * p^2 ) t:= by
        let h:= ( hasDerivAt_id' t ).mul_const p; convert! ((( (( h.const_add 1 ).neg).fun_mul (h.neg.exp) ).div_const 2 )) using 1; unfold src; simp only [Pi.neg_apply]; ring
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=> hf i) ( show IntervalIntegrable (fun x:ℝ=> src (x,p)*p^2 ) volume 0 1 from ( Continuous.intervalIntegrable ( by unfold src; fun_prop ) 0 1 )) ]; unfold f; simp; ring
-- radial price reduces to convergent finite gaussian moments.
local notation "κ" => ( fun _:Axis=>(0:ℕ) )
open Lathe (γ)
def Pin (p:F):ℝ:= rock κ 2 2 p +8*rock κ 1 1 p+2*rock κ 2 1 p-9*rock κ 0 0 p+8*rock κ 1 0 p+rock κ 2 0 p
lemma spend0 : fee G 0 p = ( (-8:ℂ)*( G.casimir:ℂ ) ) * (Pin p:ℂ):= by
    let H:=Z p; let q:= E (-H); have hz: Shells.hot 0 H=q:= by simp [Shells.hot,q]
    have hm(v:ℝ): γ v p= E (-(1+v)*H):= rfl
    have he₂: γ 2 p=q^3:= by rw [hm, show -(1+2:ℝ)*H= -H + -H + -H from (by ring), Real.exp_add,Real.exp_add]; unfold q; ring
    have he₁: γ 1 p=q^2:= by rw [hm, show -(1+1:ℝ)*H= -H + -H from (by ring), Real.exp_add]; unfold q; ring
    have he₀: γ 0 p=q:= by rw [hm]; simp [q]
    have ht: Pin p= H^2*q^3+8*H*q^2+2*H*q^3-9*q+8*q^2+q^3:= by unfold Pin rock; rw [he₁,he₂,he₀]; simp only [ γ_norm ]; unfold H; ring
    have hv: 2*q*Radial.leader (amp 0) H= -8* Pin p := by
        rw [ht]; have h : Radial.leader (amp 0) H=80*(amp 0 H*H^2)-16*( amp 0 H*H^2)^2:= by unfold Radial.leader; ring; -- syntax
        rw [h, capital ]; unfold q; ring
    unfold fee; change ((  G.casimir*Shells.hot 0 H*2*Radial.leader (amp 0) H:ℝ ):ℂ) = _; rw [hz]; push_cast; linear_combination (norm:=(push_cast; ring)) (G.casimir:ℂ) * congr_arg ((↑):ℝ→ℂ) hv

lemma clockPin : (∫ k, Pin k∂μ)= (-14/3:ℝ)*b₀:=by
    let x:= rock κ 2 2; let y:= fun k=> 8* rock κ 1 1 k; let z:=fun k=>2* rock κ 2 1 k
    let a:= fun k=>9*rock κ 0 0 k; let b:=fun k=>8*rock κ 1 0 k; let e:=rock κ 2 0
    have f (u:ℝ)(h:0≤u)(n:ℕ): Integrable (rock κ u n) μ:= gram h _ _
    have hx:Integrable x μ:= f 2 (by norm_num) 2
    have hy:Integrable y μ:= ( f 1 (by norm_num) 1 ).const_mul (8:ℝ)
    have hz:Integrable z μ:= ( f 2 (by norm_num) 1 ).const_mul (2:ℝ)
    have ha:Integrable a μ:= ( f 0 (by norm_num) 0 ).const_mul _
    have hb:Integrable b μ:= ( f 1 (by norm_num) 0 ).const_mul _
    have he:Integrable e μ:= f 2 (by norm_num) 0
    change (∫ k,(x+y+z-a+b+e) k∂μ)=_; rw [ integral_add' ( ( ( ( hx.add hy ).add hz ).sub ha ).add hb ) he, integral_add' ((( hx.add hy ).add hz ).sub ha) hb, integral_sub' (( hx.add hy ).add hz) ha, integral_add' (hx.add hy) hz, integral_add' hx hy ]
    unfold x y z a b e
    simp_rw [integral_const_mul]; change tide κ 2 2 + 8* tide κ 1 1+2*tide κ 2 1-9*tide κ 0 0 + 8*tide κ 1 0+tide κ 2 0=_
    simp (disch:=norm_num) only [show (2:ℕ)=1+1 from rfl,show (1:ℕ)=Nat.succ 0 from rfl,Gaussian.jump (by norm_num : 0≤(2:ℝ)) κ 1, Gaussian.jump (by norm_num : 0≤(2:ℝ)) κ 0, Gaussian.jump (by norm_num : 0≤(1:ℝ)) κ 0, basis₀,Szero ]; ring
-- radial high projected mark
include M simple A
local notation "v" => Energy.called 1 2 G
abbrev trigger (M: Land.MS_Data G B) (S:Clock ℝ) :=
   (spaceD G).recu 0 (1:ℂ) (Archive 4 M.bulk) ( MarkRows.packet M (Energy.called 1 2 G) ) 2 S
lemma point_s (t:ℝ) : probeAct A (trigger M (t,0))= ↑( ((-8:ℝ)*G.casimir) * ( -14/3*b₀ ) ) := by
    rw [ trigger, paceAct M simple A (t,0), radial 0 M simple A ]; simp_rw [spend0]; rw [ integral_const_mul, integral_complex_ofReal, clockPin ]; push_cast; ring

end
end YM.SignedWilsonExpansion.Radial
