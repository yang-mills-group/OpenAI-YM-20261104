import YM.RegulatorIR.Profiles.Staple
import YM.Next.WARD_BIN.Coin

/-!
# Top input stencil styling & geometry convention

Uses real coordinate axes, sup distance to support. Includes Laurent
shifting, test argument pull, $\epsilon^{4-h}$ factors, bounded test
with declared finite differentiability. `Feeds.scale` is Wilson trajectory
written in common coupling t, with branch conventions in binding. Here
use continuous positive extension realizing formal g_i=t α_i(t) for tests.
No reexpression asserted across different prescriptions. Derivative costs
paid later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Labels Source Bid
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I:Type}{q u b p a i e k d:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{J D:Choice M}
variable {F:Labels.Frame G d}
section
-- coupling g=t α(t) not required to specify testing coefficient at t≠0 real, only algebra identity at common finite regulator. positive continuation global on line for compact Haar extension.
structure Feeds where
 dine : ℝ→ℝ
 origin : dine 0=1
 continuous : Continuous dine
 positive : ∀ t,0<dine t
 smooth : ContDiffAt ℝ ∞ dine 0
namespace Feeds
def scale (T:Feeds):= creator T.dine T.continuous.measurable T.smooth T.origin
def coupling (T:Feeds)(t) :=t*T.dine t
lemma chart (S:Feeds) t: Real.exp (-((S.coupling t)⁻¹^2))=Real.exp (-(S.scale.beta t/t^2)):=by unfold scale Binding.creator coupling;dsimp only; rw [mul_inv,mul_pow];simp only [div_eq_mul_inv,inv_pow]; rw [mul_comm]
-- definitions refer S unless consuming Budget
lemma leans (S:Feeds)(b:ℕ)(j:F.Index){t:ℝ}(h:t≠ 0)(hb:(F.grades j).2 ≤ b): t^b * (S.coupling t)⁻¹^(F.grades j).2=t^(b-(F.grades j).2)*(S.dine t)⁻¹^(F.grades j).2:=by
 let s:=(F.grades j).2;rw [coupling,mul_inv,mul_pow]; nth_rw 1 [← Nat.sub_add_cancel hb]; change t^(b-s+s)*((t⁻¹)^s*_)=_;rw [pow_add,← mul_assoc, mul_assoc (t^(b-s)), ← mul_pow,mul_inv_cancel₀ h,one_pow,mul_one]
lemma admits {α:ℝ→ℝ}(h:Continuous α)(hs:ContDiffAt ℝ ∞ α 0)(hv:α 0=1) : ∃ S:Feeds,S.dine =ᶠ[𝓝 0] α:=by
 let D (t:ℝ):= max (1/2) (α t);have hh:D=ᶠ[𝓝 0] α:=by
    filter_upwards [(show Tendsto α _ _ from h.tendsto 0).eventually (lt_mem_nhds (show (1/2:ℝ)<α 0 by simp [hv]; norm_num))] with x hx;exact max_eq_right (le_of_lt hx)
 exact ⟨⟨D,hh.eq_of_nhds.trans hv,continuous_const.max h,fun x=>lt_of_lt_of_le (show (0:ℝ)<1/2 by norm_num) (le_max_left ..),hs.congr_of_eventuallyEq hh⟩,hh⟩
end Feeds
end

-- joint actual ordered multi-index, dimension four. Use RG06/Bid for off-shell untest labels at horizon. Jets order ℓ from frame.
abbrev Stroke (F:Labels.Frame G d) := Σ i : F.Index, (Σ j: Fin (d+1-(F.grades i).1), {v:Fin j.val→ Axis // Monotone v}) -- full alphabet test matches need multiple nonexact derivative orders

instance : Fintype (Stroke F):= by unfold Stroke; infer_instance

def nu (i:Stroke F) := i.snd.fst.val
lemma combo (i:Stroke F) : (F.grades i.fst).1+nu i≤d:=by have h:= i.snd.fst.isLt; have hv:= F.bound i.1; unfold nu; omega
def finger (i:Stroke F) (j :Fin (nu i)) : Room:= Pi.single (i.snd.snd.val j) 1
def derivativeA (i:Stroke F)(φ: Room→ℝ)(r:Room):ℝ:= iteratedFDeriv ℝ (nu i) φ r (finger i)
def waveA (i:Stroke F)(ε:ℝ) (φ:Room→ℝ)(x:Room) := ε^(nu i) * derivativeA i φ x
lemma slope_ap (i:Stroke F)(ε:ℝ){φ:Room→ℝ}(h:ContDiff ℝ d φ): Continuous (waveA i ε φ):=by
 apply continuous_const.mul; exact (ContinuousMultilinearMap.apply ℝ (fun _:Fin (nu i)=>Room) ℝ (finger i)).continuous.comp (h.continuous_iteratedFDeriv (by exact_mod_cast (le_trans (Nat.le_add_left ..) (combo i))))
lemma in_ap (i:Stroke F)(ε:ℝ)(φ:Room→ℝ):support (waveA i ε φ)⊆ tsupport φ:=by
 intro y hy; apply support_iteratedFDeriv_subset (𝕜:=ℝ) (nu i); intro hz; apply hy; simp [waveA,derivativeA,hz]
structure PhaseTests (p:ℕ) where
 phi : Room→ℝ
 smooth : ContDiff ℝ p phi
 radius : ℝ
 priceR : 0≤radius
 uses : tsupport phi ⊆ Metric.closedBall 0 radius
structure Tap (F:Labels.Frame G d) where
 dollars : Stroke F→ℝ→ℝ
 priceU v: Continuous (dollars v)
 frames v: ContDiffAt ℝ ∞ (dollars v) 0
-- use global Feeds, preserve vertex stencil rank extension cutoff d on rotations. Tap dollars common-coefficient formal tuning input $N_{k,h}^{-1}$ to be provided. Can use varying per-w params.

section
-- sum over arbitrary table/v (vacuum unit tests etc). Admissible with Finset.
variable {V U:Portrait G}
lemma LocalStamp.plus (h:LocalStamp V d)(hp:LocalStamp U d): LocalStamp (V+U) d:=by
 obtain ⟨g,hg⟩:= h.crown; obtain ⟨p,hq⟩:=hp.crown
 refine { people:= ⟨h.people.cap.add hp.people.cap,fun t f x=> congr_arg₂ (·+·) (h.people.guise t f x) (hp.people.guise t f x),fun b F he hh hv hc=> (h.people.neat b F he hh hv hc).add (hp.people.neat b F he hh hv hc)⟩, order:=fun v=> Tested.bill_add (h.order v) (hp.order v), crown:=⟨g∪p,?_⟩ }
 intro t i j h; exact congr_arg₂ (·+·) (hg t i j (fun e hz he=> h e (Finset.mem_union_left p hz) (Finset.mem_union_left p he))) (hq t i j (fun e hz he=> h e (Finset.mem_union_right g hz) (Finset.mem_union_right g he)))
lemma stamps (s:Finset I)(A:I→Portrait G)(h:∀ i∈s,LocalStamp (A i) d): LocalStamp (∑ i∈s,A i) d:=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty]; exact { people:= ⟨continuous_const,fun _ _ _=>rfl,fun _ _ _ _ _ _=>contDiffAt_const⟩, crown:= ⟨∅,fun _ _ _ _=>rfl⟩, order:= fun _=> ⟨0,le_rfl,Eventually.of_forall fun _=>by change ‖(0:ℝ)‖ ≤ _;simp⟩ }
 | insert i s he ih=> rw [sum_insert he]; exact (h _ (mem_insert_self ..)).plus (ih (fun i hi=> h i (mem_insert_of_mem hi)))
end
namespace Aperture
variable (Ψ : PhaseTests d) (T:Tap F)(Z:SectionData F) {H:Hol G}(Q: Feeds)(ε:ℝ)
-- fees with d-r power restore X, so plotPT with offset d produces t series from atlas

def fees (i:Stroke F)(t:ℝ):ℝ:=t^(d-(F.grades i.1).2)*(Q.dine t)⁻¹^(F.grades i.1).2*T.dollars i t
lemma feesSmooth (i:Stroke F): ContDiffAt ℝ ∞ (fees T Q i) 0 := (((contDiffAt_id.pow _).mul ((Q.smooth.inv (by rw [Q.origin]; norm_num)).pow _)).mul (T.frames i))
lemma feesLive (i:Stroke F): Continuous (fees T Q i):= ((continuous_id.pow _).mul ((Q.continuous.inv₀ (fun x=>(Q.positive x).ne')).pow _)).mul (T.priceU i)

lemma pays (i:Stroke F) : Tested.Bill (d-(F.grades i.1).2) (fees T Q i):=by
 let g t:=(Q.dine t)⁻¹^(F.grades i.1).2*T.dollars i t;let a:=d-(F.grades i.1).2; let f(t:ℝ):= t^a
 have hp:Tested.Bill a f:=⟨1,zero_le_one,Tested.eventually_pos.mono fun _ hx=> by rw [Real.norm_eq_abs,abs_of_pos (pow_pos hx a),one_mul]⟩
 have hv: ContDiffAt ℝ ∞ g 0:= (((Q.smooth.inv (by rw [Q.origin];norm_num)).pow _).mul (T.frames i))
 have hh:= Tested.bill_mul hp (Script.actual hv).bounded; rw [Nat.add_zero] at hh; rw [show fees T Q i=fun t=> f t*g t from funext fun _=> mul_assoc ..]; exact hh

variable (x:Room)
def kindle (t:Cover)(i:Stroke F) (u:ℝ):ℝ:= (ε^4/ε^d * waveA i ε Ψ.phi (slide ε t-x)) * fees T Q i u
def flare (z:Cover)(i:Stroke F):Portrait G:=guardP (convey z (bare Z i.1)) (kindle Ψ T Q ε x z i)
def Intag (z:Cover): Portrait G:=∑ i : Stroke F,flare Ψ T Z Q ε x z i
def Testifies : Portrait G := ∑ z∈ Address.census ε Ψ.radius x, Intag Ψ T Z Q ε x z

variable (A:Z.Sound H)(B:Bid.pop Z)
include A B
lemma authenticated : LocalStamp (Testifies Ψ T Z Q ε x) d :=by
 apply stamps; intro z _;apply stamps; intro i _
 have hp : LocalStamp (convey z (bare Z i.1)) (F.grades i.1).2:= (authentically Z A B i.1).moves
 let f:= ε^4/ε^d*waveA i ε Ψ.phi (slide ε z-x); let S:=kindle Ψ T Q ε x z i
 have hv : Tested.Bill (d-(F.grades i.1).2) S:= by simpa only [zero_add] using! Tested.bill_mul (bill_const f) (pays T Q i)
 have he:=hp.dresses (f:=S) (continuous_const.mul (feesLive T Q i)) (contDiffAt_const.mul (feesSmooth T Q i)) hv; rw [Nat.sub_add_cancel (WardBin.basis_degree _)] at he; exact he
omit A B in
lemma within_point (hh:0<ε)(z:Cover)(i:Stroke F)(u:ℝ)(h:kindle Ψ T Q ε x z i u≠0): z∈Address.census ε Ψ.radius x:=by
 apply (Address.enroll _ hh _ _ _).mpr; have hp:= Ψ.uses (in_ap i ε _ (right_ne_zero_of_mul (left_ne_zero_of_mul h))); change dist _ _≤ Ψ.radius at hp; rwa [dist_eq_norm,sub_zero] at hp -- target dist
omit A B in
lemma rotation : Testifies Ψ T Z Q ε x= fun u y=> ∑ z∈Address.census ε Ψ.radius x, ∑ i: Stroke F,kindle Ψ T Q ε x z i u * bare Z i.1 u (translate z y):=by ext1 u;ext1 y; simp only [Testifies,Finset.sum_apply, Intag];rfl

omit A B in
theorem fingerprint {t:ℝ}(h:t≠0)(X:CoverConfig G): Testifies Ψ T Z Q ε x t X=t^d*(ε^4/ε^d)*(∑ z∈Address.census ε Ψ.radius x, ∑ i:Stroke F, T.dollars i t*(Q.coupling t)⁻¹^(F.grades i.1).2*bare Z i.1 t (translate z X)*waveA i ε Ψ.phi (slide ε z-x)):=by
 rw [rotation,mul_sum]; apply sum_congr rfl;intro i _;rw [mul_sum]; apply sum_congr rfl;intro v _; unfold kindle fees;rw [← Q.leans d v.1 h (WardBin.basis_degree _)];ring
end Aperture
end YM.RegulatorIR.Profiles
