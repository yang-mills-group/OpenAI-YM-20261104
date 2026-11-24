import YM.SignedWilsonExpansion.WickFace
import YM.FVA2.Parity.Clock
namespace YM.SignedWilsonExpansion.PhaseTilt
/-! Through-order-two tilt across same field labels and canonical comparison.
 Position equality requires a common `MS_Data` at the phase via canonical solve.
 No estimates on inter-horizon powers assumed. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Land MS.Fleet MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {d n:ℕ} {Y:Initialize G} {B: Normalize.Store G}  -- remove
local notation "r" => Guard G 4
local notation "Ξ" => PowerSeries.coeff
local notation "λF" => Facets.actMark -- λ unicode keyword?
local notation "π" => Extent.token
local notation "Φ" => Manifest.response
variable (h:G.Simple)
local notation "κ" => Sec G 4
local notation "E" => WickFace.lens G
lemma starts_cost (V:Type)[AddCommGroup V][Module ℂ V] (q:Cn) (he:Tangent q)(f:ℕ→V)(hf:f 1=0): Program.substitute q f 2=f 2:= by
    rw [ Program.rules, Finset.sum_eq_single_of_mem (2:ℕ) (by simp) ]; · rw [ show Program.cut q 2 2=1 from (stamp_n q he.start 2).trans (by rw [he.lead,one_pow]),one_smul ]
    intro i hi hv; replace hi:= Finset.mem_Iic.mp hi; interval_cases i; · rw [ show Program.cut q 0 2=0 from (by simp [Program.cut]),zero_smul ]; -- period
    · rw [hf,smul_zero];
    · contradiction
include h
lemma parity_point (f:ℕ→Structure1.Point G 4 n)(hu: FVA2.Parity.Invol.Relays f): f 1=0:= by ext1 p; have h₁:= hu 1 p; rw [ show hinge 4 ∘ p=p from funext (fun i=> even4 h (p i)) ] at h₁; have hv: Hue.σ 1=(-1:ℂ):=(by unfold Hue.σ; rw [pow_one]); rw [ hv, smul_eq_mul,neg_one_mul ] at h₁; change _= (0:ℂ); linear_combination h₁/2
lemma parity_cost (P:r)(hu: FVA2.Parity.Invol.Facing P) : Ξ 1 P=0:= by ext1 p; have h₁:= hu 1 p; rw [even4 h, even4 h, show Hue.σ 1=(-1:ℂ) from ( by unfold Hue.σ; rw [pow_one]),show (-1:ℂ) • ((Ξ 1 P) p) = - (Ξ 1 P p) from neg_one_smul ℂ ((Ξ 1 P) p)] at h₁; have hp:= add_eq_zero_iff_eq_neg.mpr h₁; rw [← two_smul ℂ] at hp; exact (smul_eq_zero.mp hp).resolve_left two_ne_zero
lemma feeling (F:Way G 4)(hg:StarGround F)(P:r)(hp: Base P)(he:FVA2.Parity.Invol.Facing P)(x:Stage n)(u:Tags G 4 n): actMark P F n x 2 u-F n x 2 u=Φ x u (Ξ 2 P):= by
    have hr (i:ℕ)(hi:i<2): Ξ i P= Ξ i (1:r):= by
      interval_cases i; · rw [hp.zero]; exact (by simp)
      rw [parity_cost h P he]; simp
    obtain ht:= Manifest.exhibits F P 1 hg (by decide : (2:ℕ)≠0) Base.one hr x u; rw [ acts_h F, PowerSeries.coeff_one, if_neg (by decide : (2:ℕ)≠0), show Ξ 2 P-(0:FieldEnd G 4)= Ξ 2 P from sub_zero (Ξ 2 P) ] at ht; exact ht
-- Scale: pay β action, at [2] it's `exhibits` exactly, not asymptotic in length.
variable {O:Booked (Press.portDeck G)}(M:MS_Data G O)(ν:ℝ)
variable (Y:Initialize G){B: Normalize.Store G}(K:Rose.Pick B)(S:Land.Prescription (Press.portDeck G))(hs:TaylorOKF M (Press.wickInput Y) S)(hr:Favors.Horder S)(hu: Ace.UnitP S)
local notation "P'" => wave ν M
local notation "F" => (P' 4)
local notation "β" => GroupS.gaugeM Y K M ν
local notation "A₀" => (Measure.liftT K ν M 4)
local notation "A₁" => (Measure.Z Y K ν M 4)
local notation "Ψ" => GroupS.Ψ K M ν
local notation "Φℓ" => Measure.start Y K 4
local notation "φM" => Measure.outlook Y K 4
include hs hr hu
lemma order_first (x:Stage n): F n x 1=0 ∧ Φℓ n x 1=0 ∧ φM n x 1=0:= by obtain ⟨a,b,c⟩:= FVA2.Parity.Clock.aligns ν Y K M S h hs hr hu 4 n x; exact ⟨ parity_point h _ a, parity_point h _ b, parity_point h _ c ⟩
lemma tilt_two (t:ℝ) (x:Stage n)(u:Tags G 4 n): F n x 2 u-scaling t F n x 2 u= Φ x u (Ξ 2 (β t 4)):= by
    obtain hL:= Scale.Precise.mainM ν Y K M S h hs hr hu
    rw [ ← feeling h ( scaling t F ) ( Manifest.fuel _ M Y S h hs ( before ν M ) t ) _ ( hL.paid t 4 ) ( FVA2.Parity.Clock.presence_M ν Y K M S h hs hr hu t ) x u, hL.reads t 4, couple, starts_cost _ _ ( hL.led t ) _ (order_first h M ν Y K S hs hr hu x|>.1) ] -- but recu unwinds
-- Compare via location or Z, payrolls pointwise (x arbitrary). No product cutoff factors.
lemma settle (x:Stage n)(u:Tags G 4 n): Φℓ n x 2 u-F n x 2 u= Φ x u (Ξ 2 A₀):= by
    let Q:=Measure.f K ν M; let Bv:=couple Q F
    rw [ ← Measure.together Y K ν M S h hs hr hu ]; change actMark A₀ Bv n x 2 u-F n x 2 u=_; rw [ ← feeling h Bv ( step_dawn F Q (before ν M) ) _ ( Measure.charges Y K ν M S h hs hr hu ) ( FVA2.Parity.Clock.presence_l ν Y K M S h hs hr hu ) ]; rw [ show Bv n x 2=F n x 2 from starts_cost _ _ ( Specific.vigor_f Y K ν M S h hs hr hu ) _ (order_first h M ν Y K S hs hr hu x|>.1) ]
lemma settled' (x:Stage n)(u:Tags G 4 n): φM n x 2 u - F n x 2 u= Φ x u (Ξ 2 A₁):= by
    let Q:=Measure.f K ν M; let Bv:=couple Q F
    rw [ ← feeling h Bv (step_dawn F Q (before ν M) ) _ ( Measure.litZ Y K ν M S h hs hr hu ) ( FVA2.Parity.Clock.presence_Z ν Y K M S h hs hr hu ), Measure.compares Y K ν M S h hs hr hu, show Bv n x 2=F n x 2 from starts_cost _ _ ( Specific.vigor_f Y K ν M S h hs hr hu ) _ (order_first h M ν Y K S hs hr hu x|>.1) ]; -- maybe Bv syntactic
-- all term logs from these Native scale cocycles.
local notation "∆" => (fun t=>Ξ 2 (β t 4))
lemma cocycle (t v:ℝ): Ξ 2 (β (t+v) 4)= Ξ 2 (β t 4)+ Ξ 2 (β v 4):= by
    obtain hL:= Scale.Precise.mainM ν Y K M S h hs hr hu; rw [ hL.toTouched.additive t v|>.2, Scale.old_g v (β t 4) (hL.ready t 4),PowerSeries.coeff_mul ]; -- add phase
    have hp(u:ℝ): Ξ 1 ( β u 4 )=0:= parity_cost h _ ( FVA2.Parity.Clock.presence_M ν Y K M S h hs hr hu u );
    rw [ show Finset.antidiagonal 2={(0,2),(1,1),(2,0)} from by decide,sum_insert (by decide),sum_insert (by decide),sum_singleton ]; -- check order
    simp only [ hp,zero_mul, add_zero,zero_add, (hL.paid ..).zero, (Base.zero ((hL.paid v 4 ).switch (hL.led t|>.real))),mul_one,one_mul, Reg.Point.stepV, PowerSeries.coeff_mk ]; rw [ starts_cost _ _ (hL.led t) _ ( hp v ), add_comm, pay0, (hL.paid v 4).zero,mul_one ]
lemma portwise (t:ℝ) (p:Sec G 4) (z:Sec G 4→ₗ[ℂ] ℂ): z ((Ξ 2 (β (-t) 4)) p)= t • z (Ξ 2 ( β (-1) 4 ) p):= by
   obtain H:= Scale.Precise.mainM ν Y K M S h hs hr hu; let L(x:ℝ):= z (Ξ 2 ( β x 4 ) p); have hp:L (0:ℝ)=0:= by unfold L; rw [ H.toTouched.ground.2,PowerSeries.coeff_one]; simp
   let T:ℝ→+ℂ:={ toFun:= L, map_zero':=hp, map_add':=fun t v=>by unfold L; rw [ cocycle h M ν Y K S hs hr hu,LinearMap.add_apply,_root_.map_add ] }
   have hT: Continuous T:= by obtain ⟨x,hx⟩:= Rhythm.from_poly.mp (H.proper 4 2 p z); change Continuous (fun t=> z (Ξ 2 ( β t 4 ) p)); rw [hx]; fun_prop
   change T (-t)=_ ; rw [show -t=t • (-1:ℝ) from (by simp), map_real_smul T hT ]; rfl
-- real conditions on readings: both G^X,G^P transforms from wave. D2 difference later real. Quote natural d=weight. 
end
end YM.SignedWilsonExpansion.PhaseTilt
