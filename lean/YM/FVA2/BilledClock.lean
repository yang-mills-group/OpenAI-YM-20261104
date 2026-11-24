import YM.FVA2.LitLaurent
/-!
# The implemented field matrix converted to unscaled ℏ costs

No claim of order-two parity contributions changing only in a loop degree. This is the actual transform produced
by the proof, used in operator horizon (pre eigen align). Raw $\widetilde B$ itself has
precisely the declared polynomial leading part and 2k shifts; these are additional
bare *comparison* changes, eventually canceled. No assumption on bounds of the field matrix in
this theorem. Includes polynomial cost no negative powers of g after final leg settlement by the
mode-scaled Fees. Compare `RankReach`. Point funding only.V.
 -/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 440000
namespace YM.FVA2.Esprit
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop
open Wilson Lattice Gauge Labels PertExtension PertExtension.Chart
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Land MS.Menus MS.Wind.Leading
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend ArchTurn RadL BoxOffice Counterpart
open Erase Blaze Frost PositionX.Bend
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V: Warehouse G) {U J : Type} {n m k d:ℕ} {N:Side}
local notation "F"=>V.F
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
variable {h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B)(hv:Blaze.Turns V M)
variable {p:ℝ} (P:Prescription (wings G))(T: ExactSpin V P)(Z:Trusted P)(HP:TaylorOKM M (V.native (wings G)) P)
variable (R:Booth p V.F){q:ℕ+} (hq:1<q.val)(K:Knocker h R q hq ( BoxOffice.warehouse V ))
variable (i: BasisIx G d)(u:Owner G d)(x:ℝ)
local notation "r"=> ( Land.read u ).grade
local notation "Ω"=> sameAxis V.F d
local notation "W"=> ( P.fees d u )
-- orientation.L.- n << n+i-r etc. must capture d witness.Buckets
noncomputable def currencyMon : PaperLog:= PowerSeries.mk (fun n:ℕ=> if (( Land.read u ).grade ≤ i.grade+2*n) then (P.fees d u ( i.grade+2*n-( Land.read u ).grade ) ).register i else 0)
-- after canonical κ relation: E(k) (λ^i)^-1 ; restores shift under X.
noncomputable def formMon := invOfUnit (looped P.team ^ i.grade) 1 * currencyMon P i u
include T Z HP hv hq K
lemma powered_u : X^r*Channel.credits i x ( P.fees d u )=X^i.grade * expanded x (currencyMon P i u):= by
    let S:= ( Land.read u ); apply PowerSeries.ext; intro k;
    rw [ coeff_X_pow_mul', coeff_X_pow_mul' ]; unfold Channel.credits expanded; rw [ coeff_expand _ _ _ ];
    by_cases hu:r≤k; swap
    · rw [ if_neg hu ]; by_cases hj:i.grade ≤ k; swap; · rw [if_neg hj ]
      rw [if_pos hj ]; by_cases he:2∣ k-i.grade; swap; · rw [if_neg he ];
      rw [ if_pos he,coeff_map,currencyMon,coeff_mk, if_neg ( show ¬ r ≤ i.grade+2*((k-i.grade)/2) from by omega ),map_zero ]
    -- Budget constraint restored. term at p=n-r
    rw [ if_pos hu,coeff_mk ]; by_cases h:(W (k-r)).register i=0; swap; · obtain ⟨v,hv⟩:= fare_pair V M P T Z R hq K hv HP d _ u i h; rw [if_pos (by omega),if_pos (by omega),coeff_map,currencyMon,coeff_mk, show i.grade+2*((k-i.grade)/2) = k from (by omega),if_pos hu ]; rfl
    rw [ h,Polynomial.eval_zero ]; by_cases hj:i.grade ≤ k; swap; · rw [if_neg hj ];
    rw [ if_pos hj ]; by_cases he: 2∣ k-i.grade; swap; · rw [if_neg he ];
    rw [if_pos he, coeff_map,currencyMon,coeff_mk ]; have hh: i.grade+2*((k-i.grade)/2)= k:= by omega
    rw [ hh,if_pos hu,h,map_zero ]
omit T Z HP hv K hq in
private lemma mapped (a b: PaperLog): expanded x a*expanded x b= expanded x (a*b):= by simp only [expanded, map_mul ]
lemma closedMon : Clock.rate P.team x ^ i.grade * expanded x (formMon P i u)= X^r * Channel.credits i x ( P.fees d u ) := by
    let L:= looped P.team; rw [ powered_u V M hv P T Z HP R hq K i u x, Clock.price_g V M R P T Z ( MixedStory.ceases M V HP h ) hq K x,formMon ]; rw [ mul_pow,mul_assoc,show expanded x (looped P.team)^ i.grade=expanded x (looped P.team^i.grade) from ?_, mapped x,← mul_assoc (_^ i.grade), mul_invOfUnit (looped P.team ^ i.grade) 1 ( by rw [map_pow,log_init,one_pow ]; rfl ),one_mul ]; simp only [expanded,map_pow]; -- lemma map_pow needs p path
    -- ratio cancellation
omit T Z HP hv K hq
private lemma hubK {p: MS.Koszul.Sector J} (U: MS.Book.Program.Cn) (hv:Rooted U): Clock.warp p U hv X=currency p U:= by
    change Clock.prepare p U X= _; unfold Clock.prepare; apply PowerSeries.ext; intro i; rw [ coeff_mk, Program.rules, currency,coeff_map ]; by_cases he:i=0; · subst i; simp only [show Finset.Iic 0={0} from (by ext; simp), Finset.sum_singleton, hv,coeff_X ]; simp only [if_neg (show ¬(0:ℕ)=1 from by decide),smul_zero ]; exact (map_zero _).symm; -- placeholder
                                                                                                  -- norm
    rw [ Finset.sum_eq_single_of_mem 1 ( Finset.mem_Iic.mpr (Nat.one_le_iff_ne_zero.mpr he)) ]; · simp only [Program.cut,pow_one,coeff_X,if_true]; exact ( Algebra.algebraMap_eq_smul_one (R:=ℂ) (A:= Dark p) ( coeff i U ) ).symm
    intro v _ h; rw [ coeff_X,if_neg h, smul_zero ]
lemma pp_resource (p: MS.Koszul.Sector J)(i:ℕ) : Clock.currency p (X^i)=X^i := by unfold currency; rw [map_pow,map_X ]
include T Z HP hv K hq
variable (b:Module.Basis U ℝ (Wilson.Field G N)) (o:Site N) (e:ℝ) (x:ℝ)
local notation "κ"=> Clock.warp ψ (shift P.team x) (share P.team x)
def mon (P:Prescription (wings G))(i:BasisIx G d)(u:Owner G d)(x:ℝ)(e:ℝ) : Cn:= PowerSeries.C ( factorEF e d i.size )* into (expanded x (formMon P i u))
-- point use
lemma speaks (he:e≠0) : X^r * (((e:ℂ)^d )⁻¹ • Track.lantern V b ( J:=J ) o P.team x ( P.fees d u ) )=∑ i: BasisIx G d,currency ψ ( mon P i u x e ) * κ ( rawτ V b o e d i ):= by
    rw [ BoxOffice.launched V b o e P.team x he, Finset.mul_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; let F0:= Land.Prescription.team P; rw [← costT V b o i e, map_mul κ, map_pow κ, hubK ];
    rw [← pp_resource, ← mul_assoc,← mul_assoc ( currency ψ ( mon P i u x e )), ← map_pow ( currency ψ ), ← map_mul ( currency ψ ), ← map_mul ];
    congr 2; rw [mul_left_comm,mon,mul_assoc, mul_comm (into (expanded x ( formMon P i u )) ), show Program.shift P.team x=into (Clock.rate P.team x) from bare_shift _ _,← map_pow into, ← map_mul into, closedMon V M hv P T Z HP R hq K i u x, map_mul,map_pow, show into X=X from map_X _ ];
end YM.FVA2.Esprit
