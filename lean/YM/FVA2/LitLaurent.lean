import YM.FVA2.ChooseRad
import YM.FVA2.RankReach
import YM.FVA2.KappaClock
/-!
# The raw & implemented **ℏ** stencil convention on this prescription.
 Including exact shifts giving literal vertices on the torus even if odd labels.

Bare `g^r B^a` stripped of outer spacing `epsilon^{-h}`. Emits only
  shifts by 2δ. Applies to the pure *physical* letter lifts. Includes free holonomy
  test exactly in signed radial concatenations. Implemented comparison in Cost algebra.
 -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.FVA2.Esprit
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop
open Wilson _root_.YM.Wilson Lattice Gauge Labels PertExtension PertExtension.Chart
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Land MS.Menus MS.Wind.Leading
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend ArchTurn RadL BoxOffice Counterpart
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V: Warehouse G) {U J : Type} {n m k d:ℕ} {N:Side}
local notation "F"=>V.F
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
variable (i:BasisIx G d)
private abbrev Wζ (x:ℝ)(k:ℕ)(i:BasisIx G d): ℝ:= x^(i.grade-k)
def preα (u:Owner G d) (j:V.Atom d) : ℂ:= V.qfits (wings G) d (Land.read u).grade u.2 j
def allowed (k:ℕ)(u:Owner G d)(j:V.Atom d) : Prop:= 2*k+ V.grade d j= (Land.read u).grade
variable (u:Owner G d)(x:V.Atom d)
open Finset
lemma actual_price : (( V.prices (wings G) d (Land.read u).grade u.2 x ):ℂ)=preα V u x:= Warehouse.price_cast ..
private lemma pre_Parity (hv: Odd (( Land.read u ).grade + V.grade d x )): preα V u x=0:= by
    let y:= V.fits ( wings G ) d (Land.read u).grade u.2; let W:= V.scopeW d; let L:= Warehouse.inftyQ G; let f(k):=(-1:ℂ)^k; have hx: W.sign y= f ( Land.read u ).grade • y:= by
       funext i; by_cases hi:V.grade d i=(Land.read u).grade; · change _ ^W.slots i*_=_; rw [show W.slots i=( Land.read u ).grade from hi]; rfl
       have h: y i=0:= V.fit_ceil (wings G) u.2 i (fun h=> hi (congr_arg Prod.snd h) ); change _^ _*y i = _ * y i; rw [h,mul_zero,mul_zero ];
    obtain H:= W.inverse_sign y ( Q:= L ); rw [hx,map_smul] at H; obtain ht:= congr_fun H x; let r:= (Land.read u).grade; let a:= V.grade d x; change f r * preα V u x=f a *preα V u x at ht; by_contra hb; obtain hl : f r=f a:= mul_right_cancel₀ hb ht; obtain hx := ( hv.neg_one_pow ( α:=ℂ ) ); change f ( r+a )= -1 at hx; rw [show f (r+a)=f r*f a from pow_add .., hl, show f a*f a=1 from MS.Reed.invol (R:=ℂ) _ ] at hx; norm_num at hx
lemma shaped (hi:preα V u x≠0) : ∃ k, allowed V k u x := by
    let k:= ( Land.read u ).grade; let p:= V.grade d x; have h0:p≤k:= le_of_not_gt fun h=> hi (V.lower _ u.2 x h); have h1 : Even (k+p):= Nat.not_odd_iff_even.mp (fun h=>hi ( pre_Parity V u x h )); obtain ⟨i,hi⟩:=h1; refine ⟨ ( k-p ) / 2, (by change 2*(( k-p )/2)+p=k; omega )⟩
def pad (k:ℕ)(x:V.Atom d) : ℂ:= open Classical in if allowed V k u x then preα V u x else 0
lemma requestRank (k:ℕ)(j:V.Atom d)(h:pad V u k j≠0): 2*k + V.grade d j=( Land.read u ).grade:= by unfold pad at h; split at h; assumption; exact False.elim ( h rfl )
-- publish the gauge-covariant stencil **in hbar=g_*²** before link rescaling. All orders finite.
def prebake (k:ℕ) : V.Atom d→ℂ:= pad V u k
def recipe (u: Owner G d)(k:ℕ) : CoverConfig G→ℂ:= (V.S d).evaluate (prebake V u k)
-- formal reading on this pre-cov test. Launch at any period, Ward and real.
lemma booked_covariant (k:ℕ) : GaugeInvariant ( recipe V u k ):= ( V.h d ).gaugeInvariant _
lemma fixedBar (k:ℕ): star (prebake V u k)=prebake V u k:= by
    funext x; change star ( pad V u k x )=pad V u k x; unfold pad; split <;> simp [← actual_price ]
lemma real_in (k:ℕ)(X: CoverConfig G): star (recipe V u k X)=recipe V u k X:= by unfold recipe; rw [← (V.h d).ordinary_real, fixedBar ]
private lemma baseℓ : (Land.read u).size=d:= rfl
def owner : Label G d:= Warehouse.label (wings G) d ( Land.read u ).grade u.2
lemma initialZ : prebake V u 0= V.fits (wings G) d ( Land.read u ).grade u.2:= by
    funext i; unfold prebake pad; split; · next hx=> unfold allowed at hx; apply Warehouse.aligns; omega
    next hx=> symm; refine V.fit_ceil _ _ _ (fun h=> hx ?_ ); unfold allowed; rw [ show V.grade d i =_ from congr_arg Prod.snd h ]; simp
lemma role : YM.Source.Projects V.H (owner u) ( recipe V u 0 ):= by unfold recipe; rw [initialZ ]; refine (?_ : ( V.scene d ).coords.symm ( V.fits (wings G) d ( Land.read u ).grade u.2 )=owner u ) ▸ (( V.h d ).projects _); exact (V.scene d).coords.symm_apply_apply _ -- caution dependent replacement
-- same ownership in both.Bare letter.S.Prep.E
lemma sameLetter : Pert.RawLabels.physicalLabel V.F d (sameAxis V.F d (Land.read u))=owner u:= (physical_letter V.F ( Land.read u )) -- refl incl raiseLabel
lemma radial_S {A: Land.Booked (wings G)}(h: MS.RadL.Reg A): RadL.Recipe (fun z=>MS.Motif.Literal.value _ z (A.optics d u)) ( owner u ).val d (Land.read u).grade:= exact_optics u h
-- represent evaluated stencils at pre-link on positions, should link to $ξ^r$ scaled Price.
abbrev Deck (d:ℕ)(u:Owner G d) (k:ℕ)(p:Site N): Config G N→ℂ:= (V.S d).places (prebake V u k) p
lemma conform (k:ℕ)(p:Site N) (y:Config G N): Deck V d u k p y= recipe V u k (expandAt p y):= rfl
lemma corrected (k:ℕ)(p:Site N)(y:Config G N): Deck V d u k p y= ∑ i:V.Atom d,pad V u k i * ((Track.loadStamp V p i).stencil y:ℂ):= by
   let U:= expandAt p y; let Z:= V.scene d
   let W:= V.S d; let L: Z.Coeff→ₗ[ℂ] ℂ:= ( MvPolynomial.aeval (YM.Source.entry (S:=W.stencil) U) ).toLinearMap.comp W.evalC; change L ( prebake V u k )= _; have he : prebake V u k = ∑ i: V.Atom d,pad V u k i • (Pi.single i 1:Z.Coeff) := by funext x; rw [Finset.sum_apply,Finset.sum_eq_single x ]; simp [prebake]; intro i _ h; simp [Ne.symm h]; simp
   rw [he,map_sum ]; apply Finset.sum_congr rfl; intro i _; rw [ map_smul, smul_eq_mul ]; apply congr_arg ( pad V u k i * · ); change W.evaluate _ U=(( W.evaluate _ _ ).re:ℂ);
   apply Eq.symm; apply Complex.conj_eq_iff_re.mp; refine Eq.trans (Eq.symm (( V.h d|>.ordinary_real ..))) ?_; congr 1; funext i; rw [Pi.star_apply ]; simp only [ Pi.single_apply ]; split <;> simp
end YM.FVA2.Esprit
namespace YM.FVA2.Esprit
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop
open Wilson _root_.YM.Wilson Lattice Gauge Labels PertExtension PertExtension.Chart
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Land MS.Menus MS.Wind.Leading
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend ArchTurn RadL BoxOffice Counterpart
open PowerSeries
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V: Warehouse G) {U J : Type} {n m k d:ℕ} {N:Side}
local notation "F"=>V.F
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
-- $τ^r X_τ B$ equality. (X^r suppress spacing too)
variable (b:Module.Basis U ℝ (Wilson.Field G N)) (o:Site N) (i:BasisIx G d) (u:Owner G d)
local notation "Ξ"=> Boson.sharp (bell (J:=J) b) φ (bell_even b)
abbrev lineT (x:V.Atom d) := Boson.sharp (bell (J:=J) b) φ (bell_even b) (MultiGauge.Stack.rise ( Wilson.slice ( plan G N ) ( Track.loadStamp V o x ).stencil))
def tB (u:Owner G d) (k:ℕ) : Paper.Price ψ:= ∑ j: V.Atom d,(pad V u k j) • lineT V b o j
-- print coefficient expression. Char.
def rawτ (e:ℝ) (d:ℕ) (i:BasisIx G d) : Paper.Price ψ:= (((e:ℂ)^i.size)⁻¹) • ∑ k∈ Finset.Iic i.grade,X^(2*k) * (tB V b o (d:=i.size) i.2 k)
local notation "Ω"=> sameAxis V.F d
private lemma traffic (x:V.Atom i.size): X^i.grade * ( (V.prices _ i.size i.grade i.2.2 x:ℂ) • Ξ (Track.singleStamp V o x) )= ∑ j∈Finset.Iic i.grade,X^(2*j)*(( pad V i.2 j x ) • lineT ( J:=J ) V b o x):= by
   let u: Owner G i.size:= i.2; let p:= preα V u x;
   rw [show ( (V.prices _ i.size i.grade i.2.2 x :ℝ):ℂ )=p from actual_price V u x]; by_cases hp:p=0; · simp_rw [ show ∀ j:ℕ,pad V i.2 j x=0 from fun j=> by unfold pad; split; exact hp; rfl ]; rw [ hp ]; simp
   obtain ⟨ k,h ⟩:= shaped V u x hp; have hu: 2*k+ V.grade i.size x=i.grade:= h;
   rw [ Finset.sum_eq_single_of_mem k ( Finset.mem_Iic.mpr (by omega) ),pad, if_pos h ]; conv_lhs=> rw [ ← hu ];
   rw [ pow_add, mul_smul_comm, mul_assoc, lineT, ← Track.loadedStamp V o x,map_mul,map_pow, show Ξ X=X from map_X _, mul_smul_comm ]
   intro j hj hj'; rw [ pad,if_neg (fun h'=> hj' (by obtain hv:2*j+ V.grade i.size x=i.grade := h'; omega )),zero_smul,mul_zero ]
-- e≠0? even zero convention fine!
lemma costT (e:ℝ): X^i.grade*velvet V b o e d (Ω i)=rawτ (J:=J) V b o e d i:= by
    rw [BoxOffice.costing, mul_smul_comm, Finset.mul_sum ]; simp_rw [traffic V b o i ]; unfold rawτ tB; rw [Finset.sum_comm ]; simp_rw [ Finset.mul_sum ]
end YM.FVA2.Esprit
