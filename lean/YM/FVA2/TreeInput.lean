import YM.FVA2.PriceTower

/-!
# Finite based BV `Endμ` calculates the inversion-regulator tree

`score_exact` will not suppose any estimates; entry normalization, all-ghost
Berezin contractions, physical transverse field readings are checked at every
regulator order. Interacting unmarked log series excludes the quadratic seed,
as in the End API. Exact alongside every compatible insertion column (`Total`),
for combining the concrete `PowerSeries (Permit E)` representation of fields /
source dictionaries; no rank cap on spatial polynomials. Not assuming saddle
point continuum limit.
-/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Score
open Lattice FormalOPE.RG10 FormalOPE.RG10.BlockGauge TreeBasis Trans Wilson
open PertExtension PertExtension.Series PertExtension.Chart Precision MultiGauge MultiGauge.Stack MultiGauge.Splice GaussianScore
open MS MS.Landau MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.Mom MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater MS.Native MS.Native.Wilsonian MS.SpaceOut
open Function Filter Metric MeasureTheory PairCoords Based Boson Modes Paper ExactTower Finset PowerSeries
open scoped Topology Classical ContDiff
variable {G:Gauge} {n:Side} {U J:Type}
variable (he:Even n.val)(Z: ChartRatio G)(hP:LocalRatio Z)
local notation "Fκ"=> Wilson.Field G n
local notation "P"=> Param G n
local notation "L"=> plan G n
local notation "H"=> haar G n Z
local notation "ψ"=>PairCoords.φ (U:=U) (J:=J)
local notation "δ"=> Trans.price G he
local notation "ν"=> tangent G (staple n).Bulk

variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
local notation "ιθ"=> sharp (bell (J:=J) m) φ (bell_even m)
local notation "ρ"=> Currency (J:=J) m he

section amounts
variable (G n)
-- no exponent term at positive coupling retained in Tagged style -- separate.
def plainI : SpecB (Pos G n) := fun i=> if i=0 then 0 else energyPart G n true (_root_.YM.MS.Native.Wilsonian.core G i)
lemma plain_0 : plainI G n 0=0:= rfl
lemma integrity : Γ (plainI G n) σbranch := by intro i _; unfold plainI; split; exact (FeeP _).zero_mem; exact bulk_fee G n (crisp G i) _ (participates G i) true

def Force : Ticket Fκ:= advancing (WilsonPull L)
def Volume : Ticket Fκ:= rise (Real.log ∘ H)
def supportV : Ticket Fκ:= (rise (L).fpdet * rise H) * exponential (Force G n) -- all unmarked density

lemma force_empty : coeff 0 (Force G n)=0:=by rw [coeff_zero_eq_constantCoeff_apply]; exact advancing_zero _
include hP
lemma volume_empty : coeff 0 (Volume (G:=G) n Z)=0:= by unfold Volume; rw [coeff_zero_eq_constantCoeff_apply, rose_zero (f:=Real.log ∘ H)]; exact Eq.trans (congr_arg Real.log (haar_one (n:=n) Z hP)) Real.log_one
lemma support_one : incline (supportV G n Z):= by unfold supportV incline Force; simp_rw [map_mul,rose,haar_one Z hP,(L).price_one,map_one,initial,mul_one] -- explicit G
omit hP
end amounts

-- use sharp (bell m) --- call signatures check
abbrev bore (F: Ticket (Wilson.Field G n)) : SpecB (Slot U J):= Paper.track φ (ιθ F)
local notation "↓ρ"=> Paper.track ψ

variable [Fintype U][Fintype J][DecidableEq J]
-- notation Ambiguities

def candles : Matrix J J (Fκ→ℝ):=pairBill where pairBill := PairCoords.bill b
abbrev premium := (candles b).map rise
-- matrix positive-order only (quad moved into free Wick)
def shaft : Matrix J J (Ticket Fκ):= premium b - 1
omit [Fintype U] in
lemma bill_matrix : (candles b).det = (L).fpdet := by
    let T:=L; funext x
    let f:= Pi.evalRingHom (fun _:Wilson.Field G n=>ℝ) x; change f ((candles b).det)=LinearMap.det _; rw [f.map_det, ← LinearMap.det_toMatrix b]; apply congr_arg Matrix.det; ext i j; rw [LinearMap.toMatrix_apply]; rfl
lemma actual_det : Matrix.det (1+shaft b)=rise (L).fpdet:= by rw [shaft,add_comm,_root_.sub_add_cancel]; unfold premium; apply locked; intro i j; exact (bill_grown b i j).of_le le_top; exact (bill_matrix b).symm

omit [Fintype J] in
lemma bill_zero (i j:J): PairCoords.bill b i j 0= if i=j then 1 else 0:= by unfold PairCoords.bill; rw [(L).ghosts_zero,LinearMap.id_apply]; by_cases h:i=j <;> simp [*,Ne.symm]
omit [Fintype J] in
lemma shaft_empty (i j:J): coeff 0 (shaft b i j)=0:= by
    unfold shaft; rw [Matrix.sub_apply,Matrix.one_apply,map_sub]; unfold premium; rw [Matrix.map_apply]; change coeff 0 (Stack.rise (PairCoords.bill b i j)) - _=_; rw [coeff_zero_eq_constantCoeff_apply,rose,bill_zero]; split <;> simp

def exert : Price ψ:=ιθ (Force G n)
def heightB : Price ψ:=ιθ (Volume G n Z)
lemma empty_x {E A:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {e:A→E}{p:Sector A}{hp:∀ i,p i=true→e i=0} {F:Ticket E}(hh:coeff 0 F=0): coeff 0 (sharp e p hp F)=0:=by rw [sharp,coeff_map,hh,map_zero]

def past : Matrix J J (Price ψ) := RingHom.mapMatrix ιθ (shaft b)
omit [Fintype U] in
lemma bill_min (i j:J): coeff 0 (past m b i j)=0:= empty_x (e:=bell m (J:=J)) (hp:=bell_even m) (shaft_empty b i j)
omit [Fintype U] in
lemma body : coeff 0 (patches U (past m b))=0:= by unfold patches; simp_rw [map_sum, patch0 (past m b) _ (bill_min m b),Finset.sum_const_zero]

def total : Price ψ:= patches U (past m b)+ (exert (J:=J) m+heightB (J:=J) Z m)
include hP
omit [Fintype U] in
lemma total_min : coeff 0 (total Z m b)=0:= by rw [total,exert,heightB,map_add,map_add,body, empty_x (hp:=bell_even m) (force_empty G n), empty_x (hp:=bell_even m) (volume_empty G n Z hP),zero_add,zero_add]
omit hP

omit [Fintype U] [Fintype J] [DecidableEq J] in
private lemma exert_field (i:ℕ)(hj: LT.lt 0 i) : ↓ρ (exert (J:=J) m) i = -(MS.Book.mask (i+2) (ink (bell m) (WilsonPull L))):= by
    rw [tracking]; unfold exert sharp Force advancing Stack.drop; rw [coeff_map,map_add,coeff_mk,coeff_C,if_neg hj.ne',add_zero,map_neg,map_neg, Submodule.coe_neg]; congr 1; rw [ Nat.add_comm 2 i, Stack.rise, coeff_mk ]; change ink (bell m) (Radial.jet (WilsonPull L) (i+2))=_; simpa only [Nat.cast_add,Nat.cast_ofNat] using (masked (bell (J:=J) m) _ (Wilson.pull_hot L) (i+2)).symm
omit [Fintype U] in
private lemma screw_field (i:ℕ) (hj: LT.lt 0 i) (j k:J):
    (↓ρ (Paper.rowPair j k*(past m b j k))) i= product ψ (block U j k) ( MS.Book.mask i ( ink (bell m) (PairCoords.bill b j k) ) ) := by
     unfold Paper.rowPair; rw [Paper.trackC_mul]; change product ψ (block U j k) (↓ρ (ιθ (shaft b j k)) i)= _; rw [sharp_coe]; unfold shaft; rw [Matrix.sub_apply,Matrix.one_apply,map_sub]; unfold premium; rw [show coeff i (if j=k then 1 else 0:Ticket Fκ)=0 by split; rw [coeff_one,if_neg hj.ne']; exact map_zero _,sub_zero, Matrix.map_apply,Stack.rise,coeff_mk, masked (bell m) (PairCoords.bill b j k) (bill_grown ..)]; rfl

include he hP in
theorem initial_in : seriesPlug (mkPlug m b) (plainI G n)= Paper.track φ (total Z m b):= by
    funext i; rcases eq_zero_or_pos i with h|h; · rw [h]; change plug _ (plainI G n 0)=_; rw [plain_0,map_zero,tracking,total_min Z hP]; rfl
    rw [total,map_add,map_add]; change plug (mkPlug m b) (plainI G n i)= (↓ρ _ i) +((↓ρ (exert m) i) + (↓ρ (heightB Z m) i))
    rw [plainI, if_neg h.ne',(show plug (mkPlug m b) (energyPart G n true (Wilsonian.core G i))=_ from charged hP m b he i), Qboth,Qpair,exert_field m i h]; unfold heightB Volume patches Paper.turnP; rw [lifting (bell m) _ (bell_even m) (Real.log ∘ H) (PairCoords.log_analytic Z hP)]; simp_rw [map_sum,Finset.sum_apply,screw_field m b i h]; rw [sub_eq_add_neg,add_assoc]

include he hP
lemma push (F:Ticket (Wilson.Field G n)) :
    ℶV ρ (↓ρ (Paper.exp (total Z m b)* ιθ F))= fun i=> Complex.ofReal (coeff i (input δ ν (supportV G n Z * F))):= by
    let B:= ιθ F; let Y:= Force G n; let D:=exert m (J:=J); let R:=Volume G n Z
    have hv: Stack.exponential R=Stack.rise H:= by apply (rice (f:= Real.log ∘ H) ((PairCoords.log_analytic Z hP).of_le le_top) (Eq.trans (congr_arg Real.log (haar_one (n:=n) Z hP)) Real.log_one)).trans; apply rise_local; exact ((haar_analytic (n:=n) Z hP).continuousAt.eventually (lt_mem_nhds (show 0<haar G n Z 0 from haar_one Z hP ▸ zero_lt_one))).mono fun x hx=> Real.exp_log hx
    rw [total,exert,heightB,Paper.exp_add _ _ (body m b) (by rw [map_add,empty_x (hp:=bell_even m) (force_empty G n), empty_x (hp:=bell_even m) (volume_empty G n Z hP),zero_add])]; rw [Paper.exp_add _ _ (empty_x (hp:=bell_even m) (force_empty G n)) (empty_x (hp:=bell_even m) (volume_empty G n Z hP)), mul_assoc]
    rw [ ← blossom, ← blossom, hv ]; rw [← map_mul,← map_mul]; rw [ Paper.generator_integral (gram m he) ?_ (past m b) ?_ ?_ (sharp_bound _ _ _ _) (fun i=> sharp_omits _ _ _ _ _ (by rfl)) (bill_min m b) ]; rotate_left
    · exact fun i j=> congr_arg Complex.ofReal (Trans.price_turn G he (m.coord i) (m.coord j))
    · exact fun i j=> sharp_bound _ _ (bell_even m) (shaft b i j)
    · exact fun _ i j=> sharp_omits _ _ (bell_even m) (shaft b i j) _ rfl
    unfold past; rw [show (1+(ιθ).mapMatrix (shaft b))=(ιθ).mapMatrix (1+ shaft b) by rw [map_add,map_one], ← (ιθ).map_det, actual_det b,← map_mul]; unfold supportV; rw [show rise (L).fpdet * (_*F)= rise (L).fpdet * rise H * exponential (Force G n) * F from ?_]; exact funext fun i=> Boson.sharp_pay J m _ _ _ _; ring

omit hP he

def netE (xP:PowerSeries ℝ) : MS.Book.Convolve.T ℂ := fun i=> Complex.ofReal (coeff i xP)
lemma linked (a b:PowerSeries ℝ) : netE (a*b)=Trunk.core (netE a) (netE b):= by
    funext i; unfold netE; rw [coeff_mul,Complex.ofReal_sum]; change _= ∑ p∈antidiagonal i,Complex.ofReal (coeff p.1 a)*Complex.ofReal (coeff p.2 b); apply Finset.sum_congr rfl; intro p _; rw [Complex.ofReal_mul]

def exchange (F:Ticket (Wilson.Field G n)): PowerSeries ℝ := enjoy δ ν F (supportV G n Z)
include hP he
lemma recovers (F:Ticket (Wilson.Field G n)): input δ ν (supportV G n Z* F) = input δ ν (supportV G n Z)* exchange he Z F:= by
    let C:= input δ ν (supportV G n Z); unfold exchange enjoy; change _= C*(_* C⁻¹); rw [mul_left_comm,PowerSeries.mul_inv_cancel, mul_one]; rw [ show constantCoeff C=1 from underBudget _ _ (support_one G n Z hP) ]; exact one_ne_zero
include he
lemma at_end (F:Ticket (Wilson.Field G n)): Endμ ρ ψ (↓ρ (total Z m b)) (bore m F) (netE (exchange he Z F)):= by
    unfold Endμ; rw [← Paper.exp_tracks, bore, ← Paper.pair,push he Z hP m b F, recovers he Z hP F]; rw [ show ℶV ρ (↓ρ (Paper.exp (total Z m b)))= netE (input δ ν (supportV G n Z)) from ?_]; exact linked ..
    rw [← mul_one (supportV G n Z)]; apply Eq.trans _ (push he Z hP m b 1); rw [map_one,mul_one]

theorem Score_exact {Q: SpecB (Pos G n)} {F:Ticket (Wilson.Field G n)} (hpH: Γ Q σbranch) (hp: seriesPlug (mkPlug m b) Q=bore m F)(C: T ℂ):
    Endμ (cov G n true) σbranch (plainI G n) Q C ↔ netE (exchange he Z F)=C:= by
    rw [ compress m b he, ← plug_end _ _ (lawful m b) (integrity G n) hpH, hp, initial_in he Z hP ]; obtain he':=at_end he Z hP m b F; exact ⟨ fun h => classicalμ (by rw [tracking,total_min _ hP]; rfl) he' h,fun h=> h ▸ he' ⟩

variable (O:Wilson.Observable G n)
omit he in
lemma support_field (h:ContDiffAt ℝ ∞ (slice L O) 0) : supportV G n Z * Stack.rise (slice L O) = Stack.rise (sliceK L Z O) * Stack.exponential (Force G n):= by
    rw [show sliceK L Z O= slice L O * ( (L).fpdet * H) from funext (fun x=>by unfold sliceK; simp only [Pi.mul_apply]; rw [mul_comm ((L).fpdet x)] ), rise_mul (g:= (L).fpdet * H) h (((L).fp_analytic.of_le le_top).mul ((haar_analytic Z hP).of_le le_top)), rise_mul ((L).fp_analytic.of_le le_top) ((haar_analytic Z hP).of_le le_top) ]; unfold supportV; ring
lemma evidence_slice (h:ContDiffAt ℝ ∞ (slice L O) 0): PowerSeries.C (capital δ ν) * input δ ν (supportV G n Z * Stack.rise (slice L O)) = sliceRows L Z O:= by
    rw [support_field Z hP O h]; exact ticketed _ _ _ (measure_price G he) _
lemma exchange_fields (h:ContDiffAt ℝ ∞ (slice L O) 0): exchange he Z (Stack.rise (slice L O))= Wilson.sliceEval L Z O:= by
    let B:=supportV G n Z; let F:=Stack.rise (slice L O); let C:=PowerSeries.C (capital δ ν); unfold Wilson.sliceEval; apply (PowerSeries.eq_mul_inv_iff_mul_eq ?_).mpr; swap
    · rw [ ←evidence_slice he Z hP (1:Wilson.Observable G n) (show ContDiffAt ℝ ∞ (slice L (1:Wilson.Observable G n)) 0 from contDiffAt_const), rise_one', mul_one]; rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (PowerSeries.C _),coeff_C, underBudget _ _ (support_one G n Z hP),if_pos rfl,mul_one]; exact (venture _ _).ne'
    rw [ ←evidence_slice he Z hP (1:Wilson.Observable G n) (show ContDiffAt ℝ ∞ (slice L (1:Wilson.Observable G n)) 0 from contDiffAt_const),rise_one',mul_one, ← evidence_slice he Z hP O h, recovers he Z hP (Stack.rise (slice L O))]; ring
where rise_one' : Stack.rise (slice L (1:Wilson.Observable G n))=1:= MultiGauge.Stack.rise_one

/-- Full order insertion, not yet reparametrized in μ,g or shifted for the rank tag; all hypothesis
 `hp` specifies is that the Taylor jets of the position insertion certify a stamp (transverse gauge
 sufficient). Compute same normalized pressure with inversion Wilson.Will specialize to several
 stamped fields and permitted prefactors.
-/
theorem exact_tree (h:Wilson.Physical O)(Hx:Wilson.Honest O){Q: SpecB (Pos G n)} (hq: Γ Q σbranch) (hp: seriesPlug (mkPlug m b) Q=bore m (Stack.rise (slice L O)))(C: T ℂ):
    Endμ (cov G n true) σbranch (plainI G n) Q C ↔ netE ( PowerSeries.mk (Orb.diagonalWith Z (Orb.restrictedO O)))=C := by
    rw [tree_identity L he Z hP h Hx, Score_exact he Z hP m b hq hp, exchange_fields he Z hP O ((Wilson.slice_hot L h Hx).of_le le_top) ] -- name
end YM.FVA2.Score
