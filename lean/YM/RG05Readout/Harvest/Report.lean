import YM.RG05Readout.Harvest.Prices
/-!
# Master-read (regulated) returned value, authentic on one term valuation.
 Define in threshold and BEFORE restoring output field exponent. Genuine
 equality: full S_pure through ancestor propagation of all rooted slots, then
 payment from same orientations.T basis. Expose uniqueness already at finite
 c density; no assuming any future analytic mark expansion agrees.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}{e:ℝ}(h:C.Makes)
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A!"=> C.path.levels
local notation "Λ"=> C.S.toDepth
local notation "L"=> C.path.levels.clock.op
local notation "R"=> C.path.rep N p
local notation "κ₁"=> kappa C.path
variable {D:Address.Rail C}{V : Address.Sight C d p}{U: Address.Emblems C d} (hm: n ≤ m)(hv:b ≤ n)(hN:n+1 ≤ N)
local notation "η"=> (hv.trans hm)
local notation "H"=> finer U (η)
local notation "Ω"=> pulls C p N n d hN
/-- Master reports emitted to m tuning, in C labels at threshold and then
 translated to m. Input bin F to pulls = UNNORMALIZED evaluation weights
 at n+1 made from assessed units at top, BEFORE multiplying physical occupied
 measures of output. External test probes in terminal certificate charged separately,
 not examined by this definition. -/
def Sees (C:Family G)(p N n m b d:ℕ)(hm:n ≤ m)(hv:b≤ n)(hN:n+1≤N)(U:Emblems C d)(F:Bin G (C.side N p))(M: Palette C d):Prop:=
    ∃ (P:Tape G (C.side b p)), pulseOut P = pulls C p N n d hN F b hv ∧ ∃ Q e, Printed C d (C.path.rep N p b) 0 (kappa C.path b) P Q ((finer U (hv.trans hm)).symm M) e
local notation "U!"=> Sees C p N n m b d hm hv hN U
variable (F:Bin G (C.side N p)){B:ℕ→ℕ→ℝ}(hw: Awake D B b d)(ht: Spine D B h b p d N V U)
include ht hw
section coordinates
variable (X:∀ i:ℕ,Tape G (C.side i p))(Y:ℕ→ Palette C d) (e:ℝ) (hh: Shadow.Signature C p b n N d h D V (pulls C p N n d hN F n (le_refl n)) e Y X)
local notation "A"=> advances U Y b
local notation "u"=> Y n-A n
local notation "M₀"=> finer U hm u
noncomputable def upper (i:ℕ)(hr:i≤ n):Palette C d:= (finer U hr).symm (Y n-A n)
local notation "W"=> upper (U:=U) (n:=n) (b:=b) Y
omit ht hw in
lemma uphill (he:i<n): W i he.le=U i (W (i+1) he):=by
    unfold upper; rw [show finer U he.le=(finer U i.le_succ).trans (finer U he) from Many.sumwalk ..,show finer U i.le_succ= (LinearEquiv.refl ℂ _).trans (U i).symm from by rw [finer_next (le_refl i),base_value]]; rfl
local notation "X!"=> Bin G (C.side N p)
include hh
omit hw in
lemma assembled (i:ℕ)(he:b ≤ i)(hi:i ≤ n): pulseOut (X i+V i (W i hi+A i))=Ω F i hi :=by
    have hhN:=hi.trans (n.le_succ.trans hN)
    induction hi using Nat.decreasingInduction with
    | self=>
       obtain ⟨P,hP,hw'⟩:= hh.basis; rw [hw'.1,upper,base_value]; simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply,sub_add_cancel]; exact hP
    | of_succ i hi ih=>
       have h':i+1 ≤ N:=hi.trans_le (n.le_succ.trans hN); have hp₁:= he.trans i.le_succ
       let pV:=V (i+1) (W (i+1) hi+A (i+1)); have hX: BLight (pulseOut (X (i+1))):=by
            obtain ⟨z,hz⟩:= hh.rolls.empty (i+1) hp₁ hi; exact fun f=>(hz.useful (h.wilson.represents _ _ _ h').good f).integr
       have htP:BLight (pulseOut pV):=by obtain ⟨z,hz⟩:= (ht.legal (i+1) hp₁ h').capacity0 _; exact fun f=> (hz.useful (h.wilson.represents _ _ _ h').good f).integr
       rw [down hN F hi, ← ih hp₁ h'] -- order general
       let z:=U i (W (i+1) hi+A (i+1)); let Jr:= journey C p i N d
       have hJ: Jr (pulseOut (X (i+1)+pV)) =pulseOut ((X i+V i (Y i))+ V i z):=by
           rw [show pulseOut (X (i+1)+pV)=pulseOut (X (i+1)) + pulseOut pV from rfl,show Jr _=_ from sail_plus (N:=N) (d:=d) hX htP];
           rw [show journey C p i N d (pulseOut pV) = pulseOut (V i z) from (funext (fun f=> travels h ht (hm:=h') (hp:=he) f _) |>.symm), show journey C p i N d (pulseOut (X (i+1)))=pulseOut (X i+ V i (Y i)) from (funext (fun f=> proceeds C p i N d _ _ f ((hh.rolls.gate i he hi h'))) |>.symm)]; rfl
       have hz:Y i+z= W i hi.le + A i:=by unfold z; rw [map_add,←uphill Y hi,adv_leans he]; abel
       rw [← hz,map_add, ←add_assoc]; exact hJ.symm
lemma reports_tt :
    ∃ (P:Tape G (C.side b p)), pulseOut P = pulls C p N n d hN F b hv ∧ ∃ Q, Printed C d (C.path.rep N p b) 0 (kappa C.path b) P Q ((H).symm M₀) (Shadow.tab C (Shadow.bid C n d e) n b+B d b*size ((H).symm M₀)):=by
    have he:W b hv=(H).symm M₀:= by unfold upper; rw [Many.sumwalk U hv hm]; change (finer U hv).symm _= (finer U hv).symm ((finer U hm).symm _); rw [LinearEquiv.symm_apply_apply] -- notation
    obtain ⟨T,hT⟩:= hh.rolls.empty b (le_refl b) hv; obtain ⟨Z,hZ⟩:= (ht.legal b le_rfl (hv.trans (n.le_succ.trans hN))).capacity0 (W b hv)
    obtain ⟨s,b',α,β,P,Q,K,-⟩:=(hw.toll p b N le_rfl (by omega)).author; let S:= (K.cursor.sense d le_rfl)
    let W':= X b+ V b (W b hv+A b); refine ⟨W',assembled h hN F ht X Y e hh b le_rfl hv, T+ Z,?_⟩
    unfold W'; rw [adv_base,add_zero]; have ht':=hT.addP hZ (h.wilson.represents _ _ _ (hv.trans (n.le_succ.trans hN))).good S.order S.power; rw [zero_add] at ht'; rwa [← he]
lemma reports : U! F M₀:=by
    obtain ⟨P,hP,Q,hQ⟩:=reports_tt h hm hv hN F hw ht X Y e hh
    exact ⟨P,hP,Q,_,hQ⟩
end coordinates
include hw
omit ht
lemma Sees.unique {M M':Palette C d}(hp:U! F M)(hq: U! F M'):M=M':=by
    obtain ⟨P,hE,Y,b',hx⟩:= hp; obtain ⟨Q,hR,V',c,hv'⟩:=hq; have hh :=germ_eyelet hw hx hv' le_rfl (show b < N from by omega) (hE.trans hR.symm); exact ((finer U (η)).symm.injective hh)
omit hw in
lemma Sees.zeroC : U! 0 0:=by refine ⟨0,?_,0,0,?_⟩; rw [vacC]; rfl; rw [map_zero]; exact Printed.blank (Real.sqrt_pos.mpr (forcedPos ..)) -- edit
include h
lemma Sees.upward {x q:Bin G (C.side N p)}{M M':Palette C d}(hP:U! x M)(hQ:U! q M')(hp: timely x)(hr:timely q): U! (x+q) (M+M') := by -- p binder conflict
    obtain ⟨X,hX,A,x₁,h_X⟩:=hP; obtain ⟨Y,hY,A',x₂,h_Y⟩:=hQ
    refine ⟨X+Y,?_,A+A',x₁+x₂,?_⟩; rw [doubles h hN hv hp hr,←hX,←hY];rfl
    obtain ⟨s,b',α,β,L',Q,K,-⟩:=(hw.toll p b N le_rfl (show b<N by omega)).author
    rw [map_add]; exact h_X.addP h_Y (h.wilson.represents _ _ _ (by omega)).good (K.cursor.sense d le_rfl).order (K.cursor.sense d le_rfl).power
omit h in
lemma Sees.times (z:ℂ){M:Palette C d}(hp: U! F M): U! (z • F) (z • M) :=by
    obtain ⟨X,hX,A,x',h_X⟩:= hp; obtain ⟨s,b',α,β,L',Q,K,-⟩:=(hw.toll p b N le_rfl (show b<N by omega)).author; refine ⟨z • X,?_,z • A,‖z‖*x',?_⟩; rw [budgets,← hX];rfl; rw [map_smul]; exact h_X.twist (K.cursor.sense d le_rfl).order (K.cursor.sense d le_rfl).power _
omit hw h
/-! Cost for layout replay in Mark pallet. Lerma string cost from
 inverse matrix; forward has engineering attenuation in reverse. -/
noncomputable def advanceCost (C:Family G)(d:ℕ){b m:ℕ}(hv:b ≤ m):ℝ:=
    stringCost C hv * (C.S.a b/C.S.a m)^d
lemma string_pos' {b m:ℕ}(hv:b ≤ m) : 0 < stringCost C hv:=by
    induction m,hv using Nat.le_induction with
    | base=> simp only [Address.string_base]; exact zero_lt_one
    | succ m hm ih=> rw [Address.string_next hm]; exact mul_pos (zero_lt_one.trans_le (lamp_nn ..)) ih
lemma advanceCost_pos {b m:ℕ}(hv:b ≤ m):0<advanceCost C d hv:=mul_pos (string_pos' hv) (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _)
include ht h
lemma Spine.downsized {n m:ℕ}(hp:b≤ n)(hv:n≤ m)(hq:m≤ N) (x : Palette C d): size ((finer U hv).symm x)≤ advanceCost C d hv * size x:=by
    induction m,hv using Nat.le_induction generalizing x with
    | base=> rw [advanceCost,base_value,string_base,div_self (C.S.a_pos _).ne',LinearEquiv.refl_symm, LinearEquiv.refl_apply]; simp
    | succ m hm ih=>
       have hh:= (ht.follows m (hp.trans hm) hq).strength x
       let K := (C.S.block m).val
       have he: size (U m x) ≤ ld C.path.levels m * ((K:ℝ)^d*size x):= hh.2.trans (mul_le_mul_of_nonneg_left (Address.size_tuned ..) (zero_le_one.trans (lamp_nn (C:=C) m)))
       rw [Address.finer_next hm]; change size ((finer U hm).symm (U m x)) ≤ _
       apply ((ih (m.le_succ.trans hq) (U m x)).trans (mul_le_mul_of_nonneg_left he (advanceCost_pos hm).le)).trans_eq
       unfold advanceCost; rw [Address.string_next hm,C.S.a_step m]
       rw [show C.S.a n / (C.S.a m / ↑(C.S.block m).val)=C.S.a n / C.S.a m * K from ?_]; ring
       change _=_* ((C.S.block m).val:ℝ); field_simp [(C.S.a_pos m).ne']
end YM.RG05Readout.Harvest
