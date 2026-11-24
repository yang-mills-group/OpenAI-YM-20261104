import YM.FVA2.BilledField
/-!
# Explicit field scheme maps from pricing to `B_a` array BEFORE any asymptotic.

Apply to Own columns by our sameAxis. Horizon compatibility strict. `surcharge` uses Vis real.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 920000
set_option quotPrecheck false
namespace YM.FVA2.Counterpart
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop
open Wilson Lattice Gauge Labels PertExtension PertExtension.Chart
open PertExtension.LatticePT RG
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve MS.Land MS.Menus
open PositionX.Jet
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Frost Blaze ArchTurn
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (V: Warehouse G) (P:Land.Prescription (wings G)) (sx sm:ℝ) (n:ℕ) {r d:ℕ}
local notation "F"=> V.F
local notation "Y"=> ColorCode.sameAxis V.F d
local notation "B"=> wings G
-- native oil weights diagonal expense factor; z^d tangent formal not using at s. d-basis.
def rateV (i:Owner G d)(j:Glyph (wings G) d) :ℂ:= factorEF sx d j.size * oil (P.fees d i) j n sm
lemma rate_real (i:Owner G d)(j:Glyph (wings G) d) : star (rateV P sx sm n i j)=rateV P sx sm n i j:= by simp [rateV,factorEF,oil]
def loadAt (i:Owner G d) := factory (T:=V) (rateV P sx sm n i)
def binder (i:Glyph (wings G) d): E F d:= up F ( not_under i ) (loadAt V P sx sm n i.2)
def bareD (d:ℕ) : Module.End ℂ (E F d) := (sameAxis V.F d).constr ℂ (binder V P sx sm n)
lemma D_pane (i: Glyph (wings G) d) : bareD V P sx sm n d (Y i)= up F ( not_under i ) (loadAt V (d:=i.size) P sx sm n i.2):=(sameAxis ..).constr_basis ..
lemma D_own (i: Owner G d) : bareD V P sx sm n d (Y (Land.read i))= loadAt V P sx sm n i:= by rw [D_pane]; change up F (le_refl d) _=_; rw [up_same]; rfl
lemma D_link (h:r≤d) (v:E F r): bareD V P sx sm n d (up F h v)=up F h (bareD V P sx sm n r v):= by
    apply LinearMap.congr_fun (f:= bareD V P sx sm n d∘ₗ up F h) (g:= up F h ∘ₗ bareD V P sx sm n r); apply (sameAxis V.F r).ext; intro i; rw [LinearMap.comp_apply, LinearMap.comp_apply,same_up,D_pane,D_pane,up_mul ]; rfl
lemma loadWorth (i:Owner G d): loadAt V P sx sm n i= scalePolDiff F ( fun a=> factorEF sx d a.1 ) d ( Blaze.sketch V P d sm n i ):= by
    unfold loadAt Blaze.sketch Blaze.factory; rw [map_sum ]; apply Finset.sum_congr rfl; intro j _; rw [map_smul,rateV,mul_smul ]; have he : scalePolDiff F (fun a=> factorEF sx d a.1) d (Y j)=factorEF sx d j.size • Y j:= physical_inj F ( by rw [ scalePol_physical,map_smul ]; exact scalePol_pure F ( fun a=>factorEF sx d a.1 ) (RawLabels.physicalLabel F d (Y j)) (graded F j) (m:=(j.size,j.grade)) ); rw [he,smul_comm]
lemma D_turn (H: ExactSpin V P)(s:Signed)(v:E F d): bareD V P sx sm n d (spin F s.ortho d v)=spin F s.ortho d (bareD V P sx sm n d v):= by
    have he {d:ℕ} (i: Owner G d) : bareD V P sx sm n d (spin F s.ortho d (sameAxis F d (Land.read i)))=spin F s.ortho d (loadAt V P sx sm n i):= by
       let C (t:E F d):= scalePolDiff F ( fun a=> factorEF sx d a.1 ) d t
       rw [owners,map_sum ]; simp_rw [ map_smul,D_own,loadWorth ]; unfold ColorCode.spin; rw [ PositionX.scalePol_spin ];
       have hq := H.legal s d i sm n; change Extra.FD.rideO F s.ortho d (Blaze.sketch V P d sm n i)=_ at hq; rw [hq,map_sum ]; refine Finset.sum_congr rfl fun j _=>?_ ; let f:= ColorCode.fee F s.ortho d i j; rw [show (scalePolDiff F (fun a=>factorEF sx d a.1) d) ( f • Blaze.sketch V P d sm n j )= f • C (Blaze.sketch V P d sm n j) from LinearMap.map_smul_of_tower .. ]; exact Eq.symm (RCLike.real_smul_eq_coe_smul (K:=ℂ) f (C _))
    apply LinearMap.congr_fun (f:= bareD V P sx sm n d ∘ₗ (spin F s.ortho d).toLinearMap) (g:= (spin F s.ortho d).toLinearMap ∘ₗ bareD V P sx sm n d ); apply (Y).ext; intro i; let a := Land.read (d:=i.size) i.2 ( «B» := wings G ); let L:=sameAxis F i.size a;
    change bareD V P sx sm n d ( Extra.FD.rideO F s.ortho d (Y i))=Extra.FD.rideO F s.ortho d (bareD V P sx sm n d (Y i)); have hv:Y i=up F (not_under i) L:= (same_up V.F (not_under i) a).symm; rw [hv, up_signed, D_link, D_link, up_signed, show bareD V P sx sm n i.size L=_ from D_own V P sx sm n i.2 ]; exact congr_arg _ ( he i.2 )
lemma D_real (v:E F d) : bareD V P sx sm n d ((Model F).conj (hierarchy F).spin d v)= (Model F).conj (hierarchy F).spin d ( bareD V P sx sm n d v ):= by
   let B':=Y; let P' t := (Model F).conj (hierarchy F).spin t; let D := bareD V P sx sm n d;
   change D (P' _ v)= P' _ (D v); rw [ ← B'.sum_repr v,map_sum,map_sum, map_sum,map_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ;
   simp only [B',P',map_smulₛₗ,conj_basisX,D,D_pane,up_conj ]; unfold loadAt Blaze.factory; simp_rw [ map_sum,map_smulₛₗ,conj_basisX,show ∀ j: Glyph B i.size, starRingEnd ℂ _ = _ from fun j=> rate_real P sx sm n (d:=i.size) i.2 j ]; rfl 
lemma D_unit (H: Trusted P) (d:ℕ): bareD V P sx sm n d ((Model F).unit d)= if n=0 then (Model F).unit d else 0:= by
   suffices hu: ∀ v:E F 0,bareD V P sx sm n 0 v= (if n=0 then v else 0) from ?_; · rw [← up_unit F (Nat.zero_le d), D_link, hu,apply_ite (up F (Nat.zero_le d)),map_zero];
   have h0 (i:Glyph B 0):= tip0 i; have hN (i:Glyph B 0): i.size=0:= Nat.eq_zero_of_le_zero (not_under i); let W:= sameAxis F 0; have he (i:Glyph B 0): bareD V P sx sm n 0 (W i)= if n=0 then W i else 0:= by
       obtain ⟨j,rfl⟩:= owner_exists 0 i (hN i); unfold W; rw [D_own]; unfold loadAt Blaze.factory; simp_rw [rateV,H.unit j,sign_p, factorEF, hN _,pow_zero,inv_one,one_mul ]; by_cases h:n=0 <;> simp [h]
   intro v; rw [← W.sum_repr v,map_sum]; simp_rw [map_smul,he]; by_cases h:n=0 <;> simp [h]
local notation "E0"=> LinearMap.id (R:=ℂ) (M:=E F d) -- conflict M
-- express subtraction by coefficient at n=0.Def
abbrev topD (κ : Labels.Frames G)(d n:ℕ): Module.End ℂ (E κ d):= if n=0 then 1 else 0
def projectionD (d:ℕ) : Module.End ℂ (E F d):= bareD V P sx sm n d-topD F d n
def bareReset (HI:ExactSpin V P)(H:Trusted P)(d:ℕ): Buffer F d := let A:= projectionD V P sx sm n d; ⟨ (A.restrictScalars ℝ).toContinuousLinearMap, by
    have hh(p): A p=bareD V P sx sm n d p - ( if n=0 then p else 0 ):= by unfold A projectionD topD; split <;> rfl
    refine ⟨?_, fun s hs p hp=> ?_, fun p=> ?_, fun s p=> ?_, map_smul A _ ⟩
    · change A _ =_; rw [hh, D_unit V P sx sm n H, sub_self ]
    · rw [up_pre F hs.le] at hp; obtain ⟨q,rfl⟩:=hp; change A (up F hs.le q)∈ _; rw [hh]; apply (lower F s d).sub_mem;
      · rw [D_link, up_pre F hs.le ]; exact ⟨_,rfl⟩
      split; rw [up_pre F hs.le]; exact ⟨q,rfl⟩; exact Submodule.zero_mem _
    · change _= A _; rw [ show ((A.restrictScalars ℝ).toContinuousLinearMap) p=A p from rfl, hh, map_sub,← D_real,hh ]; split <;> try simp [*]
    change _ = A _; rw [show ((A.restrictScalars ℝ).toContinuousLinearMap) p=A p from rfl, hh,map_sub, ← D_turn V P sx sm n HI s p, hh,apply_ite (Extra.FD.rideO F s.ortho d),map_zero ] ⟩

def frameWord (κ:Labels.Frames G) {d:ℕ}(u:ℕ→ Buffer κ d)(n:ℕ) : Module.End ℂ (E κ d):= bufferL κ (u n)+topD κ d n
lemma frame_projects (H:ExactSpin V P)(HI:Trusted P) (d n:ℕ) : frameWord F ( fun i=> bareReset V P sx sm i H HI d ) n=bareD V P sx sm n d := by
   unfold frameWord; rw [show bufferL F _= projectionD V P sx sm n d from LinearMap.ext fun i=>rfl]; unfold projectionD; rw [sub_add_cancel ]
lemma frame_at (κ:Labels.Frames G) (u:ℕ→ Buffer κ d)(k:ℕ)(p:E κ d) : frameWord κ u k p= (u k).val p + ( if k=0 then p else 0 ):= by
   unfold frameWord topD; split <;> rfl
lemma frame_zero (κ:Labels.Frames G) (u:ℕ→ Buffer κ d): frameWord κ u 0=frameC κ (u 0) := by
   apply LinearMap.ext; intro p; rw [frame_at, if_pos rfl ]; change _= p + _; rw [add_comm]; rfl
lemma frame_ζ (u: Buffer F d) : (Pert.Position.motor F u).toLinearMap= (frameC F u).restrictScalars ℝ := rfl -- structure equality?
-- zoom commute
lemma collective (U:ExactSpin V P)(h:Trusted P)(hp:r≤d): zoomL F hp (bareReset V P sx sm n U h d)= bareReset V P sx sm n U h r:= by
   ext1; apply ContinuousLinearMap.ext; intro v; apply up_inj F hp; rw [zoomL_eq ];
   let Z(d):= projectionD V P sx sm n d; change Z d (up F hp v)=up F hp (Z r v); rw [show Z d (up F hp v)= _ from rfl]; unfold Z projectionD; rw [ LinearMap.sub_apply,D_link,LinearMap.sub_apply,map_sub, topD, topD ]; split; rfl; simp
-- D0 unipotent. needed to handle coordinate uniqueness.T.No compact control assumption
local notation "Δ"=> projectionD V P sx sm 0
lemma nil_slots' (hx:sx≠0)(i: Owner G d): Δ d (Y (Land.read i))= ∑ j∈ Finset.univ.erase (Land.read i),(rateV P sx sm 0 i j ) • Y j:= by
    unfold projectionD; rw [ LinearMap.sub_apply, D_own ]; unfold loadAt Blaze.factory; let v:= Land.read i;
    have he (j: Glyph B d)(h:v.grade≤j.grade): oil (P.fees d i) j 0 sm= if j=v then 1 else 0:= by unfold oil; rw [(P.init d i).Single j h]; split; simp [*]; simp [*]
    have hm : rateV P sx sm 0 i v=1:= by
       rw [ rateV, he v (le_refl _), if_pos rfl, mul_one ]; unfold factorEF; exact inv_mul_cancel₀ (pow_ne_zero d (by exact_mod_cast hx))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), hm,one_smul ]; change _-Y v=_; exact add_sub_cancel_left ..
private lemma volatility (p:Owner G d)(j:Glyph B d) (hj:(Land.read p).grade ≤ j.grade)(he:j≠Land.read p) : rateV P sx sm 0 p j=0:= by rw [rateV,oil,(P.init d p).Single j hj,if_neg he,Polynomial.eval_zero,Complex.ofReal_zero,mul_zero]
lemma nil_slots (hx:sx≠0)(m:ℕ)(i: Glyph (wings G) d)(H:i.grade < m): (Δ d^m) (Y i)=0 := by
    induction m generalizing i d with
    | zero=> omega
    | succ m ih=>
       let g:=not_under i; let v:Owner G i.size:= i.2; let p:= Land.read v; let f t:= projectionD V P sx sm 0 t;
       have he : sameAxis V.F d i=up F g (sameAxis F _ p):=(same_up V.F g p).symm
       rw [pow_succ, Module.End.mul_apply, he, show projectionD V _ _ _ 0 d (up F (not_under i) _)=up F g (f i.size (sameAxis F i.size p)) from ?_, show f i.size _=_ from nil_slots' V P sx sm hx v]; swap; · unfold f projectionD; simp [topD,D_link] -- proof
       simp_rw [ map_sum,map_smul, same_up ]; refine Finset.sum_eq_zero fun j h=>?_ ; by_cases hl:j.grade < m; · rw [ ih (d:=d) (includeI _ _ _) hl,smul_zero]
       rw [volatility P sx sm v j (by have he:i.grade=(Land.read v).grade:=rfl; omega) (Finset.ne_of_mem_erase h), zero_smul ]
lemma nilpotent (hx:sx≠0)(d:ℕ) : (Δ d ^ (d+1))=0 := by apply (sameAxis F d).ext; intro i; exact nil_slots V P sx sm hx _ i (Nat.lt_add_one_iff.mpr ( Glyph.memory i ))
lemma invertible (hx:sx≠0)(d:ℕ) : IsUnit (bareD V P sx sm 0 d):= by
    rw [show bareD V P sx sm 0 d=1+Δ d from ?_]; apply IsNilpotent.isUnit_one_add; exact ⟨d+1,nilpotent V P sx sm hx d⟩; unfold projectionD topD; rw [if_pos rfl]; abel
end YM.FVA2.Counterpart
