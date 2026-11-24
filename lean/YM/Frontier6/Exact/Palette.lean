import YM.Frontier6.Exact.Pulse

/-! Cumulative detector system on one real, O(4)-covariant splitting. Because
we may fix the splitting as part of this measurement scheme, we can make the
fixed-horizon detector recipes *nested* on every list of probe values. (Needn't
hold for independently chosen recipes.) This does not give any estimate
uniform over output horizons. As usual only use probes on their collar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Filter Set Spec Table Wilson Lattice
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) {d e w:ℕ}
set_option quotPrecheck false
local notation "J" => S.conj K.room.kernel.spin
local notation "R" => K.sector.turns.act
local notation "U" => K.sector.derivatives

/-- All detector probes through horizon d. -/
abbrev Palette (d:ℕ):= (i:Fin (d+1)) → (hand K i.val).Pulse K -- check order

def plain (d:ℕ): Palette K d →L[ℂ] (hand K d).Pulse K := ContinuousLinearMap.proj (Fin.last d)
def previous (h:e ≤ d): Palette K d →L[ℂ] Palette K e:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (Fin.castLE (Nat.succ_le_succ h) i)
lemma previous_refl (x:Palette K d): previous K le_rfl x=x:=rfl
lemma previous_paths (he:w ≤ e)(hd:e ≤ d)(x:Palette K d): previous K he (previous K hd x)=previous K (he.trans hd) x:=rfl

def higher (h:e ≤ d): S.Field e →L[ℂ] S.Field d:=LinearMap.toContinuousLinearMap ((U).rise h)
def reaches (e d:ℕ): S.Field d →L[ℂ] Palette K e := ContinuousLinearMap.pi fun i=> (hand K i.val).echo K _
lemma previous_reaches (he:e ≤ d)(x:S.Field w): previous K he (reaches K d w x)=reaches K e w x:= rfl
lemma reaches_at (x:S.Field e) (i:Fin (d+1))(p:(hand K i.val).list)(b:Bool)(g:Ortho):
  (reaches K d e x i p b g)=((p.val.flip K b).roll K g).form K none e x:= rfl
lemma form_rises (p:Probe S)(s:StateIndex K)(he:e ≤ d)(x:S.Field e): p.form K s d (higher K he x)=p.form K s e x:=by
  change reading _ _ _ _ _ _ _=reading _ _ _ _ _ _ _; rw [reads_at,reads_at]; exact (inception K s).kernels he x p.clear _
lemma reaches_rise (x:S.Field e)(he:e ≤ d)(w:ℕ): reaches K w d (higher K he x)=reaches K w e x:=funext fun i=> funext fun p=> funext fun b=> ContinuousMap.ext fun g=> form_rises K ((p.val.flip K b).roll K g) none he x
lemma higher_pass (he:w ≤ e)(hd:e ≤ d)(x:S.Field w):higher K hd (higher K he x)=higher K (he.trans hd) x:= (U).transit K.room.kernel.laws.toSymmetric K.phase.transport.injection he hd x
lemma higher_fix (x:S.Field e):higher K le_rfl x=x:= (U).arrival K.room.kernel.laws.toSymmetric K.phase.transport.injection x

def singleFit (d:ℕ): Palette K d →L[ℂ] S.Field d:= surround K d _ ∘L plain K d
lemma single_fit (x:S.Field d): singleFit K d (reaches K d d x)=x:= surrounds K d _ x

/-- Correct the single-orbit fit into the previous detector's kernel. -/
def detector : (d:ℕ)→ Palette K d →L[ℂ] S.Field d
 | 0=> singleFit K 0
 | d+1=>
   let x:= detector d
   let y:= singleFit K (d+1)
   y + (higher K (Nat.le_succ d)) ∘L x ∘L (previous K (Nat.le_succ d) - (reaches K d (d+1)) ∘L y)

lemma detector_hop (x:Palette K (d+1)): detector K (d+1) x=singleFit K (d+1) x + higher K (Nat.le_succ d) (detector K d (previous K (Nat.le_succ d) x-reaches K d (d+1) (singleFit K (d+1) x))):=by rw [detector]; rfl
lemma detector_field (x:S.Field d): detector K d (reaches K d d x)=x:=by
  cases d with
  | zero=> exact single_fit ..
  | succ d=> rw [detector_hop,single_fit,previous_reaches]; simp

/-- Intrinsic lower projection (works on *any* field position identified
with that horizon, not the arbitrary reference representatives). -/
def projectBelow (h:e ≤ d): S.Field d →L[ℂ] S.Field e:= detector K e ∘L reaches K e d
lemma projects_at (h:e ≤ d)(x:S.Field d): projectBelow K h x = detector K e (reaches K e d x):= rfl
lemma projects_short (h:e ≤ d)(x:Palette K d): projectBelow K h (detector K d x)=detector K e (previous K h x):=by
  induction d,h using Nat.le_induction with -- x generalize auto
  | base=> exact detector_field ..
  | succ d hd ih=>
    let y := singleFit K (d+1) x
    let z := previous K (Nat.le_succ d) x
    let v:= reaches K d (d+1) y
    rw [projects_at,detector_hop,map_add,reaches_rise,map_add,← projects_at K hd,ih,map_sub,← previous_paths K hd (Nat.le_succ d) x,previous_reaches K hd,map_sub]; abel
lemma projects_fix (h:e ≤ d)(x:S.Field e): projectBelow K h (higher K h x)=x:=by rw [projects_at,reaches_rise,detector_field]
lemma projects_self (x:S.Field d): projectBelow K le_rfl x=x:= detector_field K x
lemma projects_comp (h:w ≤ e)(hi:e ≤ d)(x:S.Field d): projectBelow K h (projectBelow K hi x)=projectBelow K (h.trans hi) x:=by rw [projects_at K hi, projects_short,previous_reaches,projects_at]
lemma projects_arrive (h:w ≤ e)(hd:e ≤ d)(x:S.Field e) : projectBelow K (h.trans hd) (higher K hd x)=projectBelow K h x:=by rw [projects_at,reaches_rise,projects_at]

/-- Pure-weight endoprojection. -/
def weight : (d:ℕ) → S.Field d →L[ℂ] S.Field d
 | 0=> ContinuousLinearMap.id ℂ _
 | d+1=> ContinuousLinearMap.id ℂ _ - higher K (Nat.le_succ d) ∘L projectBelow K (Nat.le_succ d)
/-- Range as subtype for grade-by-grade operations and change of basis. -/
def Grade (d:ℕ): Submodule ℂ (S.Field d):= LinearMap.range (weight K d).toLinearMap
lemma weight_up (x:S.Field (d+1)): weight K (d+1) x=x-higher K (Nat.le_succ d) (projectBelow K (Nat.le_succ d) x):=rfl
lemma weight_idem (x:S.Field d): weight K d (weight K d x)=weight K d x:=by cases d with
 | zero=> rfl
 | succ d=> rw [weight_up K (weight K _ x),weight_up, map_sub,projects_fix]; simp
lemma weight_space (x:S.Field d): x∈Grade K d ↔ weight K d x=x:=by
  constructor; rintro ⟨w,rfl⟩; exact weight_idem K _; intro he; exact ⟨_,he⟩
lemma grade_zero (x:S.Field 0): x∈ Grade K 0:= (weight_space ..).mpr rfl
lemma projects_pure (h:e<d)(x:S.Field d) : projectBelow K h.le (weight K d x)=0:=by
   cases d with
   | zero=> omega
   | succ d=>
     have he:e ≤ d:=by omega
     rw [← projects_comp K he (Nat.le_succ d),weight_up,map_sub,projects_fix,sub_self,map_zero]
lemma weight_away (x:S.Field e)(h:e < d) : weight K d (higher K h.le x)=0:=by
   cases d with
   | zero=> omega
   | succ d=>
     rw [weight_up,← higher_pass K (show e ≤ d by omega) (Nat.le_succ d) x,projects_fix,sub_self]
lemma weights_span (x:S.Field d):
   ∑ i:Fin (d+1), higher K (show i.val ≤ d by have:=i.isLt; omega) (weight K i (projectBelow K (show i.val≤d by have:= i.isLt; omega) x))=x:=by
   induction d with
   | zero=> rw [Fin.sum_univ_one]; change higher K le_rfl (projectBelow K le_rfl x)=_; rw [higher_fix, projects_self]
   | succ d ih=>
     rw [Fin.sum_univ_castSucc];
     let X:= projectBelow K (Nat.le_succ d) x; let V:= higher K (Nat.le_succ d)
     let a (i:Fin (d+1)):= higher K (show i.val ≤ d by have:=i.isLt; omega) (weight K i (projectBelow K (show i.val≤d by have:= i.isLt; omega) X))
     have ht(i:Fin (d+1)): a i=a i:= rfl
     have hv:= ih X
     -- each summand at castSucc is ...
     rw [Finset.sum_congr rfl (g:=fun i:Fin (d+1)=> V (a i)) (fun i _ => ?_),← map_sum,hv]
     · change V X+higher K le_rfl (weight K (d+1) (projectBelow K le_rfl x))=_; rw [projects_self,higher_fix,weight_up]; change V X + (x - V X)=x; abel
     unfold V a X; rw [higher_pass, projects_comp]; rfl

def orbiting (u:Ortho) (x:Palette K d):Palette K d:= fun i=> leftPulse K _ _ u (x i)
def starring (x:Palette K d): Palette K d:=fun i=> flipPulse K _ _ (x i)
lemma single_orbit (u:Ortho) (x:Palette K d): singleFit K d (orbiting K u x)=(R) d u (singleFit K d x):= surround_left K d _ u _
lemma single_star (x:Palette K d): singleFit K d (starring K x)=(J) d (singleFit K d x):= surround_flip K _ _ _
lemma reaches_orbit (u:Ortho)(x:S.Field d)(e:ℕ): orbiting K u (reaches K e d x)=reaches K e d ((R) d u x):= funext fun i=> echo_left K _ _ u x
lemma reaches_star (x:S.Field d)(e:ℕ): starring K (reaches K e d x)=reaches K e d ((J) d x):= funext fun i=> echo_flip ..
lemma previous_orbit (u:Ortho)(x:Palette K d)(h:e≤d):previous K h (orbiting K u x)=orbiting K u (previous K h x):=rfl
lemma previous_star (x:Palette K d)(h:e≤d):previous K h (starring K x)=starring K (previous K h x):=rfl
lemma orbiting_sub (u:Ortho)(x y:Palette K d): orbiting K u (x-y)=orbiting K u x - orbiting K u y:= rfl
lemma starring_sub (x y:Palette K d): starring K (x-y)=starring K x-starring K y:= by
    ext1 i; ext1 p; ext1 b; exact star_sub (x i p (!b)) (y i p (!b))
lemma higher_orbit (u:Ortho)(x:S.Field d)(h:d≤e): higher K h ((R) d u x)=(R) e u (higher K h x):= (K.phase.transport.spots.filtered d e h u x).symm
lemma higher_star (x:S.Field d)(h:d≤e): higher K h ((J) d x)=(J) e (higher K h x):= (K.phase.transport.rights.realInc h x).symm
lemma detector_orbit (u:Ortho)(x:Palette K d): detector K d (orbiting K u x)= (R) d u (detector K d x):=by
   induction d with
   | zero=>exact single_orbit ..
   | succ d ih=>rw [detector_hop,detector_hop,single_orbit,previous_orbit,← reaches_orbit,← orbiting_sub,ih,map_add,higher_orbit]
lemma detector_star (x:Palette K d): detector K d (starring K x)= (J) d (detector K d x):=by
   induction d with
   | zero=>exact single_star ..
   | succ d ih=>rw [detector_hop,detector_hop,single_star,previous_star,← reaches_star,← starring_sub,ih,map_add,higher_star]
lemma projection_orbit (u:Ortho)(x:S.Field d)(h:e≤d): projectBelow K h ((R) d u x)= (R) e u (projectBelow K h x):=by rw [projects_at,projects_at,← reaches_orbit,detector_orbit]
lemma projection_star (x:S.Field d)(h:e≤d): projectBelow K h ((J) d x)= (J) e (projectBelow K h x):=by rw [projects_at,projects_at,← reaches_star,detector_star]
lemma weight_orbit (u:Ortho)(x:S.Field d): weight K d ((R) d u x)= (R) d u (weight K d x):=by cases d with
 | zero=>rfl
 | succ d=>rw [weight_up,weight_up,projection_orbit,higher_orbit,map_sub]
lemma weight_star (x:S.Field d): weight K d ((J) d x)= (J) d (weight K d x):=by cases d with
 | zero=>rfl
 | succ d=>rw [weight_up,weight_up,projection_star,higher_star,map_sub]
end YM.Frontier6
