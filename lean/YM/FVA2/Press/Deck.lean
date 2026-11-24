import YM.MS.Theater.Horizon
import YM.XSpace.OnShell
/-! The graded insertion basis for the continuum graph sum uses the fixed real
equivariant Maxwell section and the complement of the null polynomial sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Labels XSpace
open MS MS.Local.Physical MS.Lifting MS.Theater
open Maxwell Maxwell.Free
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ}
local notation "P" => Labels.Pol G
local notation "W" => WickPol G
local notation "µ" => On.lifting
-- needed transfer through real structures: before mixing any labels
variable {v : Labels.Pol G} {w r:ℕ}
private lemma lift_cast (h:v∈ Labels.invariantSpace G)(hx:v∈ Labels.limited G w): µ (reduceEq v)∈ Labels.invariantSpace G:= by
 let V: Labels.Label G w:=⟨v,hx,h⟩; let v' := observable G w V; exact (On.fits (⟨v', ⟨V,rfl⟩⟩: shellSector G w)).2
lemma lower_real (p:P)(h:Labels.conjPol p=p) : realForm (reduceEq p)= reduceEq p:= by
    apply equalPol; intro v; rw [real_eval,jet_value]; exact (Labels.conj_value p _).symm.trans (by rw [h])
lemma re_grade (p:P)(h:Theater.At p (w,r)) : MvPolynomial.IsWeightedHomogeneous Free.bwt (reduceEq p) (w,r) := by
    let t:= biasW G (w,r); have hp: t (reduceEq p)=reduceEq p:= by change _=reduceEq p; exact ( Free.commuting Labels.bidegree _ reduceEq ( Free.reduce_grade fun i=> ( i+2,(1:ℕ) ) ) p (w,r) ).trans ( congr_arg reduceEq ((Theater.nodeId p _|>.mp h).weightedHomogeneousComponent_same ))
    rw [← hp]; exact MvPolynomial.weightedHomogeneousComponent_mem ..

def refineF (G:Gauge)(w r:ℕ) : Film0 G w r→ₗ[ℝ] Film0 G w r:=
 (( On.lifting.toLinearMap.restrictScalars ℝ ) ∘ₗ (stageM G w r)).codRestrict (Film0 G w r) fun p=> by
    obtain ⟨ht,h,hv⟩:= (cinema p.val).mp p.property; apply (cinema _).mpr
    let z:shellSector G w:=⟨reduceEq p.val, ⟨⟨p.val,limitH ht,h⟩,rfl⟩⟩
    refine ⟨ (pure_grade ..).mp ( On.section_grade z (re_grade p.val ht) ), lift_cast h (limitH ht),?_⟩
    change Labels.conjPol (On.lifting (reduceEq p.val))= _; rw [← On.lift_conj,lower_real p.val hv]; rfl
lemma fixedR (x:Film0 G w r) : ((refineF G w r) x).val= µ (reduceEq x.val):=rfl

-- range in Ambient Law. Can use rank lift per word; no non-unit scalings at this step.
local notation "A" => Allowed G w r
local notation "N" => Null G w r
local notation "γ" => Theater.orbit G
def born (G:Gauge) (w r:ℕ):= LinearMap.range (((Allowed G w r).subtype ∘ₗ over0 G w r) ∘ₗ refineF G w r)
local notation "B" => born G w r
lemma born_on {x} (h:x∈born G w r): x∈ Allowed G w r:= by obtain ⟨y,rfl⟩:=h; exact ((over0 G w r) ((refineF G w r) y)).property
lemma born_root : B ⊔ N=A:= by
    apply le_antisymm (sup_le (fun x h=> born_on h) (null_subset G)); intro x hx; obtain ⟨p,hp,hP⟩:= Theater.chooseX hx; let y:Film0 G w r:= ⟨p,hp⟩; set P':= (refineF G w r) y; set a:= γ P'.val; have ha : a∈ born G w r:= ⟨y,rfl⟩; have hS:x-a=γ (y-P').val:= by rw [← hP, Submodule.coe_sub,map_sub]
    refine Submodule.mem_sup.mpr ⟨a,ha,x-a,?_ ,by abel⟩; rw [hS]; apply (certN (h:=w) (r:=r) ?_ (?_)).mpr; swap; exact ((cinema _).mp (y-P').property).1
    · change reduceEq (y.val-P'.val)=0; rw [map_sub,show P'.val= _ from fixedR y, On.lift_recover,sub_self]
    exact (show (γ (y-P').val) ∈ Allowed G w r from (show γ _∈ Allowed G w r ∧ _ from (y-P').property).1)
lemma integrity : Disjoint B N:= by
    apply disjoint_iff.mpr; apply bot_unique; rintro x ⟨h,k⟩; obtain ⟨p,hp⟩:= (show x∈ born G w r from h); let f:= refineF G w r p; let y:=f.val; have ht:y∈Film0 G w r:= f.property; obtain he:= (certN (h:=w) (r:=r) ((cinema _).mp ht).1 (hp.symm ▸ (born_on (w:=w) (r:=r) h) : γ y∈ Allowed G w r)).mp (show γ y∈ Null G w r from hp.symm ▸ k)
    refine (Submodule.mem_bot ℝ).mpr ?_; change γ y=x at hp; rw [← hp, show y=0 from ?_,map_zero]; exact ((congr_arg On.lifting (show reduceEq p.val=0 from (On.lift_recover _).symm.trans he)).trans (map_zero _))
/-- Nonnegative weight ports specific; inherit Deck from any choice in irrelevant negative weights. -/
def portDeck (G:Gauge): Deck G:= let B':= Classical.choice (Deck.setting G)
 {
   carries:= fun x k=> if h:x≥0 then born G x.toNat k else B'.carries x k
   sup:= by intro x k; by_cases h':0≤x; swap; · rw [dif_neg h']; exact B'.sup ..
            lift x to ℕ using h'; rw [dif_pos (Nat.cast_nonneg x)]; exact born_root (G:=G) (w:=x)
   disjoint:= by
      intro x k; by_cases h':0≤x; swap; · rw [dif_neg h']; exact B'.disjoint ..
      lift x to ℕ using h'; rw [dif_pos (Nat.cast_nonneg x)]; exact integrity (G:=G) (w:=x) }
end YM.FVA2.Press
