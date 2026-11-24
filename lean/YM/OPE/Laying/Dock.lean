import YM.OPE.Laying.Ruling
/-!
# Docking all purchases of one season

Only consumes per-event resources. Ordering of slots arbitrary, epochs of
untouched tickets can reach well below the current landing. Land perfectly
centered for rolling through long gaps.Need identical layout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T :ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V}{A:Fibers I J} {s:Ward (Names V I)} {s':Ward (Names V J)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)} {z:Finset J}
variable (S:Ledger Θ (j+1) (pullback A s') F P u φ W₀ x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))

/- Interruption plan. indices pre-Th LAND at i+1, starts j+1,
all awaken where due; room in repetitions sufficient. Capture still
inside Runner or private collapse later. -/
structure Release (Θ:Playout C.path p b N V) (A:Fibers I J)(z:Finset J)(s':Ward (Names V J))(i j:ℕ) (L:LogPackage C W r D) (φ:I→ℕ)(u:∀ i:ℕ,I→ Site (C.side i p)) : Prop where
    game : Trial s'
    funded : C.ref 0 < b
    beginning : b ≤ i
    prep : i+1 < j
    lights : ∀ k∈z,A.Solo k
    sleeper k:A.bunch k ∈ z → φ k ≤ i
    prompt k:A.bunch k ∉ z→ φ k=j
    clearances k : i ≤ k → k ≤ j → Θ.occupied (r k) (u k) ∧ Θ.occupied (r k) (u (k+1))
    site k: i+1 ≤ k→k ≤ j → ∀ x y:V×I, Drapery.room (pullback A s') x y → (partialGroup V A).bunch x ≠ (partialGroup V A).bunch y → let f:=Θ.spectrum k (u k); (C.path.levels.budget k).B*meter L k ≤ separation (f x) (f y)
    even x y:A.bunch x=A.bunch y→ u (i+1) x=u (i+1) y
    hope k:k∉z→ u (i+1) (A.twig k)=(C.path.levels.clock.op i p).ratio.embed (u i (A.twig k))

def peer (L:LogPackage C W r D) (T j:ℕ) := η₀ j * lamina L T j /8
lemma peer_paid (hG:G.Simple)(h:0 < T)(he:i≤j) : let x:=peer L T j; 0<x∧x≤1 ∧ 8*x ≤ η₀ i*license C.path δ₀ T (meter L i+2) i :=by
    intro x; let t:ℝ:= η₀ j; have hp:1 < (Y).clock.hatBeta (j+1):=(Y).fits.delayed _; have he':0 < t:= inv_pos.mpr (zero_lt_one.trans hp)
    have ht':0<t* lamina L T j:=mul_pos he' (laminaPos L h j); have ht:t≤1:= inv_le_one_of_one_le₀ hp.le; have hψ:= ht'.le
    refine ⟨div_pos ht' (by norm_num),(div_le_self hψ (by norm_num)).trans ((mul_le_of_le_one_left (laminaPos L h j|>.le) ht).trans (lamina_le L h _)),?_⟩
    unfold x peer; rw [show (8:ℝ)*(η₀ j*lamina L T j/8)=_ from (by ring : (8:ℝ)*(η₀ j*lamina L T j/8)=t*lamina L T j)] -- t abbrev ring may fail
    exact mul_le_mul (nearAnti hG he) (laminaAnti L hG _ h he) (laminaPos L h _|>.le) (L.system.costs.stay.water i (Nat.zero_le i)|>.1.le)
variable (U:Release Θ A z s' i j L φ u)
local notation "a!"=> peer L T j
include h U S
lemma Release.schedule (hG:G.Simple)(hT:Fintype.card I ≤ T)(h':0<T): Season Θ (i+1) j δ₀ L.trace L.token (meter L) η₀ r A z u s' T (lifted W₀ x) a! D P:=by
    let X':=lifted W₀ x; have hf:= S.clock.scaleRight S.rate.1; have hl:= U.prep; have hk:= U.beginning; have ht:= L.guide h U.funded.le; have hL:j<N:= S.limit; have hc:= peer_paid (L:=L) hG h' (le_refl j)
    refine ⟨ht,hk.trans i.le_succ,hl,hL,h',hT,⟨hc.1,hc.2.1⟩,U.game,U.lights,fun iφ he h=> S.slots iφ (by omega) (by omega), fun k he hv=> U.clearances k (by omega) hv, U.site, fun k he hv=>?_,U.even,fun k hk _ t=> hf.ready t k,fun i' _ _ t=> hf.paid t i',fun k he hv t hp=> ?_,fun k=>?_,fun k hh=>?_⟩
    · have hk':=peer_paid L hG h' hv; have hz:=U.funded; refine ⟨hk'.2.2,lamina_le L h' k,L.clusters (by omega),L.contact (by omega) (by omega) p,L.lightWalk p (by omega) _⟩ -- contact arg order
    · exact (hf.early t k (by rw [U.prompt t hp]; exact hv.le)).trans (hf.early t (k+1) (by rw [U.prompt t hp]; exact hv)).symm
    · refine (S.progress k).follows j ?_ j.lt_succ_self; by_cases he:A.bunch k∈z; exact (U.sleeper k he).trans (Nat.le_of_succ_le hl.le); exact (U.prompt k he).le
    exact (S.progress k).within ((U.sleeper k hh).trans i.le_succ) le_rfl (fun _ _ _=>(hf.ready ..).le) (fun _ _ _=>le_rfl) -- `k`? Season.staying i old name. edit

-- funding thaw formula
omit h U S
local notation "α'"=> (cell C.path (i+1) j (T+2) a! x)
def lineRelease (A:Fibers I J)(W:I→ℝ)(v:J):=∏ i∈A.contents v,W i
lemma budget_release {F:I→ℝ}(T:ℕ)(hT:0<T)(h:Fintype.card I ≤ T)(hp:0<α)(hq:α≤1)(hx:0<x)(ht:x≤1)(hi:i≤j)(he:∀ i,0<F i)(y:J)(A:Fibers I J): cell C.path i j (T+2) α x ^T * lineRelease A F y ≤ Lecture.bill C.path i j (T+2) α (fun i=> x*F i) A y:=by
    let u:= cell C.path i j (T+2) α x; have hK:0 < u:= cell_pos hp hx; have hu:u≤1:=by unfold u cell; refine mul_le_one₀ (mul_le_one₀ ?_ (pow_nonneg hp.le _) (pow_le_one₀ hp.le hq)) hx.le ht; have h':= Schedule.a_pos C.S i; exact pow_le_one₀ (by have hz:=Schedule.a_pos C.S j; positivity) ((div_le_one h').2 ((C.S.strictAnti.antitone hi)))
    have he':∀ i',cell C.path i j (T+2) α (x*F i')=u*F i':= fun _=> (mul_assoc ..).symm
    unfold Lecture.bill; simp_rw [he',prod_mul_distrib,prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hK.le hu ((card_le_card (subset_univ _)).trans (card_univ.trans_le h))) (prod_nonneg fun j _=> (he j).le)

include S h U
lemma Release.race (T:ℕ)(hG:G.Simple)(hT:Fintype.card I ≤ T)(h':0<T)(hx:0<x')(hf:x'≤ (cell C.path (i+1) j (T+2) (peer L T j) x)^T): let v:= (fun k=> x'* lineRelease A (W₀ (i+1)) k); ∃ F':J→Cup (C.path.rep N p (i+1)), Θ.Market s' (u (i+1)∘A.twig) F' (Θ.intention (grouped_X F A) (i+1) ((U.prep.trans_le (j.le_succ.trans S.limit)).le)) v (ν (i+1))∧ (∀ k:J,k∈z→ F' k=P (i+1) (A.twig k)) ∧ (∀ k∉z,Blade (Ξ (i+1)) (u (i+1) (A.twig k)) (F' k).home (F' k).leaves 0 (1/(2*v k))):=by -- i ≤ j?? needs U.prep.le then.Mat.
    intro v; have ht:= Release.schedule L h S U hG hT h'; obtain ⟨X,hX,hL,hK⟩:= Season.finishBudget F ht S.terms S.market; have hu(k):0<v k:=mul_pos hx (prod_pos fun i _=>S.clock.ready ..)
    have he: v ≤ Lecture.bill C.path (i+1) j (T+2) (peer L T j) (lifted W₀ x (i+1)) A:= fun k=> (mul_le_mul_of_nonneg_right hf ((prod_pos fun g _=>S.clock.ready g (i+1)).le)).trans (budget_release T h' hT ht.thaws.1 ht.thaws.2 S.rate.1 S.rate.2 U.prep.le (fun k=> S.clock.ready ..) k A) -- i capture typo parenth
    refine ⟨X,hX.shy Θ hu he le_rfl,hL,fun k hk=> (hK k hk).more (div_le_div_of_nonneg_left (by norm_num) (mul_pos zero_lt_two (hu k)) (by gcongr; exact he k))⟩
end YM.OPE.Log.Book
