import YM.FVA2.Position.Tourist
/-!
# The H action on the chosen physical label basis

One fixed convention for all shapes & scales. Prove the needed coherence in
any horizon restriction (actions within bidegrees -- weight/slot rank). As for
the kernels, watch the orientation of the action; we use right-composition there.
We don't postulate `Horder` of the fee polynomials. It's proved with this action
and additional results about orientation of the (specific) MS prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Axes
open Function Set Filter Finset
open MS MS.Plane MS.Arts MS.Arts.Spin MS.Landau MS.Landau.Detect MS.Momentum MS.Koszul
open MS.Outlook MS.Halo MS.Motif MS.Theater Labels MS.Local.Physical MS.Menus
open Brass Weft OpenAxis Press Maxwell Maxwell.Free
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n k:ℕ}{G:Gauge} (s t:Signed)
abbrev Panel (G:Gauge)(m k:ℕ):= ( Press.portDeck G ).carries m k
local notation "ι"=> Signed.inclusionO
local notation "U"=> Resume (Press.portDeck G) m k
lemma goose_p (p:Pol G)(h: At p (m,n)) (ht:p∈ Labels.invariantSpace G) : rotated s.ortho p∈ Labels.invariantSpace G:= by
    let V: Labels.Label G m:=⟨p,limitH h, ht⟩; exact (tensor (ι s) V).property.2
lemma goose_c (p:Pol G)(h: Labels.conjPol p=p): Labels.conjPol (rotated s.ortho p)=rotated s.ortho p:= by
    apply Labels.eval_ext; intro a; simp_rw [ Labels.conj_value, rotated, eval_changed, ← conj_value, h ]
lemma flies (v:Film0 G m k): rotated s.ortho v.val∈Film0 G m k:= by obtain ⟨ht,hv,h⟩:= (cinema _).mp v.property; exact (cinema _).mpr ⟨still _ ht,goose_p s _ ht hv,goose_c s _ h ⟩
def Beam (s:Signed)(G:Gauge)(m k:ℕ): Film0 G m k→ₗ[ℝ] Film0 G m k:= { toFun x:= ⟨rotated s.ortho x.val,flies s x⟩, map_add':=fun x y=> Subtype.ext (map_add (rotated s.ortho) x.val y.val), map_smul':=fun c x=>Subtype.ext (map_smul ((rotated s.ortho).toLinearMap.restrictScalars ℝ) c x.val) }
lemma winged (v:Film0 G m k): Beam s G m k (refineF G m k v)= refineF G m k (Beam s G m k v):= by
    let L:Labels.Label G m:= ⟨v.val,limitH (cinema _|>.mp v.property|>.1),cinema _|>.mp v.property|>.2.1⟩; refine Subtype.ext ?_; change rotated _ ( XSpace.On.lifting (reduceEq v.val))= _; rw [← XSpace.On.lift_signed, ← show reduceEq (rotated s.ortho v.val)= reflectPol s.ortho (reduceEq v.val) from Maxwell.Free.pulls_label L s.ortho ]; rfl
lemma core_t (p:Panel G m k): (Beam s G m k (U p))=refineF G m k (Beam s G m k (U p)):= by rw [ ← winged, Press.stageF ]

local notation "Ɵ"=> Theater.orbit G
local notation "V"=> Beam s G m k
def order (s:Signed)(G:Gauge)(m k:ℕ): ↥(Panel G m k) →ₗ[ℝ] Panel G m k:= ((( Allowed G m k ).subtype ∘ₗ Theater.over0 G m k ) ∘ₗ Beam s G m k ∘ₗ Theater.Resume (Press.portDeck G) m k ).codRestrict (Panel G m k) fun p=> by generalize h: ( (( Allowed G m k ).subtype ∘ₗ Theater.over0 G m k ) ∘ₗ Beam s G m k ∘ₗ Theater.Resume (Press.portDeck G) m k ) p=x; rw [Panel,level, ← h]; exact ⟨ Beam s G m k (Resume ( Press.portDeck G ) m k p),congr_arg (fun X:Film0 G m k=> Theater.orbit G X.val) (core_t s p).symm⟩
lemma kind (f:Pol G) : rotatedQ (s⁻¹) f= rotated s.ortho f:= by rw [rotated_id s⁻¹, show (s⁻¹).ortho=s.ortho⁻¹ from map_inv ι s, inv_inv]
lemma lineK (p: Panel G m k) : (order s G m k p).val= cash s⁻¹ 0 p.val := by
    change Ɵ (rotated s.ortho (U p).val)=_; rw [ ← honor (portDeck G) ( x:=p ), ← kind, ← stake, ← equivariant, stake ]
lemma identifies (p:Panel G m k): U ( order s G m k p )= V (U p):= (craftK G m k).injective (Subtype.ext (honor ( Press.portDeck G ) ( x:=order s G m k p))) -- defeq latter
local notation "Π"=> Panel G m k
lemma Mone (p:Panel G m k): order 1 G m k p=p:= by apply Subtype.ext; rw [lineK, inv_one, cash,tangent]; exact beam_e p.val
lemma Mlaw (p:Panel G m k): order (s*t) G m k p= order s G m k (order t G m k p):=by apply Subtype.ext; rw [lineK,lineK,lineK, mul_inv_rev,gatherH]
def billH (s:Signed)(G:Gauge)(m k:ℕ): ↥(Panel G m k) ≃ₗ[ℝ] Panel G m k:=
    { order s G m k with invFun:= order s⁻¹ G m k, left_inv:= by intro p; change order s⁻¹ G m k ( order s G m k p ) = _; rw [ ← Mlaw, inv_mul_cancel,Mone ], right_inv:= by intro p; change order s G m k ( order s⁻¹ G m k p )=_; rw [ ← Mlaw,mul_inv_cancel,Mone ] }
-- matrix conventions. basis from Resume.B. indices d,k.
-- IMPORTANT due to dimensional indexes etc. Explicit.
abbrev Case (G:Gauge)(m k:ℕ):= (Press.portDeck G).BIndex m k
abbrev baseH (G:Gauge)(m k:ℕ): Module.Basis (Case G m k) ℝ (Panel G m k):= Module.finBasis ℝ _
def markS (s:Signed)(G:Gauge)(m k:ℕ)(i j:Case G m k):ℝ:= (baseH G m k).coord j ( order s G m k (baseH G m k i))
local notation "ω"=> markS s G m k
local notation "BV"=> baseH G m k
lemma wraps (i: Case G m k) : order s G m k (BV i)= ∑ j:Case G m k,ω i j • BV j:= ( Module.Basis.sum_repr ( baseH G m k ) ( order s G m k (BV i) ) ).symm
lemma pack (i j:Case G m k) : markS (s*t) G m k i j=∑ l:Case G m k, markS t G m k i l * markS s G m k l j:= by unfold markS; rw [Mlaw]; nth_rw 1 [wraps t]; rw [map_sum,map_sum]; simp_rw [map_smul]; rfl -- omega
lemma start (i j:Case G m k): markS 1 G m k i j= if i=j then 1 else 0:= by unfold markS; rw [Mone]; by_cases t:i=j <;> simp [t ] -- 
lemma cast (i:Case G m k): rotated s.ortho (film ( Press.portDeck G ) i (h:=m) (r:=k)) = ∑ j:Case G m k,ω i j • film (Press.portDeck G) j (h:=m) (r:=k):= by
    have he:= (identifies s ( BV i )).symm; replace he:= congr_arg Subtype.val he; rw [wraps, map_sum, AddSubmonoidClass.coe_finsetSum] at he; simp_rw [map_smul, Submodule.coe_smul] at he; exact he
local notation "M"=> Press.portDeck G
lemma indigo_frame (i:Case G m k): reduceEq (film (M) i (h:=m) (r:=k))=(Indigo (M) m k i).val:= by rw [sees,Indigo,Module.Basis.map_apply]
lemma castV (i:Case G m k): reflectPol s.ortho (Indigo ( Press.portDeck G ) m k i).val=∑ j:Case G m k,ω i j • (Indigo (M) m k j).val:= by
    simp_rw [← indigo_frame]; let f:Pol G:= film (M) i (h:=m) (r:=k); obtain ⟨ht,he,H⟩:= Theater.cinema f|>.mp (filmW (M) i (h:=m)); rw [ ← show reduceEq (rotated s.ortho (film (M) i (h:=m)))= reflectPol s.ortho (reduceEq (film (M) i (h:=m))) from Maxwell.Free.pulls_label ( G:=G ) (⟨f,(limitH ht), he ⟩: Labels.Label G m) s.ortho, cast ]; -- Label structure subtype
    exact (show _= ∑ j:Case G m k,ω i j • reduceEq (film (M) j (h:=m)) from by simp_rw [map_sum,show ∀ x:ℝ,∀ p:Pol G,reduceEq ( x • p )= x • reduceEq p from fun _ _=> map_smul ((reduceEq.toLinearMap).restrictScalars ℝ) ..])
-- family reading of arbitrary `g: Glyph`. Convenient to avoid all pair tests wide.MF.
abbrev take (g:Glyph (M) k)(i:Case G g.size g.grade) : Glyph (M) k:= ⟨g.1,g.2.1,i⟩
lemma homebase (g:Glyph (M) k) : take g g.2.2=g:= rfl
def rotateField {E:Type}[AddCommMonoid E][Module ℝ E](f:Glyph (M) k→ E)(g:Glyph (M) k): E:= ∑ i:Case G g.size g.grade, markS s G g.size g.grade g.2.2 i • f (take g i)
-- action `φ(f): coord in continuation(label s)`
lemma rotateGroup {E:Type}[AddCommMonoid E][Module ℝ E](f:Glyph (M) k→ E)(g:Glyph (M) k): rotateField s (rotateField t f) g=rotateField ( t*s ) f g:= by
    unfold rotateField; simp_rw [Finset.smul_sum, smul_smul]; change (∑ x:Case G g.size g.grade,∑ y:Case G g.size g.grade,( markS s G g.size g.grade g.2.2 x * markS t G g.size g.grade x y ) • f (take g y))= _; nth_rw 1 [Finset.sum_comm]; -- dependent.Sigma maybe fail; write change
    apply Finset.sum_congr rfl; intro i _; rw [pack, Finset.sum_smul]
lemma stil {E:Type}[AddCommMonoid E][Module ℝ E](f:Glyph (M) k→ E)(g:Glyph (M) k): rotateField 1 f g=f g:= by
    unfold rotateField; simp_rw [start, ite_smul,zero_smul,one_smul, Finset.sum_ite_eq,if_pos ( Finset.mem_univ _)] -- mem proof
lemma letterSpin (g:Glyph (M) k): reflectPol s.ortho (Letters (M) g)=rotateField s (Letters (M)) g:= by rcases g with ⟨i,j,k⟩; simp only [letS]; rw [castV]; unfold rotateField; simp_rw [take,letS]
end YM.FVA2.Position.Axes
