import YM.FVA2.Teller.Desk
import YM.FVA2.Parity.Kit
/-!
# Rank and signed-symmetry implementation

Helpers like `morph` (check the `Houses` requirements survive taking `aspired`)
and `spice`. No analysis of actual-QFT field charts/schemes. These are the
`fees` in the formal comparison, not those schemes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Teller.Homes
open Function Set Filter Finset MeasureTheory Metric Real
open Lattice MS MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Arts MS.High
open MS.Local.Physical MS.Menus MS.Land MS.Lifting MS.Native MS.Native.Orient MS.Native.Chart MS.Cylinder MS.Cylinder.Lab
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Wind MS.Wind.Leading
open Position Position.Wheel Position.Axes Position.Favors Parity Capacity Desk
open MS.Native.Paint
open Register
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n d k r:ℕ} {B:Deck G} {J:Glyph B d}{b:Bool}{I:Type}{u:ℤ}
local notation "℘"=> Press.portDeck G
local notation "γ"=> Parity.Screen.grey G Cover
-- Rank integrated across symmetries. no reconstruction of dimensional F yet.
def Sturdy (A: Prescription ( Press.portDeck G ))(b:Bool): Prop:= ∀ d,∀ i:Plaid ( Press.portDeck G ) d,Houses (A.fees d i) (Land.read i) b
variable {P:Acts (Press.portDeck G) d}{F:DMark G d→Acts (Press.portDeck G) d}
lemma group_loc (W:Finset I) (f:I→ℝ) {X:I→Acts (Press.portDeck G) d}(h:∀ i∈W, Located r ( X i n ) u): Located r ( stepF W f X n ) u := by
    constructor
    · intro g he; change (∑ i∈W,f i • (X i n).register) g=_; simp_rw [ Finset.sum_apply ]; exact Finset.sum_eq_zero fun i hi=> by rw [ Pi.smul_apply,( h i hi ).holds _ he, smul_zero ]
    exact lower_r f (fun i hi=> (h i hi).moves)
lemma lift_loc (s: Signed)(H:Located r (P n) u): Located r (lifted s P n) u := by
    constructor
    · intro i h; unfold lifted erect; dsimp only; apply Finset.sum_eq_zero; intro j _; rw [H.holds (Axes.take i j) (show _ from h), smul_zero]
    exact fun i=> limits_p s ( H.moves i )
lemma current (x:I→Acts (Press.portDeck G) d) (W:Finset I)(c:I→ℝ)(z:ℝ): (stepF W c x n).proof.input z=∑ i∈W,c i • (x i n).proof.input z:= by unfold stepF bigH; simp_rw [Finset.sum_apply,Pi.smul_apply]
lemma morph (j:DMark G d)(h:∀ i: DMark G d,Houses (F i) ( Land.read i ) b): Houses (aspired F j) ( Land.read j ) b:= fun n=> ⟨ fun H=> H.symm ▸ mainL F (fun i=> (h i 0).leading rfl) j, group_loc _ _ (fun i _=> group_loc _ _ (fun x _=> lift_loc i (( h (pin j x) n ).upper))),fun t hi=> group_loc _ _ (fun i _=> group_loc _ _ (fun x _=> lift_loc i ((h (pin j x) n).strict t hi))) ⟩
lemma town (j: DMark G 0): Houses ( Ace.active j ) ( Land.read j ) b:= by
    intro n; have ht (i:ℤ)(he:0 ≤ i) : Located ( Land.read j ).grade (Ace.active j n) i:= ⟨ fun g h=>by rw [Ace.register, if_neg (fun p=>?_)]; rw [p.2] at h; omega,fun x=> by rw [Ace.vatican]; exact fun _ _=> rfl ⟩
    refine ⟨fun H=> H.symm ▸ Ace.fit _, ht n (by omega), fun h i=> ht _ (by omega)⟩
lemma solid (i:ℕ)(h:Located r (P n) u): Located r (Parity.Screen.shaded i P n) u:= by
    constructor
    · intro a ha; change Parity.Screen.rightS _ _ _ _=_; rw [Parity.Screen.rightS,h.holds a ha,smul_zero]
    intro x; rw [Parity.Screen.shaded,Parity.Screen.copes]; exact (Parity.Screen.forecast (h.moves x)).smul _
lemma spice (j:DMark G d) (H:Houses P (Land.read j) b): Houses (Parity.Screen.morn j P) ( Land.read j ) b:= by
    intro n; refine ⟨fun h=> h.symm ▸ Parity.Screen.retained _ _ ( (H 0).leading rfl), group_loc _ _ (fun i _=>?_ ),fun h k=>group_loc _ _ (fun i _=>?_)⟩
    · cases i; exact (H n).upper; exact solid _ ( H n ).upper
    cases i; exact ( H n ).strict h k; exact solid _ (( H n ).strict h k)
-- stamping.
section
variable (s t: Signed)(K: Dot G Cover)
lemma pursed (x:Edge Cover): purse s (purse t x)=purse (s*t) x:= by
    cases ht:t.flip x.2 <;> cases hs:s.flip (t.perm x.2) <;> simp [purse,shiftTerm,Signed.act_add,stepflip,ht,hs,Signed.act_mul]
lemma turning_all (i:LightMode G Cover): turn s (turn t i)= turn (s*t) i:= by
    rcases i with ⟨⟨⟨_|j,b⟩,i⟩,x⟩; · simp only [turn,Signed.act_mul]
    obtain ht:= pursed s t (x,j); refine Prod.ext rfl ?_; exact congr_arg Prod.fst ht
lemma pricing (i:LightMode G Cover): Native.Orient.σ s (turn t i)*Native.Orient.σ t i=Native.Orient.σ (s*t) i:= by
    rcases i with ⟨⟨⟨_|j,b⟩,i⟩,x⟩; · simp [turn,Native.Orient.fee, Native.Orient.σ]
    cases hp:t.flip j <;> cases ht:s.flip (t.perm j) <;> simp [ Native.Orient.σ,Native.Orient.fee,cross,turn,hp,ht]
lemma graffiti_mul (X Y:LightMode G Cover→ℂ): graffiti X (graffiti Y K)= graffiti (X * Y) K:= by
    apply Subtype.ext; funext l; simp only [landc,Cylinder.rent, ← mul_assoc, show (X * Y)= fun i=> X i * Y i from rfl, List.prod_map_mul ] -- theorem name
lemma pose_mul : pose s (pose t K)=pose (s*t) K:= by
    unfold pose; simp only [LinearMap.comp_apply, ← ferry_rent (turn t),ferry_trans, Function.comp_def,graffiti_mul,turning_all,show (fun i=> Native.Orient.σ s (turn t i))*Native.Orient.σ t= ( Native.Orient.σ (G:=G) (P:=Cover) (s*t) ) from funext fun _=> pricing s t _ ]
local notation "φ"=> Parity.Screen.grey
lemma commute : γ (pose s K)= pose s (γ K):= by unfold pose Screen.grey; rw [ LinearMap.comp_apply, ← ferry_rent,graffiti_mul,LinearMap.comp_apply,graffiti_mul,mul_comm ]; rfl
-- See `Teller/Later` next, for the application.
end
end YM.FVA2.Teller.Homes
