import YM.AlbaMS.Cutis.Fleece
import Mathlib.Algebra.Algebra.Operations
/-!
# populated shift on orbit variables. Cost nil. per stencil U & sym
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter IsNilpotent LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace
open Bric Coil Loft Inlay Inlay.Net Odom Lattice Nexus
variable {V I R S : Type*}[Fintype V][Fintype I][CommRing R]{G:Gauge}{n:Side} (T:Tune R)

private def lunar (U:LightQ G n R) : Prop:=∀ l, (Beam T).firm (roots Finset.univ (Beam T).fee (Stick T).fee l U)=0
variable {U X:LightQ G n R}{c d:G.Color}
local notation "E↑" T F => Wind ø (Tune.D T) F
local notation "C'" T p => air (fun i=> Tune.D T (fill p i))
lemma lunar_pay {U : LightQ G n R} (h:lunar T U)(a:R): lunar T (a • U):=fun i=> by rw [map_smul,map_smul,h i,smul_zero]
lemma full_hp (U:LightQ G n R)(h:(Beam T).firm U=0)(H:∀ c:G.Color,air (fun i=>T.D (fill c i)) U=0): lunar T U:= by
  intro L; cases L with|nil=>exact h|cons x v=>
    obtain ⟨c,he⟩:=drift_color T U x; rw [roots_out,he,H c,map_zero,map_zero]
omit [Fintype V][Fintype I] in -- implicit already not included
lemma breath (w: ink0 G n→ℝ)(i:ink0 G n): air w (C (E:=ink1 G n) ℝ i)=w i • 1:=by rw [air_ap, Finset.sum_eq_single i]; unfold DC C; simp; intro j _ ht; simp [C,DC,Place.c, ht]; simp -- orientation
-- token drift charge has only second term; H here coefficientwise. projection after any active difference derivative.
def lbit (c d:G.Color)(n:Side) (i:ink0 G n):=∑ j:ink0 G n,turn c i j * fill d j
lemma bill (c d:G.Color) : air (fill d) (hill (V:=Arm n) (I:=Vtx n) c)=∑ i:ink0 G n,lbit c d n i • Loft.L (E:=ink1 G n) ℝ i:=by
  have ht (x:ink0 G n): air (fill d) (Loft.L (E:=ink1 G n) ℝ x)=0:=air_simple _ _ (fun i=>by simp [Loft.L,DC,Place.l, Place.c])
  have hv (x y:ink1 G n): air (fill (I:=Vtx n) d) (K ℝ x*A ℝ y)=0:= air_simple _ _ (fun i=>by simp [K,A,DC,mulD,Place.c,Place.k,Place.a])
  rw [hill,map_add]; simp_rw [Finset.mul_sum,mul_smul_comm,map_sum,map_smul,hv]; rw [Finset.sum_eq_zero (s:=Finset.univ) ?_,zero_add]; swap; · intro i _; simp
  simp_rw [air_prod, ht,breath, show ∀ i:ink0 G n,plane true (Loft.L (E:=ink1 G n) ℝ i)= Loft.L ℝ i from fun i=>(var_tone (ρ:=ø) (Place.l i)).pl true]; simp only [zero_mul,zero_add,mul_smul_comm,smul_smul,mul_one, lbit, Finset.sum_smul]
lemma lunar_hill (h:Even n.val) : lunar T (Wind ø T.D (hill (V:=Arm n) (I:=Vtx n) c)):=by
  intro l; cases l with
  | nil=> unfold roots; change ((lead G n).atlas T.D).firm _=0; rw [id_apply, Wire.visits,citizen h,map_zero]
  | cons x l=>
    rw [roots_out]; obtain ⟨d,hd⟩:=drift_color (G:=G) (n:=n) T (Wind ø T.D (hill c)) x; rw [hd,← air_move];
    refine full_hp T (Wind _ _ _) ?_ (fun f=>?_) l -- proof lunar
    · unfold Beam; rw [Wire.visits,bill,map_sum];
      rw [Finset.sum_eq_zero]; rw [map_zero]; intro i _; rw [map_smul,Wire.actL, lore_S]; simp
    rw [← air_move,bill,map_sum]; rw [Finset.sum_eq_zero]; rw [map_zero]; intro i _; rw [map_smul, air_simple]; simp
    intro j; simp [DC, Loft.L,Place.l,Place.c]
lemma color_free (h:Even n.val)(X: LightQ G n R) (hs:∀ c:G.Color,∃ q:R,air (fun i=>T.D (fill c i)) X=q • Wind ø T.D (hill c)) : (Beam T).firm X=(Stick T).firm X:=by
  refine Flair.project (T:=(Stick T).fee) (s:=Finset.univ) (h:=(Beam T).stub) ?_ (Stick T).stub
  intro x v; obtain ⟨c,he⟩:= drift_color T X x; obtain ⟨b,hb⟩:= hs c; rw [he,hb]; exact lunar_pay T (lunar_hill T h) b v
lemma holds (U:LightQ G n R)(h:Even n.val)(hp:∀ c:G.Color, air (fun i=>T.D (fill c i)) U=0): (Beam T).firm U=(Stick T).firm U:= color_free T h U fun c=> ⟨0,(hp c).trans (zero_smul R _).symm⟩
lemma spent (F:Odom.Book (deck n) G)(he:Even n.val) : (Beam T).firm (F.stim T)= (Stick T).firm (F.stim T):= color_free T he (F.stim T) fun c=>⟨_,F.stim_shift T c (arms n)⟩
end YM.MSBar.Cutis.Winter
