import YM.XSpace.Cornea
/-!
# Cubic probe budget
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gland
open Function Set Filter Trace Relief Tide Sail Lattice Chart2 Chiral Octave Graph3 Mu MvPolynomial Asymptotics
open scoped Topology BigOperators Pointwise
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{G:Gauge}{V:ι→Cover→Prop} {i j k n:ℕ}
-- permit translation from P inserted to Γ with sign costs
abbrev read (A B C:Line G):Module.Dual ℂ (Stamp G):= (peek G).toLinearMap ∘ₗ Ξ A ∘ₗ Ξ B ∘ₗ Ξ C
abbrev feet (x y z: Cover)(P Q R:Line G)(H:Stamp G)(w:Cover):= read (displace x P) (displace y Q) (displace z R) (Trace.volume w H)
lemma money (A B C:Line G)(p:Stamp G): read A B C p=peek G (Ξ A (Ξ B (Ξ C p))):=rfl
lemma midfoot (P Q R A B C:Line G)(x y z w:Cover):
     feet x y z P Q R (harp A *harp B * harp C) w=sign x y z P Q R A B C w+sign x y z P Q R A C B w+sign x y z P Q R B A C w+sign x y z P Q R B C A w+sign x y z P Q R C A B w+sign x y z P Q R C B A w:=by unfold feet; rw [map_mul (Trace.volume w),map_mul (Trace.volume w),Trace.rings,Trace.rings,Trace.rings,money]; simp only [ξ_mul,ξ_harp,ξ_zero,map_add,map_mul,zero_add,add_zero, mul_zero,zero_mul,peek_C]; unfold sign collation; ring
variable {P Q R:Line G}(p:P∈cane 1 G)(q:Q∈cane 1 G)(r:R∈cane 1 G)
private def sustains (P Q R:Line G) : Levee G where
 carrier := {A |∀ x y z:Cover, Summable (feet x y z P Q R A)}
 zero_mem' x y z:= by change Summable (fun w=> feet x y z P Q R 0 w); unfold feet; simp only [map_zero]; exact summable_zero
 add_mem' {A B} a b x y z:=by change Summable (fun w=> feet x y z P Q R (A+B) w); unfold feet; simp_rw [_root_.map_add]; exact (a x y z).add (b x y z)
 smul_mem' c v he x y z:=by change Summable (fun w=> feet x y z P Q R (c • v) w); unfold feet; simp_rw [map_smul]; exact (he x y z).const_smul c
include p q r in
lemma entry {H:Stamp G}(h:H∈Trio G i j k)(x y z:Cover): Summable (feet x y z P Q R H):=by
  suffices H∈sustains P Q R from this x y z; refine through3 (sustains P Q R) (fun A hA B hB C hC x y z=>?_) h; change Summable (fun w=> feet x y z P Q R (harp A * harp B * harp C) w); simp_rw [midfoot]; let f (A B C:Line G) := sign x y z P Q R A B C; have ha(A B C:Line G) :Summable (f A B C):= sign_fin x y z P Q R p q r A B C; apply Summable.add (Summable.add (Summable.add (Summable.add (Summable.add ?_ ?_) ?_) ?_) ?_) ?_ <;> apply ha
private def crystal (P Q R:Line G)(L:Filter ι)(d:ℕ)(a:ι→ℝ)(x y z:ι→Cover)(V:ι→Cover→Prop) : Levee G where
 carrier:={A|Dance V L a d fun i=> feet (x i) (y i) (z i) P Q R A}
 zero_mem':= by change Dance V L a d (fun i w=> feet (x i) (y i) (z i) P Q R 0 w); simp_rw [ feet,map_zero]; exact Dance.zero
 add_mem':=by intro A B h H; change Dance V L a d (fun i w=> feet (x i) (y i) (z i) P Q R (A+B) w); simp_rw [feet,_root_.map_add]; exact Dance.add h H
 smul_mem':=by intro c A h; change Dance V L a d (fun i w=> feet (x i) (y i) (z i) P Q R (c • A) w); simp_rw [feet,map_smul]; exact Dance.const_smul h c
include p q r in
lemma essence (H:board V L a x y z)(hi:i≤1)(hj:j≤1)(hk:k≤1){A:Stamp G}(h:A∈Trio G i j k): Dance V L a (5+i+j+k) (fun w=> feet (x w) (y w) (z w) P Q R A):= by
  change A∈ crystal _ _ _ L _ a x y z V; refine through3 _ (fun A hA B hB C hC => ?_) h; change Dance V L a _ _; simp_rw [show ∀ x y z, feet x y z P Q R (harp A* harp B*harp C)=_ from fun x y z=> funext fun w=> midfoot P Q R A B C x y z w]; -- typo all predicate; simp unfolded?
  refine Dance.add (Dance.add (Dance.add (Dance.add (Dance.add (sign_toll p q r hA hB hC H hi hj hk) ?_) ?_) ?_) ?_) ?_
  · rw [show 5+i+j+k=5+i+k+j by omega]; exact sign_toll p q r hA hC hB H hi hk hj
  · rw [show 5+i+j+k=5+j+i+k by omega]; exact sign_toll p q r hB hA hC H hj hi hk
  · rw [show 5+i+j+k=5+j+k+i by omega]; exact sign_toll p q r hB hC hA H hj hk hi
  · rw [show 5+i+j+k=5+k+i+j by omega]; exact sign_toll p q r hC hA hB H hk hi hj
  rw [show 5+i+j+k=5+k+j+i by omega]; exact sign_toll p q r hC hB hA H hk hj hi
private lemma climb_le : Trio G i j k ≤ Trio G 0 0 0:= k₃
lemma clique (x:Cover)(H:Stamp G)(h:H∈ Trio G i j k): Trace.volume x H ∈ Trio G i j k:=by
  refine through3 ((Trio G i j k).comap (Trace.volume x).toLinearMap) (fun p hp q hq r hr=>?_) h; change Trace.volume x (harp p * harp q * harp r)∈ Trio G i j k; simp_rw [map_mul,Trace.rings]; exact Submodule.mul_mem_mul (Submodule.mul_mem_mul (sap (cane_move hp x)) (sap (cane_move hq x))) (sap (cane_move hr x))
lemma clean : Mute G≤Trio G 0 0 0:= by refine sup_le climb_le (iSup_le fun i=>?_ ); rintro x ⟨x,h,rfl⟩; exact Submodule.sub_mem _ (clique (step i) x h) h
abbrev Uplands (x y z: Cover)(P Q R:Line G)(A:Stamp G):= ∑' w:Cover, feet x y z P Q R A w
private lemma uplands_smul (x y z:Cover)(P Q R:Line G)(c:ℂ)(A:Stamp G): Uplands x y z P Q R (c • A)= c*Uplands x y z P Q R A:=by unfold Uplands feet; simp_rw [map_smul,smul_eq_mul,tsum_mul_left]
include p q r in
lemma uplands_add (x y z:Cover)(A B:Stamp G)(h:A∈ Trio G i j k)(h':B∈Trio G i j k): Uplands x y z P Q R (A+B)= Uplands x y z P Q R A+Uplands x y z P Q R B:=by unfold Uplands feet; simp_rw [_root_.map_add]; exact (entry p q r h x y z).tsum_add (entry p q r h' x y z)
private def benign (x y z:ι→Cover)(P Q R:Line G)(L:Filter ι)(a:ι→ℝ)(hp:P∈cane 1 G)(hq:Q∈cane 1 G)(hr:R∈cane 1 G): Levee G where
 carrier:={A|A∈Trio G 0 0 0 ∧ Little L a 6 (fun i=> Uplands (x i) (y i) (z i) P Q R A)}
 zero_mem':=⟨Submodule.zero_mem _, (isLittleO_zero _ L).congr (fun x=> by simp [Uplands,feet]) (fun _=>rfl)⟩
 add_mem':=by rintro A B ⟨h,h'⟩ ⟨k,k'⟩; exact ⟨Submodule.add_mem _ h k,(IsLittleO.add h' k').congr (fun i=> (uplands_add hp hq hr _ _ _ _ _ h k).symm) (fun _=>rfl)⟩
 smul_mem':=by rintro c A ⟨h,h'⟩; exact ⟨Submodule.smul_mem _ _ h,(IsLittleO.const_mul_left h' c).congr (fun i=> (uplands_smul (x i) (y i) (z i) P Q R c A).symm) (fun _=>rfl)⟩
private lemma diaspora (t:Axis)(f:Cover→ℂ)(H:Summable f): 0=∑' i:Cover,(f (i+step t)-f i):=by
  let E:= Equiv.addRight (step t: Cover); have he:Summable (fun i=>f (E i)):= (Equiv.summable_iff E).mpr H; change 0=∑' i:Cover,(f (E i)-f i); rw [he.tsum_sub H,Equiv.tsum_eq E]; rw [sub_self]
include p q r in
lemma pays_out (s: Stage L a)(H:Ensemble L a x y z){A: Stamp G}(h:A∈Mute G): Little L a 6 (fun i=> Uplands (x i) (y i) (z i) P Q R A):=by
  suffices Mute G≤benign x y z P Q R L a p q r from (this h).2; refine sup_le (fun i hi=> ⟨climb_le hi,pull s (essence p q r (diastole s H) le_rfl le_rfl (by norm_num) (show i∈Trio G 1 1 0 from hi))⟩) (iSup_le fun i=>?_ ); rintro H ⟨Z,h,rfl⟩; refine ⟨Submodule.sub_mem _ (clique (step i) _ h) h, (isLittleO_zero _ L).congr (fun k=>?_) (fun _=>rfl)⟩; unfold Uplands feet; simp_rw [hike,LinearMap.sub_apply,LinearMap.id_apply,AlgHom.toLinearMap_apply,_root_.map_sub,Foundation.stroll]; exact diaspora i _ (entry p q r h (x k) (y k) (z k))
end YM.XSpace.Gland
