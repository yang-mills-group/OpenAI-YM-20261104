import YM.MSbar.Lis.Mercy
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "X"=>Positions (Primary n G)
local notation "K"=>Primary n G
variable (F:Positions (Primary n G)→ℝ)(x:Primary n G)(s:Strand G)(k m:ℕ)(i:Primary n G)
local notation "Y"=> buoy F 0
local notation "ℓ"=>Measuring.chart n G
local notation "Q"=>fun l=> Y (x::l)
-- Ward read bound. use actual Dept Lift expression for p≤p gamma. norm times.TTape.
noncomputable def deck (F:Positions (Primary n G)→ℝ)(x:Primary n G)(s:Strand G) (y:Positions (Primary n G)):=fderiv ℝ F y (grad (ace x s))
local notation "Ω"=>deck F x s
noncomputable def tide (l:List (Primary n G)) : ℝ:= 1+(dim l:ℝ)
lemma ppe (x:Primary n G)(l' l : List K) (hh:l' ⊆ l): tide l' ≤ tide l:=by
    unfold tide; gcongr; apply intr; unfold Whisk.zone; gcongr; intro i h; exact List.mem_toFinset.mpr (List.map_subset _ hh (List.mem_toFinset.mp h))
lemma stern (l:List K)(hi:i∈l)(hq: x∈l)(u: List Axis)(hh:u.length≤1) (z:Strand G):|target x i u z|≤ tide l :=by
   refine (signs x i 1 z u hh hh).trans ?_; unfold beadPad; rw [pow_one]; unfold tide; apply add_le_add_right
   exact (Nat.cast_le.mpr ( Whisk.curve (x:=ℓ i) (y:=ℓ x) (W:=Whisk.zone ℓ ∅ l) (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩))) (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hq,rfl⟩)))))
lemma arms (i :Primary n G)(z:Strand G):|target x i [] z|≤ 1:=by simpa only [beadPad,pow_zero] using signs x i 0 z [] (by simp) (by simp)
variable (l:List (Primary n G)) {B a C:ℝ}{p:ℕ} (h:ContDiffAt ℝ k F 0)(ha:0≤a)(hv:6≤ p)
include h
lemma carved (he:l.length+2≤k): ∑ j:Primary n G,grad (ace x s) j*Y (x::j::l)=buoy (deck F x s) 0 (x::l) :=by
    let b:=grad (ace x s); let L:= l.map Uniform.bolt
    have ht: [bolt x]++L=(x::l).map Uniform.bolt:=rfl
    have hi:1+L.length < k:=by unfold L; rw [List.length_map]; omega
    change _= roc (fun y=> fderiv ℝ F y b) _ 0; rw [←ht,←takeG k h _ b (by rw [List.length_append]; exact hi)]
    have hA:roc F (b :: ([bolt x] ++ L)) 0 = roc F ([bolt x]++ (b ::L)) 0:= Lis.reflect k [] L _ _ (by simp only [List.length_nil,zero_add]; omega) h
    rw [hA,spiral b]; -- b in summand? see
    exact (num [bolt x] L (fun i:Primary n G=>bolt i) b Finset.univ k h (by simpa using hi)).symm
variable (hb: Yarn (m+1) (fun l:List (Primary n G)=> |buoy F 0 (x::l)| *swipe (Measuring.chart n G) a p (x::l)) ≤ B)
include ha hv hb
local notation "R"=>(4*100^3/(n.val:ℝ)^3)
lemma hall (hh:m+2≤k)(E:List K→ℝ)(he:∀ l:List K,l.length=m→ |E l| ≤ tide (x::l))(hT:Yarn m (fun l:List K=>tide (x::l)*|buoy (deck F x s) 0 (x::l)|) ≤ C):
      |Yarn m (fun l:List K=> E l*Measuring.parcel (target x) [] s (fun l=> buoy F 0 (x::l)) l)| ≤ R*B+C:=by
   let f(i:Primary n G)(l:List K) := tear x s i* Y (x::i::l); let I(l:List K):= E l*∑ j:Primary n G, f j l; let J(l:List K):= E l*buoy Ω 0 (x::l)
   have ht(l:List K)(hl:l.length=m):Measuring.parcel (target x) [] s Q l= (∑ j:Primary n G,f j l) + buoy Ω 0 (x::l):=by rw [←carved F x s k l h (by omega)]; unfold f Measuring.parcel tear; change _= _+_; rw [←Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=> ?_; ring
   rw [show Yarn m _= Yarn m I+Yarn m J from ?_]; swap; · rw [←pockets]; refine stitch _ fun l hl=> ?_; unfold I J; rw [ht _ hl, mul_add]
   refine (abs_add_le ..).trans (add_le_add ?_ ?_)
   · apply (polished ..).trans
     calc
       _ ≤ Yarn m fun l:List K=>∑ j:Primary n G, |E l*f j l|:=by apply shiny; intro l hl; unfold I; rw [Finset.mul_sum]; exact Finset.abs_sum_le_sum_abs _ _
       _ ≤ R*B := by rw [scarves]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hb (by positivity)); rw [twilled,Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; rw [← sheen]; refine shiny m fun l hl=>?_ ; unfold f; rw [show E l * _=tear x s j*E l*Y (x::j::l) from by ring, abs_mul]; exact (mul_le_mul_of_nonneg_right (heaped x s j l hv ha (E l) (le_trans (he _ hl) (ppe x (x::l) (x::j::l) (by grind)))) (abs_nonneg _)).trans_eq (by ring)
   refine (polished ..).trans ((shiny (ι:=Primary n G) m ?_).trans hT); intro l h; unfold J; rw [abs_mul]; exact mul_le_mul_of_nonneg_right (he l h) (abs_nonneg _)
-- pay Conde. cubic.^
omit hb
variable (hb2:Yarn 2 (fun l:List (Primary n G)=> |buoy F 0 (x::l)| *swipe (Measuring.chart n G) a p (x::l)) ≤ B) (hC:∀ s:Strand G,Yarn 1 (fun l:List (Primary n G)=> tide (x::l)*|buoy (deck F x s) 0 (x::l)|) ≤ C)
include hb2 hC
lemma slope (hh:3 ≤ k): Conde (target x) (R*B+C) 2 2 (fun l=>Y (x::l)):=by
    intro l s₀ hl v z hv'
    have ht(l:List Axis)(hi:l.length ≤ 1)(s₀ z): Conde (target x) (R*B+C) 0 (1-l.length) (Measuring.parcel (target x) l z (Measuring.parcel (target x) [] s₀ Q)):=by
         let E(t:List K): ℝ:=match t with | [i]=>target x i l z | _=>0
         apply hall F x s₀ k 1 h ha hv hb2 hh E (fun l hl=>?_) (hC _)
         cases l with
         | nil=> simp at hl
         | cons i l=> rw [show l=[] by simpa using hl]; exact stern x i _ (by simp) (by simp) _ hi z
    cases l with
    | nil=> exact (show |(_ :ℝ)|≤ R*B+C from ht v (by rw [List.length_nil,Nat.sub_zero] at hv'; omega) s₀ z)
    | cons i L=> have hL:L=[]:=by simpa only [List.length_cons] using List.length_eq_zero_iff.mp (show L.length=0 by simp only [List.length_cons] at hl; omega)
                 rw [hL] at *
                 have he:v=[]:=List.length_eq_zero_iff.mp (show v.length=0 by simp only [List.length_cons,List.length_nil, Nat.zero_add] at hv'; omega); subst v
                 change |Measuring.parcel _ _ _ _ []| ≤ _
                 rw [show Measuring.parcel _ _ _ _ []= Measuring.parcel (target x) [i] s₀ (Measuring.parcel (target x) [] z Q) [] from ?_]; exact ht _ (by simp) z s₀; unfold Measuring.parcel; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun p _=> ?_; change target _ _ _ _ *(target _ _ _ _*Y [x,j,p])= _; have he:Y [x,j,p]=Y [x,p,j]:=Lis.reflect k [bolt x] [] _ _ hh h; rw [he]; ring
omit hb2 hC
variable (hb3:Yarn 3 (fun l:List (Primary n G)=> |buoy F 0 (x::l)| *swipe (Measuring.chart n G) a p (x::l)) ≤ B) (hC':∀ s:Strand G,Yarn 2 (fun l:List (Primary n G)=> tide (x::l)*|buoy (deck F x s) 0 (x::l)|) ≤ C)
include hb3 hC'
lemma angel (hh:4≤ k): Conde (target x) (R*B+C) 3 1 (fun l=>Y (x::l)):=by
   intro l s₀ hl i s' hi v z hv'
   rw [show l=[] by simpa using List.length_eq_zero_iff.mp (show l.length=0 by omega)] at * ; rw [show i=[] by simpa using List.length_eq_zero_iff.mp (show i.length=0 by simpa using hi)] at *
   rw [show v=[] by simpa using List.length_eq_zero_iff.mp (show v.length=0 by simpa using hv')] at *
   let E(t:List K):ℝ:= match t with | [j,r]=> target x r [] z*target x j [] s' | _=>0
   have he:=hall F x s₀ k 2 h ha hv hb3 hh E (fun t ht=>by
         cases t with
         | nil=>simp at ht
         | cons j t=> cases t with
                      | nil=>simp at ht
                      | cons u t=> rw [show t=[] from (by simpa using ht)]; unfold tide; exact (show |target x u [] z*target x j [] s'| ≤ 1 from (by rw [abs_mul]; exact mul_le_one₀ (arms x u z) (abs_nonneg _) (arms x j s'))).trans (le_add_of_nonneg_right (by positivity))) (hC' s₀)
   let f:= Measuring.parcel (target x) [] s₀ Q; change |Measuring.parcel _ _ _ (Measuring.parcel _ _ _ f) []| ≤ _; refine le_trans (le_of_eq (congr_arg abs ?_)) he; unfold Measuring.parcel; rw [twilled]; simp_rw [Finset.mul_sum, twilled]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun r _=>?_ ; rw [twillz,← Finset.mul_sum]; change target x r [] z*(target x j [] s'*f [j,r])=target x r [] z*target x j [] s'*f [j,r]; ring
end YM.MSbar.Lis
