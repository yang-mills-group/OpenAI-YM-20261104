import YM.RG11Proof.Bearing.Degree

/-! # Known vs unknown contribution in mass adjustment algorithm -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bearing
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped BigOperators Classical
variable {J I:Type*}[Fintype J]
local notation "ps"=>PowerSeries ℝ
local notation "rr"=> Square J ℝ
local notation "ptr"=> Square J ps

-- use FPS but when programming N_q known part extract on zeros at the same order.

def known (β:ps)(b X m:ptr)(k:ℕ):rr:=piece k (X*b+β•flash X-m*X)

 theorem sep {w:J→ℕ}{X b m:ptr}{β:ps}{k}:
   piece k (diagonalX w*X-X*diagonalX w+ (X*b+β•flash X-m*X))= spot w (piece k X) id + known β b X m k:=by
  unfold known; rw [piece_add,←segmentation]
  rw [show ∀ (Y Z:ptr),piece k (Y-Z)=piece k Y-piece k Z from fun Y Z=>Matrix.ext fun i j=>by simp]
  rw [arch_piece,arch_right]

-- prior to positive orders and heads. Decompose m*X asymmetrically as m_k*1+older.
 theorem beam {β:ps}(hβ:∀ i≤1,coeff i β=0){b:ptr}(hb:piece 0 b=0){X Y m v:ptr}(hX:nearId X)(hY:nearId Y)(_hm:piece 0 m=0)(hv:piece 0 v=0){k:ℕ}(_hk:0<k)
     (h:∀ i<k,piece i X=piece i Y)(h':∀ i<k,piece i m=piece i v):
     known β b X m k+piece k m=known β b Y v k+piece k v:=by
   have he : piece k (X*b)=piece k (Y*b):=by
     rw [piece_mul,piece_mul]; refine Finset.sum_congr rfl (fun z hz=>?_)
     have hz:= Finset.HasAntidiagonal.mem_antidiagonal.mp hz
     by_cases hr:z.2=0
     · rw [hr,hb,mul_zero,mul_zero]
     rw [h _ (by omega)]
   have ht:piece k (β •flash X)=piece k (β•flash Y):=by
     ext i j; change coeff k (β*derivative ℝ _) = coeff k (β*derivative ℝ _)
     rw [coeff_mul,coeff_mul]; apply Finset.sum_congr rfl; intro z hz
     by_cases hd:z.1≤1
     · rw [hβ _ hd]; simp
     have hz:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
     rw [coeff_derivative,coeff_derivative,←piece_apply (A:=X),←piece_apply (A:=Y),h _ (by omega)]
   unfold known
   rw [show ∀ y z:ptr, piece k (y-z)=piece k y-piece k z from fun y z=>Matrix.ext fun i j=>by simp];
   rw [show piece k (Y*b+β•flash Y-v*Y)=piece k (Y*b)+piece k (β•flash Y)-piece k (v*Y) from Matrix.ext fun i j=>by simp,piece_add,he,ht]
   rw [piece_mul_recurse_left m X,piece_mul_recurse_left v Y,hX,hY,mul_one,mul_one]
   unfold trailLeft
   rw [show (∑ z∈Finset.HasAntidiagonal.antidiagonal k, if z.2=0 then (0:rr) else piece z.1 m * piece z.2 X)=
         (∑ z∈Finset.HasAntidiagonal.antidiagonal k, if z.2=0 then 0 else piece z.1 v * piece z.2 Y) from ?_]
   · abel
   refine Finset.sum_congr rfl fun z hz=>?_; split
   · rfl
   rename_i hd
   have hz:=Finset.HasAntidiagonal.mem_antidiagonal.mp hz
   rw [h' _ (by omega)]
   by_cases hp:z.1=0
   · rw [hp,hv]; simp
   rw [h _ (by omega)]

-- for programming
local notation "bundle"=> ℕ→(rr × rr)

def alien (x:bundle):ptr:=unpack (fun i=>(x i).1)
def tailMap (x:bundle):ptr:=unpack (fun i=> (x i).2)

def takeMap (x:bundle)(n:ℕ):ptr:=unpack (fun i=>if i<n then (x i).2 else 0)

 theorem fresh {β:ps}(hβ:∀ i≤1,coeff i β=0){b:ptr}(hb:piece 0 b=0){X m:ptr}(hX:nearId X)(hm:piece 0 m=0){k:ℕ}(hk:0<k)(x:bundle)(h:∀ i<k,piece i X=(x i).1 ∧ piece i m=(x i).2):
     known β b X m k=known β b (alien x) (takeMap x k) k-piece k m:=by
   simp_rw [eq_sub_iff_add_eq]
   have hx(i)(ht:i<k):piece i (alien x)=piece i X:=by unfold alien; rw [piece_unpack,(h i ht).1]
   have hy(i)(ht:i<k):piece i (takeMap x k)=piece i m:=by unfold takeMap; simp only [piece_unpack, ht, if_true]; exact (h _ ht).2.symm
   have hu:=beam hβ hb hX ((hx _ hk).trans hX : nearId (alien x)) hm ((hy 0 hk).trans hm) hk (fun i hi=> (hx i hi).symm) (fun i hi=>(hy i hi).symm)
   simpa only [takeMap,piece_unpack,lt_irrefl,↓reduceIte,add_zero] using hu
end YM.RG11.Bearing
