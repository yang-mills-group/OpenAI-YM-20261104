import YM.MSbar.MeasureP.Wreath
import YM.MSbar.MeasureP.Chordal
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Lattice Gauge Push Uniform
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Whisk RG Precision Next.Free Exterior Laurent Bloch
open MultiNext.SignedSource Newt Debut Pattern Cane
variable {ι:Type}{G:Gauge}{c n:Side}{g:Ratio c n} {ρ : ℝ} {κ p:ℕ} {η a E D :ℝ}
variable (P : Cross g.count (TypeFace 1) (TypeFace 1))
local notation "A"=>Primary n G
local notation "B"=>Primary c G
local notation "X"=>pension g P G []
local notation "L"=>(g.count.val:ℝ)
variable (x:Primary n G)(i:Primary n G)(v:B)
local notation "J"=> lyrics g P (Measuring.chart n G x)
noncomputable def voyage (x i:Primary n G): Cover:= lift (i.1.1 - x.1.1)
lemma sings (v:Primary c G) : lyrics g P x.1.1 i v (voyage x i)=pension g P G [] i v:=by rw [lyrics, show circle x.1.1 i (voyage x i)=i from ?_]; unfold voyage circle; rw [wrap_lift,sub_add_cancel]
noncomputable def yarn (g:Ratio c n) (P:Cross g.count (TypeFace 1) (TypeFace 1))(x:Primary n G)(k:ℕ)(i:Primary n G)(j:Primary c G):=Newt.piece k (lyrics g P x.1.1 i j) (xyz (voyage x i))
local notation "F"=>yarn g P x
noncomputable def dim (l: List (Primary n G)):= extent (Whisk.zone (Measuring.chart n G) ∅ l)
lemma afar (l:List A)(hi:i∈l) : size (voyage x i) ≤ 4*dim (x::l):=by
    have hh: separation i.1.1 x.1.1 ≤ dim (x::l):= curve (W:=Whisk.zone (Measuring.chart n G) ∅ (x::l)) (x:=Measuring.chart n G i) (y:=Measuring.chart n G x) (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,List.mem_cons_of_mem _ hi,rfl⟩))) (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,List.mem_cons_self ..,rfl⟩)))
    unfold size; exact (Finset.sum_le_sum fun j _=> (component_le (i.1.1-x.1.1) j).trans hh).trans_eq (by rw [Finset.sum_const,Finset.card_univ,show Fintype.card Axis=4 from rfl]; rfl)
namespace Cane
variable {k:ℕ} (h:Cane P D η a E κ p) (l: List (Primary n G)) (hk:k≤κ)
local notation "χ"=>candle a D η E 4 p
local notation "z"=> dim (x::l)
noncomputable def delta (x:Primary n G)(l:List (Primary n G))(g:Ratio c n):= (1+4*(dim (x::l):ℝ))/g.count.val
local notation "σ"=>delta x l g
local notation "w"=>grot g G a p (Measuring.chart n G x)
noncomputable def teeth (r:ℕ):ℝ:= (4*((r:ℝ)+1))^r
noncomputable def value(a D η E:ℝ)(p k:ℕ):= teeth k * candle a D η E 4 p
lemma jaws (k:ℕ): 1≤teeth k:=one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) k] : 1≤ 4*((k:ℝ)+1))
lemma dentures(b k:ℕ)(h:b≤k):teeth b ≤ teeth k:=by unfold teeth; exact (pow_le_pow_left₀ (show (0:ℝ)≤4*((b:ℝ)+1) by positivity) (show (4:ℝ)*((b:ℝ)+1) ≤ 4*((k:ℝ)+1) by gcongr) b).trans (pow_le_pow_right₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) k]) h)
include h
lemma tot: 0 ≤ candle a D η E 4 p:= goodF P h 4 (by norm_num) (k:=0) (Nat.zero_le κ)
lemma sigmaP : 0 < delta x l g:=by unfold delta; positivity
local notation "Φ"=>value a D η E p κ
lemma specs : 0≤ value a D η E p κ:=mul_nonneg (zero_le_one.trans (jaws κ)) (tot P h)
include hk
lemma fling(hi:i∈l): (∑ j:B,w j*|F k i j|) ≤ Φ/L*σ^k:=by
    let v:= voyage x i
    have hr :0≤χ:= tot P h; have hs:=afar x i l hi
    calc
        _ ≤ teeth k * (1+(size v:ℝ))^k*(χ/L^(1+k)) := pieced P x.1.1 i h 4 (by norm_num) v hk (by positivity)
        _ ≤ teeth κ * (1+4*(z:ℝ))^k*(χ/L^(1+k)):=by
            refine mul_le_mul_of_nonneg_right (mul_le_mul (dentures _ _ hk) (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hs 1) _) (by positivity) (zero_le_one.trans (jaws κ))) (by positivity)
        _ = Φ/L*σ^k:=by rw [pow_add,pow_one]; unfold value delta; rw [div_pow]; ring
lemma price (hi:i∈l)(hl:dim (x::l) ≤ g.count.val): (∑ j:B,w j*|X i j-scroll F k i j|) ≤ Φ/L* σ^k:=by
    let t:= voyage x i; have hv:= afar x i l hi; have ht:(size t:ℝ) ≤ 4*L:= by exact_mod_cast (hv.trans (Nat.mul_le_mul_left 4 hl))
    have hr:=tot P h
    have hh(j:B): X i j-scroll F k i j=Newt.tail k (J i j) t:=by rw [Newt.tail,show lyrics g P (chart n G x) i j t=_ from sings P x i j]; rfl
    simp_rw [hh]; calc
        _ ≤ χ/L^(1+k)*(1+(size t:ℝ))^k:= dressed P x.1.1 i h 4 (by norm_num) t hk ht
        _ ≤ Φ/L^(1+k)*(1+4*(z:ℝ))^k:=by
            refine mul_le_mul (div_le_div_of_nonneg_right (le_mul_of_one_le_left hr (jaws _)) (by positivity)) (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hv 1) _) (by positivity) (div_nonneg (specs P h) (by positivity))
        _ = Φ/L*σ^k:=by rw [pow_add,pow_one]; unfold delta; rw [div_pow]; ring
omit hk
lemma prop (hi:i∈l)(hl:dim (x::l) ≤ g.count.val): (∑ j:B,w j*|X i j|) ≤ Φ/L:=by simpa only [scroll, Finset.range_zero,Finset.sum_empty,sub_zero,pow_zero,mul_one] using price P x i h l (k:=0) (Nat.zero_le _) hi hl
include hk
lemma conifers(hl:dim (x::l) ≤ g.count.val): Yarn l.length (fun T: List B=> (T.map w).prod*|beads (pension g P G []) l T-arco F k l T|) ≤ (2*((κ:ℝ)+1)*(Φ/L))^l.length*σ^k:= under F w (fun i=> grot_positive ..|>.le) (Φ/L) σ (div_nonneg (specs P h) (by positivity)) (by unfold delta; positivity) l _ hk (fun i hi k hv=>fling P x i h l hv hi) X (fun i hi=>prop P x i h l hi hl) (fun i hi k hv=> price P x i h l hv hi hl)
lemma highland (he:0<k)(hl:g.count.val≤dim (x::l)):
    Yarn l.length (fun T:List B=> (T.map w).prod*|arco F k l T|) ≤ (((κ:ℝ)+1)*(Φ/L))^l.length * σ^k:=by
    have hσ :1≤σ:=by unfold delta; rw [le_div_iff₀ (by positivity),one_mul]; linarith only [(show L ≤ (z:ℝ) by exact_mod_cast hl),Nat.cast_nonneg (α:=ℝ) z]
    have ht:= specs P h; apply (loft F w (fun i=>grot_positive ..|>.le) (Φ/L) σ (by positivity) (zero_le_one.trans hσ) l _ hk (fun i hi k hv=> fling P x i h l hv hi) hσ he).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hσ (Nat.sub_le k 1)) (by positivity)
end Cane
end YM.MSbar.Measuring
