import YM.MSbar.Sat.Rain
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} {U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v y δ w D b u t:ℝ}{m n:ℕ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
variable (F : Forest S.ratio){Y Z:Support f}(J: Voice G)(p:Palisade) 
   (i:S.Choices) (j:Key F G) (t:ℝ)(m:ℕ)
set_option quotPrecheck false
local notation "H"=> priced F i R.clip R.path
local notation "L"=> address F G
local notation "N"=> (Key F G)
local notation "G!"=> (Grants i R F p n)
def shutterPad (F: Forest S.ratio)(G:Gauge) (j : Key F G) (m:ℕ):= halo m {address F G (Sum.inr j)}
def scarf (R:Rep G f) : Positions (Key F G):= (-t) • prime (address (p:=S.ratio) F G) m (priced F i R.clip R.path) j
local notation "c₀"=> scarf F i j t m R
local notation "X"=> (shutterPad F G j m)
def braid (R:Rep G f) := (tint G _ (scarf F i j t m R))
local notation "s₀"=> braid F i j t m R
def crown (R:Rep G f): F.Slice G := G.lieExp ∘ braid F i j t m R
lemma blanking (z:F.Free)(hz:z∉ board F (shutterPad F G j m)) : braid F i j t m R z=0 :=by
   ext k; change ((-t:ℝ) * prime L m H j (z,k))=0; unfold prime; rw [if_neg, mul_zero]; intro hg; exact hz (mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨_,mem_singleton_self _,hg⟩⟩)
lemma pages (x:F.Free) (he:crown F i j t m R x≠1): x.val.1∈shutterPad F G j m :=by by_contra hn; apply he; unfold crown; rw [Function.comp_apply]; rw [blanking F i j t m x (fun h=> hn ((mem_filter.mp h).2)),G.mat_lieExp_zero]
local notation "x₀"=> crown F i j t m R
lemma aims (hx:X⊆Y): Booking (youth F Y) F x₀:=⟨fun v hp=>by have hh:=hx (pages F i j t m v hp); exact ⟨halo_subset _ _ hh,page F (halo_subset _ _ hh)⟩⟩
local notation "k₀"=> ice p.coords p.gap p.a p.density
local notation "h!"=> pedal F x₀
variable (h:Grants i R F p n)(g:Clear G J) (V:Config G c)
include h
lemma jewelled : wash (scarf F i j t m R) ≤ |t| *k₀ :=by
    unfold scarf; rw [wash_smul,abs_neg]; exact mul_le_mul_of_nonneg_left (salary h.buys m j) (abs_nonneg t)
lemma masts (z): ‖braid F i j t m R z‖ ≤ shade G*(|t| *ice p.coords p.gap p.a p.density) :=by change ‖tint G _ c₀ z‖≤ _; exact (norm_le_pi_norm (tint G _ c₀) z).trans ((tint_le c₀).trans (mul_le_mul_of_nonneg_left ((sup_wash _).trans (jewelled F p i j t m h)) (shade_pos G|>.le)))
include g
local notation "Q!"=> (chink F J V (pedal F (crown F i j t m R) U) Y - chink F J V U Y)
def bonfire (F: Forest S.ratio)(G:Gauge)(Y:Support f) (a b:ℝ):= (Y.card*4)*Fintype.card G.ColorIndex*a*b
lemma bask (he : shade G*(|t| * k₀) ≤ u) (hR:D≤ J.r) (hP:u≤D)(hp:pays F V b Y U)(hk:b≤ J.δ)(hJ: J.C*b ≤ D) (ha:X⊆Y):
    wash ((chink F J V (pedal F (crown F i j t m R) U) Y - chink F J V U Y) - c₀) ≤ bonfire F G Y (J.C*D) u:= by
   let B:=board F Y; let T:=U; let Q:=Q!
   have hh(i:F.Free): ‖s₀ i‖ ≤u:=(masts F p _ _ _ _ h _).trans he
   let X':= B ×ˢ (Finset.univ:Finset G.ColorIndex)
   let w:= Q-c₀; let a:= J.C*D*u; have hv(k:F.Free)(hj:k∈ B):
        ‖fareX F J V (h! U) k-s₀ k-fareX F J V U k‖≤ a:=(hears F J V g hp hk hJ (p:=s₀) hR (fun p _=>hh p) hP k hj).trans (mul_le_mul_of_nonneg_left (hh k) (mul_nonneg (zero_le_one.trans g.cost) ((norm_nonneg _).trans ((hh k).trans hP)))) -- protect i
   let f(k:N):ℝ:= |w k|; have ht (k:N)(hz:k∈X'): f k ≤ a:= by
       let l:= k.1; let m:= k.2; have he:l∈B:= (mem_product.mp hz).1
       let u:= fareX F J V (h! U) l-s₀ l-fareX F J V U l
       have hy: w k=u m:=by
          change (tint G _ (chink F J V _ Y) l m -tint G _ (chink F J V U Y) l m)-s₀ l m=_
          simp only [chink,ContinuousLinearEquiv.apply_symm_apply, if_pos (show l∈ board F Y from he)]; unfold u; simp only [PiLp.sub_apply]; abel
       rw [show f k=‖u m‖ from hy ▸ rfl]; exact (PiLp.norm_apply_le u m).trans (hv l he)
   unfold wash; change (∑ k,f k) ≤ _; have hw(k:N)(hd:k∉ X'): w k=0:=by
       let l:=k.1; have he:l∉ board F Y:= fun hk=>hd (mem_product.mpr ⟨hk, Finset.mem_univ _⟩); have ht :l∉board F X:=fun hv=> he (mem_filter.mpr ⟨mem_univ _,ha ((mem_filter.mp hv).2)⟩)
       change (tint G _ (chink F J V _ Y) l k.2-tint G _ (chink F J V U Y) l k.2)-s₀ l k.2=0
       simp only [chink,ContinuousLinearEquiv.apply_symm_apply, if_neg he, blanking F i j t m l ht]; simp
   rw [← sum_subset (subset_univ X') (fun p _ ht=>by unfold f; rw [hw p ht,abs_zero])]
   apply (Finset.sum_le_sum (g:=fun _=> a) ht).trans; rw [Finset.sum_const,nsmul_eq_mul,show X'.card= B.card*Fintype.card G.ColorIndex by simp [X']]; unfold a bonfire; have hu:0≤u:=(norm_nonneg _).trans (hh j.fst)
   push_cast; have hc:0≤J.C*D:=mul_nonneg (zero_le_one.trans g.cost) (hu.trans hP)
   have hp': (B.card:ℝ)≤ Y.card*4:=by exact_mod_cast boardC F Y
   refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg (α:=ℝ) (Fintype.card G.ColorIndex))) (mul_nonneg hc hu)).trans_eq ?_; ring
end YM.MSbar.Heath
