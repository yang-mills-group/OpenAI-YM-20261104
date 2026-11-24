import YM.FormalBulk08.Lava.Tip

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb MvPolynomial
open scoped BigOperators Classical
variable {V : Type*} (q : V→V→ℝ)
abbrev Veil (V : Type*) := (r : ℕ) → Tile V r
def visor {r : ℕ} (a : {a // a∈Finset.antidiagonal r}) (T K : Veil V) : Tile V r:=
   Finset.mem_antidiagonal.mp a.2 ▸ sand (bond q (T (a.1.1+1)) (K (a.1.2+1))) -- dep subst brittle
-- custom cast API
def lengthen {r l : ℕ} (h : r=l) (T : Tile V r) : Tile V l := h▸T
lemma length_agate {r l : ℕ} (h : r=l) {T : Tile V r} (k : Agate T) : Agate (lengthen h T) := by cases h; exact k
lemma visor_eq {r : ℕ} (a : {a // a∈Finset.antidiagonal r}) (T K : Veil V) : visor q a T K= lengthen (Finset.mem_antidiagonal.mp a.2) (sand (bond q (T (a.1.1+1)) (K (a.1.2+1)))) := rfl

def reach (T K : Veil V) (r : ℕ) := ∑ a∈(Finset.antidiagonal r).attach, visor q a T K
lemma reach_agate (T K : Veil V) (r : ℕ) : Agate (reach q T K r) := Agate.sums _ fun i _=> by rw [visor_eq]; exact length_agate _ (agate_sand _)

abbrev Waves (V : Type*) := ℕ→ℕ→Veil V
-- indexed [time(power)][g(power)][rank]. range-heat recurrence uses only smaller time

def posting (p : Heat ℝ V) [Fintype V] : Waves V:=fun n e r=> marble r (readSlice p e n)

def brawl (p t : Waves V) (n e r : ℕ) := ∑ a∈Finset.antidiagonal e,∑ b∈Finset.antidiagonal n, reach q (p b.1 a.1) (t b.2 a.2) r
lemma brawl_agate (p t : Waves V) (n e r : ℕ) : Agate (brawl q p t n e r) := Agate.sums _ fun _ _=> Agate.sums _ fun _ _=> reach_agate _ _ _ _

variable [Fintype V]
lemma facade_length {r l : ℕ} (T : Tile V r) (h : r=l) : facade _ (lengthen h T)=facade _ T := by cases h; rfl
lemma stone_bond (p t : TypeR V) (r : ℕ) : marble r (atomProduct q p t)=reach q (fun j=>marble j p) (fun j=>marble j t) r := by
   apply facade_unique (marble_agate _ _) (reach_agate _ _ _ _)
   simp_rw [marble_grade,reach,map_sum, visor_eq,facade_length,facade_bond q (marble_agate _ _) (marble_agate _ _),marble_grade]; simp_rw [atomProduct,mul_assoc,map_sum, homogeneousComponent_C_mul,comp_glue,comp_fuses,Finset.mul_sum];
   simp_rw [Finset.sum_attach (Finset.antidiagonal r) (fun a=>∑ i,∑ j,MvPolynomial.C (halve (q i j))* (pderiv i (homogeneousComponent (a.1+1) p) * pderiv j (homogeneousComponent (a.2+1) t)))]; simp_rw [Finset.sum_comm (s:= (Finset.univ : Finset V)) (t:=Finset.antidiagonal r)]
lemma stone_crest (p t : Heat ℝ V) (n e r : ℕ) : marble r (chartCross q p t e n)= brawl q (posting p) (posting t) n e r := by
   unfold chartCross; simp_rw [←canyon_eq];simp_rw [map_sum,canyon_eq, stone_bond]; rfl
lemma stone_curve (f : Pap V) (hp : PowerSeries.coeff 0 f=0) (n e r : ℕ) : let p:=posting (coal q f); ((n+1:ℕ):ℝ) • (p (n+1) e r)= stare q (p n e (r+1+1))+brawl q p p n e r := by
   dsimp only; have h:=arc_vac q f hp e n; let w:=readSlice (coal q f) e (n+1)
   have hh : ((n+1:ℕ):ℝ) • w= _ := (show ((n+1:ℕ):ℝ) • w= w*(n+1) by simp [smul_eq_C_mul,mul_comm]).trans h
   rw [← stone_crest]; change ((n+1:ℕ):ℝ) • marble r w = stare q (marble _ (readSlice (coal _ _) e n)) + _; rw [←marble_stare]; simp only [←canyon_eq, ← map_smul, ←map_add,hh]
lemma stone_mark (f t : Pap V) (hp : PowerSeries.coeff 0 f=0) (s : ∀ i j,q i j=q j i) (n e r : ℕ) : let p:=posting (coal q f);let u:=posting (flare q f t); ((n+1:ℕ):ℝ) • (u (n+1) e r) = stare q (u n e (r+1+1)) + (2:ℝ) • brawl q p u n e r := by
   dsimp only; have h:=arc_field q f t hp s e n; let w:=readSlice (flare q f t) e (n+1); let z:=chartCross q (coal q f) (flare q f t) e n
   change w*_= _ + 2*z at h
   rw [← stone_crest]; change ((n+1:ℕ):ℝ) • marble r w = stare q (marble _ (readSlice _ _ _))+ (2:ℝ) • marble r z
   rw [←marble_stare]; simp_rw [←canyon_eq,←LinearMap.map_smul,←map_add]
   congr 1; simp [smul_eq_C_mul,mul_comm w] at *
   rw [map_ofNat];exact h
end YM.FormalBulk08.Lava
