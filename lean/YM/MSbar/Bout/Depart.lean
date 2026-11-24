import YM.MSbar.Bout.ViewK
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bout
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave -- Set
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {n:Side}  -- remove
open Parma Portal
variable {σ:Type} [Fintype σ][DecidableEq σ]{j:σ→ Site n}{V W: Finset (Site n)}{z y:Site n}{a b B t:ℝ} {s p q d:ℕ}{f g:Pot σ}{x:View σ}
lemma orbital (h:V ⊆ W)(ha:0≤a) (he:Vault j W a s p x f B):Vault j V a s p x f B:=by
    refine ⟨he.1,fun i hi=> ?_⟩; refine le_trans ?_ (he.2 i hi); unfold lump; apply shiny; intro k hk; unfold rate; refine mul_le_mul_of_nonneg_right (w_more (intr (Finset.union_subset_union h (Finset.Subset.refl _))) ha _) (abs_nonneg _) -- spread
lemma tau (ha:0≤a)(h:Vault j {z} a s p x f B): Vault j {y} a s p x f (liftW a s (separation y z)*B):=by
    have he(L:List σ): spread j {y} a s L ≤ liftW a s (separation y z)* spread j {z} a s L:=by
       let v:(Finset (Site n)):= zone j {z} L; let u:= zone j {y} L; have hg : extent {y}=0:=Nat.eq_zero_of_le_zero (Whisk.yard (by simp)); have hx:u⊆ {y}∪ v:=by intro i hi; simp only [u,Whisk.zone, Finset.mem_union, Finset.mem_singleton] at hi; rcases hi with hi|hi; exact Finset.mem_union_left _ (mem_singleton.mpr hi); exact Finset.mem_union_right _ (mem_union_right _ hi)
       have hv:= w_cast hx (mem_singleton_self _) (mem_union_left _ (mem_singleton_self z)) ha s; rw [hg, show liftW a s 0=(1:ℝ) from (by simp [liftW]),one_mul] at hv; exact hv
    exact ⟨mul_nonneg (wpos ..|>.le) h.1,fun i hi=>by refine (le_trans ?_ (mul_le_mul_of_nonneg_left (h.2 i hi) (wpos ..|>.le))); unfold lump; rw [← sheen]; exact shiny _ fun m hm=>(mul_le_mul_of_nonneg_right (he m) (abs_nonneg (Whisk.read x m f))).trans_eq (mul_assoc ..)⟩
lemma stock (ha:0 ≤ a)(h:Vault j {z} a s p x f B) (hx:Vault j {z} a s p x g t): Vault j {z} a s p x (f*g) (2^p*(B*t)):=by
    refine ⟨mul_nonneg (by positivity) (mul_nonneg h.1 hx.1),fun i hi=>?_⟩; let v(T:List Bool):=lump j {z} a s (parts true T) x f*lump j {z} a s (parts false T) x g; have he(T:List Bool)(he:T.length=i): v T ≤ B*t:=by
        exact mul_le_mul (h.2 _ ((part_le ..).trans (he.trans_le hi))) (hx.2 _ ((part_le ..).trans (he.trans_le hi))) (lump.nonneg ..) h.1
    have hz : lump j {z} a s i x (f*g) ≤liftW a s (separation z z)* Yarn i v:=by exact Whisk.wired j {z} x ha (show ({z}:Finset _) ⊆ {z}∪{z} from Finset.subset_union_left) (mem_singleton_self z) (mem_singleton_self _)
    rw [separation_self, show liftW a s 0=1 from (by simp [liftW]),one_mul] at hz; refine (hz.trans (shiny i he)).trans ?_; rw [total_books,Fintype.card_bool,Nat.cast_ofNat]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hi) (mul_nonneg h.1 hx.1)
lemma VaultC (c : ℝ) : Vault j {z} a s p x (MvPolynomial.C c) |c|:=by
    refine ⟨abs_nonneg _,fun i _=>?_⟩; cases i
    · unfold lump; rw [twillz,rate]; change spread j {z} a s [] *|eval x (MvPolynomial.C c)| ≤ _; have hx: Whisk.extent {z}=0:=Nat.eq_zero_of_le_zero (Whisk.yard (by simp)); simp [Whisk.spread, Whisk.zone, hx,liftW] -- Pay
    next i _=> refine le_trans (b:=0) ?_ (abs_nonneg _); rw [lump,twilled,sum_eq_zero]; intro k _; unfold rate; simp_rw [read_next,pderiv_C,_root_.map_zero,abs_zero,mul_zero]; exact spool i
lemma looks (ha:0≤a)(h:Vault j {z} a s p x f B): |eval x f|≤ B:=by
    have h':= h.2 0 (Nat.zero_le _); rw [lump,twillz,rate] at h'; exact (le_mul_of_one_le_left (abs_nonneg _) (w_start ha s _)).trans h'
lemma across (F: View σ)(h:Vault j {z} a s p x f B)(ha:0≤ a) (hh:‖F-x‖ ≤ b)(ht:f.totalDegree ≤ p) (q:ℕ):Vault j {z} a s q F f (B*(1+b)^(p+1)):=by
     have hp:0 ≤ b:=le_trans (norm_nonneg _) hh; exact ⟨mul_nonneg h.1 (by positivity),fun i _=> (Bakery.crests (spice_fund ha ht h hp i) (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hh)))⟩
end YM.MSbar.Bout
