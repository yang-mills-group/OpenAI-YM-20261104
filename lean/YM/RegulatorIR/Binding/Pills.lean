import YM.RegulatorIR.Diagram.Spokes
import YM.RegulatorIR.Cluster.Poster

/-! Reading packaging and constants. Noncanonical Laurent accounting only on
external profiles -- never absorbed into the vacuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open Finset PowerSeries Diagram Budget Budget.Packet Budget.Layer Budget.Tuple Function Diagram.Formal
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {R:Type}[CommRing R] [Algebra ℝ R]

private lemma pillows (f g:R⟦X⟧)(n:ℕ): ((n.factorial:ℝ))⁻¹ • (f+g)^n=∑ i∈antidiagonal n,(((i.1.factorial:ℝ))⁻¹ • f^i.1)*((i.2.factorial:ℝ)⁻¹ • g^i.2):=by
 rw [(Commute.all f g).add_pow', Finset.smul_sum]; apply sum_congr rfl; intro i hi;rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
 let a:= i.1; let b:= i.2; have hv:n-a=b:=by have H:= mem_antidiagonal.mp hi; unfold a b;omega
 rw [smul_mul_assoc,mul_smul_comm,smul_smul]
 apply congr_arg (fun k:ℝ=> k • _)
 have H : (n.choose a:ℝ)*(a.factorial:ℝ)*(b.factorial:ℝ)=(n.factorial:ℝ):=by rw [← hv];exact_mod_cast Nat.choose_mul_factorial_mul_factorial (show a≤ n by have := mem_antidiagonal.mp hi; unfold a; omega)
 change (n.factorial:ℝ)⁻¹*(n.choose a:ℝ)=(a.factorial:ℝ)⁻¹*(b.factorial:ℝ)⁻¹; field_simp; linarith
private lemma terms_bill {f g:R⟦X⟧}(h:coeff 0 f=0)(hh:coeff 0 g=0){i j n:ℕ}(hv:n < i+j): coeff n ((((i.factorial:ℝ)⁻¹) • f^i)* (((j.factorial:ℝ)⁻¹) • g^j))=0:=by
 rw [coeff_mul];apply sum_eq_zero;intro x hx; have H:=mem_antidiagonal.mp hx;rw [coeff_smul, coeff_smul]; by_cases he:x.1 < i
 · rw [high_order h he]; simp
 rw [high_order hh (show x.2<j by omega)]; simp
lemma timble_exp {f g:R⟦X⟧}(h: coeff 0 f=0)(hh: coeff 0 g=0): expo (f+g)=expo f*expo g:=by
 ext1 n; rw [expo_any (show coeff 0 (f+g)=0 from by rw [map_add,h,hh,add_zero]) (show n≤n from le_rfl)]
 have hx: coeff n (expo f*expo g)=coeff n (truncP f n* truncP g n):=by rw [coeff_mul,coeff_mul];apply sum_congr rfl;intro i hi; have hp:= mem_antidiagonal.mp hi; rw [expo_any h (show i.1 ≤ n by omega), expo_any hh (show i.2 ≤ n by omega)]
 rw [hx]; let p(x:ℕ×ℕ):= ((x.1.factorial:ℝ)⁻¹ • f^x.1)*((x.2.factorial:ℝ)⁻¹ • g^x.2)
 let S:= range (n+1)
 rw [show truncP f n* truncP g n= ∑ i∈S ×ˢ S,p i by unfold truncP p; rw [Finset.sum_product]; rw [Finset.sum_mul];apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]]
 rw [truncP];simp_rw [pillows]; rw [← Finset.sum_biUnion]; simp only [map_sum]; apply sum_subset
 · intro i hi;obtain ⟨b,hb,he⟩:= Finset.mem_biUnion.mp hi;have hx:= mem_range.mp hb; have he:= mem_antidiagonal.mp he;exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
 · intro i _ hv; apply terms_bill h hh; by_contra! hc;exact hv (mem_biUnion.mpr ⟨i.1+i.2, mem_range.mpr (by omega), mem_antidiagonal.mpr rfl⟩)
 intro i _ j _ hx; exact Finset.disjoint_left.mpr (fun a ha hb=> hx ((mem_antidiagonal.mp ha).symm.trans (mem_antidiagonal.mp hb)))

variable {I J:Type}[Fintype I][Fintype J]{r e:ℕ}
def flavor (r:ℕ)(w:I→ℝ)(T:Orders I) := PowerSeries.map (Diagram.emphasis w).toRingHom (rated (fun i=>i+r) T)
def pulp (T:Orders I)(e r:ℕ): Packet I r := if r=0 then 0 else T e r
lemma flavor_lo (r:ℕ)(w:I→ℝ)(T:Orders I)(e): coeff e (flavor r w T)=MvPolynomial.eval w (packed (T e) (e+r)):=by rw [flavor,PowerSeries.coeff_map,rated_v]; exact language ..
lemma flavor_offer (d:I↪J)(T:Orders I)(w:J→ℝ): flavor r w (Cluster.present d T)=flavor r (w ∘ d) T:=by ext1 i; rw [flavor_lo,flavor_lo]; unfold packed; rw [map_sum,map_sum]; exact sum_congr rfl (fun j _=> Diagram.offer_render d _ _)
lemma flavor_add (T V:Orders I)(w:I→ℝ):flavor r w (T+V)=flavor r w T+flavor r w V:=by ext1 i; rw [map_add,flavor_lo,flavor_lo,flavor_lo,Pi.add_apply,pack_add,map_add]
lemma flavor_collect (d:J↪I)(T:Orders I)(K:Layer I I)(w:J→ℝ): flavor r (announce K (dilute d w)) T=flavor r w (collectO d K T):= (collect_formula d K T w _).symm
lemma flavor_dark (T:Orders I) (h:T 0=0) (w:I→ℝ): coeff 0 (flavor r w T)=0:= by rw [flavor_lo,h,show packed _ _=0 from ?_,map_zero]; simp [packed]
omit [Fintype I] in
def out (T:Orders I):ℝ⟦X⟧:= PowerSeries.mk fun i=> T i 0 Fin.elim0
lemma flavor_pulp (T:Orders I)(w:I→ℝ): flavor r w T= flavor r w (pulp T)+out T:=by
 ext1 i; rw [map_add,flavor_lo,flavor_lo,out,coeff_mk]; unfold packed;rw [map_sum,map_sum];let R:= range (i+r+1)
 have hi : 0∈range (i+r+1):=mem_range.mpr (by omega)
 simp_rw [← Finset.sum_erase_add _ _ hi]; simp only [pulp]; rw [ite_true, render_zero,map_zero,add_zero]; apply congr_arg₂ (·+·)
 · exact sum_congr rfl fun j hj=>by rw [if_neg (ne_of_mem_erase hj)]
 rw [render]; simp [word]; congr
omit [Fintype I] in
lemma flavor_bare (T:Orders I)(K:Layer I I)(h:Vacuum T) : ceaseHeat K T true 0=0:=by
 ext1 i; rw [Pi.zero_apply]; unfold ceaseHeat heated; apply Finset.sum_eq_zero; intro r _; by_contra! hv; exact lt_irrefl 0 (heated_cap K T h true 0 i r hv).1
end YM.RegulatorIR.Binding
