import YM.XSpace.Braid
/-!
# Symbolic reduction of the triangle to terms graded by slots at the b mark
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Graph3
open Function Set Filter Lattice Trace Chart2 Next.Rank.Normal Outline Contraction Stall Mu MvPolynomial Finsupp Pages Chiral
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}{n d e:ℕ}
abbrev col (a b:Line G) := (↑(handshake a b):ℂ)
def Ξ (a:Line G):Module.End ℂ (Stamp G):= (D (bake a)).toLinearMap
lemma ξ_comm (a b:Line G)(p:Stamp G): Ξ a (Ξ b p)=Ξ b (Ξ a p):= slit_slit ..
lemma ξ_mul (a:Line G)(p q:Stamp G): Ξ a (p*q)=p*Ξ a q+Ξ a p*q:=by change D _ _=_; rw [(D (bake a)).leibniz]; change _ + q*_=_; rw [mul_comm q]; rfl
lemma ξ_tie (a:Line G)(p q:Stamp G): Ξ a (tie G p q)=tie G (Ξ a p) q+ tie G p (Ξ a q):= jet ..
@[simp] lemma ξ_zero (a:Line G)(z:ℂ): Ξ a (C z)=0:= slit_C ..
@[simp] lemma ξ_1 (a:Line G): Ξ a (1:Stamp G)=0:=by rw [← map_one (C : ℂ→+* Stamp G),ξ_zero]
@[simp] lemma ξ_harp (a b:Line G) : Ξ a (harp b)= C (col b a):= played ..
lemma ξ_rule (a:Line G){p:Stamp G}(h:Hom p (n+1)): Hom (Ξ a p) n:= slit_degree h _
lemma ξ_low (a:Line G){p:Stamp G}(h: p∈DegZ (UnitIndex G) (n+1)): Ξ a p∈ DegZ (UnitIndex G) n:= slanted h _
lemma ξ_end (a:Line G){p:Stamp G}(h:p∈ DegZ (UnitIndex G) 0): Ξ a p=0:=by obtain ⟨z,rfl⟩:=Pages.shroud h; apply ξ_zero
abbrev peek (G:Gauge) := Mu.scalar G
lemma peek_centers : peek G=aeval (0:Bone G ℤ→ℂ):=by unfold peek Mu.scalar pit; congr 1
lemma high (p:Stamp G)(hl:Hom p n)(he:n≠0): peek G p=0:=by rw [peek_centers]; exact strand hl he
@[simp] lemma peek_leg (a:Line G): peek G (harp a)=0:= high _ (strongs ..) one_ne_zero
@[simp] lemma peek_C (a:ℂ): peek G (C a)=a:= by simp [peek]
-- turn to discrete ordinary Gaussian self population
abbrev F2 (g:Gauge) (p q:Stamp g):= peek g (tie g p q)
def binds (a: Stamp G): Module.Dual ℂ (Stamp G):=(peek G).toLinearMap ∘ₗ tie G a
lemma clasp (a b:Stamp G): binds a b=F2 G a b:=rfl
lemma bound_up (a b:Stamp G): F2 G a b= F2 G b a:= congr_arg (peek G) (Mu.flip ..)
lemma ζ_hop (L: Line G)(p q: Stamp G): F2 G (harp L*p) q= F2 G p (Ξ L q):=by unfold F2; rw [cross_rule,map_add,map_mul,peek_leg, zero_mul,zero_add];rfl
lemma ζ_line (L:Line G)(p:Stamp G): F2 G (harp L) p=peek G (Ξ L p):=by nth_rw 1 [← mul_one (harp L)]; rw [ζ_hop, F2, one_tie]
lemma ζ_two (a b: Line G)(p:Stamp G): F2 G (harp a*harp b) p= peek G (Ξ b (Ξ a p)):= by rw [ζ_hop,ζ_line]
lemma ζ_pair (a b x y: Line G): F2 G (harp a*harp b) (harp x*harp y)= col x a*col y b+ col x b*col y a:=by rw [ζ_two]; simp only [ξ_mul, map_add, map_mul,ξ_harp,ξ_zero,zero_mul,mul_zero,peek_C,map_zero,zero_add,add_zero]; ring
private lemma γ_cross (s:UnitIndex G→₀ℕ)(k:ℂ):∀ (v:ℕ) (p:Stamp G), Hom p v → Volume s≠v→ F2 G (monomial s k) p =0:=by
  apply Extra.FD.per_factor s
  · intro v p hp hv; have ht : C (σ:=UnitIndex G) k=k • 1:= by rw [← C_mul',mul_one]
    change peek G (tie G (C k) p)=0; rw [ht,map_smul,LinearMap.smul_apply, one_tie,map_smul, high p hp (fun h=> hv (h ▸ (map_zero (weight ..)))),smul_zero]
  intro t i h v p hp hv; rw [volume_fee] at hv; rw [monomial_add_single,pow_one,← harps, mul_comm, ζ_hop]; cases v with
    | zero=> rw [ξ_end _ (hom_g hp),F2,map_zero,map_zero]
    | succ v=> exact h v _ (ξ_rule _ hp) (by omega)
lemma γ_between (p q:Stamp G)(h:Hom p n)(H:Hom q d)(he:n ≠ d): F2 G p q=0:= by rw [bound_up,← clasp,p.as_sum,map_sum]; exact Finset.sum_eq_zero fun i hi=> (clasp ..).trans ((bound_up ..).trans (γ_cross i _ d q H (fun H=> he ((h (MvPolynomial.mem_support_iff.mp hi)).symm.trans H))))

abbrev F3 (p q r:Stamp G):=F2 G p (tie G q r)
lemma ζ_value (p q r:Stamp G): F3 p q r=JetGauge.E (root G) (freeze p*(freeze q*freeze r)):=by rw [F3,F2, counts,out,out]
lemma f3_swap (p q r:Stamp G): F3 p q r=F3 q p r:=by rw [ζ_value,ζ_value,mul_left_comm]
lemma f3_last (p q r:Stamp G): F3 p q r=F3 p r q:=by rw [ζ_value,ζ_value,mul_comm (freeze q)]
lemma rotate_right (p q r:Stamp G): F3 p q r=F3 r p q:=by rw [f3_last p,f3_swap]

lemma second (x y: Line G): Ξ x (harp y*harp y)= (2*col y x) • harp y:=by rw [ξ_mul,ξ_harp,mul_comm _ (C _),C_mul', two_mul,add_smul]
lemma angles (p q: Stamp G)(x:Line G) : Ξ x (Ξ x (tie G p q))= tie G p (Ξ x (Ξ x q))+ (2:ℂ) • tie G (Ξ x p) (Ξ x q)+ tie G (Ξ x (Ξ x p)) q:=by rw [ξ_tie,map_add,ξ_tie,ξ_tie,two_smul]; abel
lemma pp (p q: Stamp G)(x:Line G): F3 p q (harp x*harp x)= F2 G p (Ξ x (Ξ x q)) + 2*F2 G (Ξ x p) (Ξ x q)+ F2 G (Ξ x (Ξ x p)) q:=by rw [rotate_right,F3,ζ_two,angles p q]; simp only [map_add,map_smul,F2];rfl
lemma p22 (p q: Stamp G)(a:Line G)(h:Hom p 3)(H:Hom q 3): F3 p q (harp a*harp a)= 2 * F2 G (Ξ a p) (Ξ a q):=by rw [pp,γ_between _ _ h (ξ_rule _ (ξ_rule _ H)) (by decide),γ_between _ _ (ξ_rule _ (ξ_rule _ h)) H (by decide),zero_add,add_zero]
lemma ψ_angles (p:Stamp G)(x y:Line G): F3 p (harp x*harp x) (harp y*harp y)=
    peek G (Ξ x (Ξ x (Ξ y (Ξ y p)))) + (4 * col x y)*peek G (Ξ x (Ξ y p))+(2*col x y^2)*peek G p:=by
  have he: Ξ y (Ξ y (harp x*harp x))=(2*col x y^2) • (1:Stamp G):=by rw [second,map_smul,ξ_harp,← C_mul',← C_mul',mul_one, ← map_mul C,mul_assoc,pow_two]
  rw [pp,he,second,← clasp, ← clasp (Ξ y p), map_smul, map_smul]; simp only [clasp]; rw [bound_up (Ξ y p), ζ_line, bound_up (Ξ y _),ζ_two]; rw [F2,tie_one]; simp only [smul_eq_mul]; ring
end YM.XSpace.Graph3
