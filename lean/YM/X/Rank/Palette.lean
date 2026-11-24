import YM.Next.MAXWELL.Statistic
import YM.Next.MAXWELL.Flavor
import YM.Next.RANK.GaussLeg
import YM.Next.RANK.GaussTags
/-!
# Separating the flavor and color indices of the free Wick algebra

Linear polynomial variable changes here on the **on-shell** towers.
Staging auxiliary for the nondegeneracy theorem for nested position conditions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Rank
open Function Set Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial
open scoped BigOperators Classical
variable {G : Gauge} {j l : ℕ} {p : Gauge.Simple G}

abbrev Ax (j : ℕ) := Fin (Module.finrank ℝ (Flavor j))
def ax (j : ℕ) := Module.finBasis ℝ (Flavor j)
abbrev Style := (j : ℕ) × Ax j
abbrev Key (G : Gauge) := Style × G.ColorIndex
abbrev Poly (G : Gauge) := Next.Rank.Normal.poly (Key G)

def ink (k : Key G) : Probe G k.1.1 := flavor k.1.1 k.2 (ax k.1.1 k.1.2)
abbrev hue (G : Gauge) (j : ℕ) (i : Ax j) (c : G.ColorIndex) : Key G := (⟨j,i⟩,c)

def nib (k : Key G) : Slot G →₀ ℂ :=
  ∑ i, Finsupp.single (⟨k.1.1,i⟩ : Slot G) ((ink k (Maxwell.frame G k.1.1 i) : ℝ) : ℂ)
def send (G : Gauge) := Next.Rank.Normal.exchange (nib (G:=G))

lemma nib_eval (f : Slot G → ℂ) (k : Key G) :
    Finsupp.linearCombination ℂ f (nib k) = ∑ i, ↑(ink k (Maxwell.frame G k.1.1 i))*f ⟨k.1.1,i⟩ := by
  simp [nib, smul_eq_mul]
lemma send_X (k : Key G) : send G (X k)= bit (ax k.1.1 k.1.2) k.2 := by
  unfold send; rw [exchange_x]; unfold bit symbol; simp [glyph,nib,C_mul',ink]

def pen (c : G.ColorIndex) : Flavor j →ₗ[ℝ] Poly G where
  toFun w := ∑ i : Ax j, C (((ax j).coord i w : ℝ) : ℂ)*X (hue G j i c)
  map_add' u v := by simp [_root_.map_add,Finset.sum_add_distrib,add_mul]
  map_smul' t w := by
    simp only [_root_.map_smul, RingHom.id_apply, smul_eq_mul, Complex.ofReal_mul,_root_.map_mul,mul_assoc]
    rw [← Finset.mul_sum]
    exact (MvPolynomial.C_mul' ..).trans (RCLike.real_smul_eq_coe_smul _ _).symm

lemma penned (i : Ax j) (c : G.ColorIndex) : pen c (ax j i)=X (hue G j i c) := by
  change ∑ k : Ax j, _ =_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp
  intro y _ hy; simp [hy]
lemma send_pen (w : Flavor j) (c : G.ColorIndex) :
    send G (pen (j:=j) c w)=bit w c := by
  obtain ⟨L,h⟩ := symbol_linear (G:=G) j
  let M := ((send G).toLinearMap.restrictScalars ℝ).comp (pen (G:=G) (j:=j) c)
  change M w=bit w c
  have hL:M=L.comp (flavor j c) := by
      apply (ax j).ext; intro i; change send G (pen (j:=j) c ((ax j) i)) = _
      rw [penned,send_X]; exact (congr_fun h _).symm
  rw [hL]; exact congr_fun h _

def blendP (G : Gauge) (j : ℕ) : Probe G j →ₗ[ℝ] Poly G where
  toFun p := ∑ c : G.ColorIndex, pen c (flavor_pick p c)
  map_add' p q := by
    conv_lhs => arg 2; intro c; rw [show flavor_pick (p+q) c= flavor_pick p c + flavor_pick q c from rfl]
    simp [_root_.map_add, Finset.sum_add_distrib]
  map_smul' t p := by
    conv_lhs => arg 2; intro c; rw [show flavor_pick (t • p) c=t • flavor_pick p c from rfl]
    simp [_root_.map_smul, Finset.smul_sum]

def paint (G : Gauge) : WickPol G →ₐ[ℂ] Poly G := aeval fun i => blendP G i.1 (coordinateLeg i)
lemma painted (w : Probe G j) : paint G (symbol j w)=blendP G j w := by
  have hh : (∑ i, w (Maxwell.frame G j i) • coordinateLeg (⟨j,i⟩ : Slot G)) = w := by
    apply LinearMap.ext; intro v
    conv_rhs => rw [← (Maxwell.frame G j).sum_repr v]
    simp only [_root_.map_sum,map_smul,smul_eq_mul]
    change (∑ i, w (Maxwell.frame G j i) • ((Maxwell.frame G j).coord i)) v = _
    rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl; intro i _; exact mul_comm ..
  conv_rhs => rw [← hh]; simp only [_root_.map_sum,map_smul]
  simp_rw [symbol,_root_.map_sum, MvPolynomial.C_mul',map_smul,paint, aeval_X]
  refine Finset.sum_congr rfl ?_; intro i _; exact (RCLike.real_smul_eq_coe_smul _ _).symm
lemma paint_bit (w : Flavor j)(c : G.ColorIndex) : paint G (bit w c)=pen c w := by
  unfold bit; rw [painted]
  change ∑ i : G.ColorIndex, _ = _
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ _)]
  · exact congr_arg (pen c) (LinearMap.ext (fun v => tasted w c v))
  intro i _ hi
  have h: flavor_pick (flavor (G:=G) j c w) i=0 := by
    apply LinearMap.ext; intro u; change w (faceMap j _ (fill j (unitColor G i) _)) = 0
    rw [which]; simp [unitPaint,Ne.symm hi]
  rw [h,_root_.map_zero]

lemma send_paint : (send G).comp (paint G) = AlgHom.id .. := by
  ext1 i -- MvPolynomial ext
  rw [AlgHom.comp_apply,show X i= _ from (Maxwell.symbol_coordinate i).symm,divide,_root_.map_sum, _root_.map_sum]; simp_rw [paint_bit,send_pen]; rfl
lemma paint_send : (paint G).comp (send G) = AlgHom.id .. := by
  ext1 i; rw [AlgHom.comp_apply,send_X, paint_bit, penned]; rfl
@[simp] lemma sendPaint (p : WickPol G) : send G (paint G p)=p := DFunLike.congr_fun send_paint p
@[simp] lemma paintSend (p : Poly G) : paint G (send G p)=p := DFunLike.congr_fun paint_send p
lemma full_poly (p q : WickPol G) (h : paint G p=paint G q) : p=q := by simpa only [sendPaint] using congr_arg (send G) h

end YM.PositionX.Rank
