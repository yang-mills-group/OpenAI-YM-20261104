import YM.FVA2.GrassSlice
/-!
# One Wick Gaussian on both sectors of the based quotient modes

Slots = arbitrary real coordinates of `FVA2.Wilson.Field` and one c,barc pair per
root-tangent coordinate. Differentiation order matters. Include all components,
including zeros of K on unfed modes. Equivalently a pullback law independent of
choice of any realizing Fourier plates and sqrt matrices. We do *not* assume
thermodynamic bounds on this compression.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Chart
open Function Finset Filter Set Metric MeasureTheory TreeBasis Trans
open Wilson Based GaussianScore MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare MS.Plane MS.Landau MS.Koszul
open Modes
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

namespace PairCoords
abbrev Slot (U J:Type) := U ⊕ (J ⊕ J)
abbrev φ {U J} (x:Slot U J) : Bool:=x.isRight
abbrev gaugeMode {G:Gauge}{n:Side}(x:Wilson.Field G n):= coverL G n ((plan G n).L x)
abbrev c {U J:Type}(j:J):Slot U J:= Sum.inr (Sum.inl j)
abbrev bar {U J:Type}(j:J):Slot U J:= Sum.inr (Sum.inr j)

variable {U J:Type}{G:Gauge}{n:Side}
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
def dualB (j:J) := (poisson G n).symm (b.coord j)
-- basis indexed on *rooted* vertices, sent to mean-zero after inversion lift
def ghostC (j:J) := siteCover G n (b j)
def kField (j:J) : Edge (Site n)→ G.Color:= - coverL G n (d G (rim n) (dualB b j))

def plugIn : Slot U J→ Pos G n→ℝ
| .inl i,(((some j,false),a),x)=> Trans.xMode G x j a (m i)
| .inr (.inl i),(((none,false),a),x)=> ghostC b i x a
| .inr (.inr i),(((some j,true),a),x)=> kField b i (x,j) a
| _,_=>0
abbrev mkPlug : Slot U J→Pos G n→ℂ:=fun i j=> (plugIn m b i j:ℝ)
lemma lawful : MS.Cylinder.Tie σbranch φ (mkPlug m b) := by
     intro i j h; rcases i with ⟨⟨⟨_|i,_|_⟩,a⟩,x⟩ <;> rcases j with _|⟨_|_⟩ <;> ( first| rfl| (unfold mkPlug plugIn at h; exact False.elim (h Complex.ofReal_zero)))

-- generic half-covariance from symmetric H (stored full here)
section form
variable (Y:Grain U)
def major (Y : Grain U) : Grain (Slot U J)
| .inl i,.inl j=> Y i j / 2
| .inr (.inl i),.inr (.inr j)=> if i=j then (2:ℂ)⁻¹ else 0
| .inr (.inr i),.inr (.inl j)=> if j=i then -(2:ℂ)⁻¹ else 0
| _,_=>0
lemma rule (h:∀ i j,Y i j=Y j i): Cog.Sym φ (major (J:=J) Y):= by
    rintro (i|⟨a|u⟩) (j|⟨b|v⟩)
    all_goals simp only [φ,Sum.isRight, cross_false, cross_false',cross_true, major,mul_zero,one_mul] <;> first| exact congr_arg (·/2) (h i j)| rw [neg_one_mul]; split <;> simp
lemma order : Clear (φ (U:=U) (J:=J)) (major Y):= by
    rintro (i|⟨a|u⟩) (j|⟨b|v⟩) h <;> first | rfl | exact (h rfl).elim
lemma cost_even (p q : U): Chill (major Y (J:=J)) (.inl p) (.inl q)= Y p q := by unfold Chill major; ring
lemma cost_c (j:J) (x:Slot U J): Chill (major Y) (c j) x= if x=bar j then 1 else 0:= by
    rcases x with _|⟨b|b⟩ <;> simp only [Chill,major,bar, reduceCtorEq,↓reduceIte, mul_zero, Sum.inr.injEq]; by_cases h:j=b <;> simp [*,Ne.symm] -- h orientation
end form
variable (hn:_root_.Even n.val)
abbrev gram (p q:U):ℂ := ((Trans.price G hn).wick (m.coord p) (m.coord q):ℝ)
abbrev Currency : Grain (Slot U J) := major (gram m hn) -- hn order?

variable [Fintype U][Fintype J]
local notation "K" => Currency m (J:=J) hn
omit [Fintype U] [Fintype J] in
lemma proper : Cog.Sym φ (K):= rule _ (fun i j=> congr_arg _ (Trans.price_turn G hn (m.coord i) (m.coord j)))

private lemma basis_μ (A B : Module.Dual ℝ (Wilson.Field G n)): ∑ i:U,∑ j:U, gram m hn i j*((A (m i):ℂ)*(B (m j):ℂ)) = ((Trans.price G hn).wick A B:ℝ) := by
  let P := Trans.price G hn; let g(i j:U):ℝ:= P.wick (m.coord i) (m.coord j); let x:= P.inverse A
  have he (v:Wilson.Field G n)(P:Module.Dual ℝ (Wilson.Field G n)): ∑ j:U,(m.coord j v)*P (m j)= P v:= by
       simp_rw [show ∀ j:U,(m.coord j v)*P (m j)=P (m.coord j v • m j) from fun j=> Eq.symm (map_smul ..),← map_sum,show ∑ j:U,m.coord j v • m j=v from m.sum_repr v]
  have hx:A=∑ i:U,A (m i) • m.coord i := LinearMap.ext (fun v=> by rw [LinearMap.sum_apply]; simp only [LinearMap.smul_apply,smul_eq_mul]; nth_rw 1 [← he v A]; exact Finset.sum_congr rfl (fun i _=>mul_comm ..)) -- potential recursive rewrite A v
  suffices hv : ∑ i:U, ∑ j:U,g i j * (A (m i)*B (m j)) = P.wick A B by exact_mod_cast hv
  unfold g Law.wick
  conv_rhs => rw [hx,map_sum,map_sum]; -- only A inside?
  simp_rw [map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro i _; simp_rw [mul_left_comm _ (A _), ← Finset.mul_sum, he]
lemma paymentA (x y : Site n) (i j : Axis) (a b' : G.ColorIndex) :
 Chill (induceK (mkPlug m b) (K)) (Bos i a,x) (Bos j b',y) = Chill (cov G n true) (Bos i a,x) (Bos j b',y):= by
    rw [induce_chill]; simp_rw [Fintype.sum_sum_type];
    simp only [mkPlug,Bos,plugIn, Complex.ofReal_zero, zero_mul,mul_zero,Finset.sum_const_zero,add_zero,cost_even]; rw [basis_μ, Trans.image_eq G hn y j b' x i a, Trans.price_turn] -- image_eq y x direction implicit hn
lemma paymentC (x y : Site n) (j : Axis) (a b' : G.ColorIndex) :
 Chill (induceK (mkPlug m b) (K)) (SiteC a,x) (KV j b',y) = Chill (cov G n true) (SiteC a,x) (KV j b',y):= by
    rw [induce_chill]; simp_rw [Fintype.sum_sum_type]
    simp only [mkPlug,SiteC,KV,ghost,anti, plugIn, Complex.ofReal_zero, zero_mul, mul_zero,Finset.sum_const_zero,zero_add,add_zero];
    rw [pairG G n y a b x j b']; rw [Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i hi; rw [ Finset.sum_eq_single i ]; rotate_left
    · intro j hj he; rw [show Chill (K) (c i) (bar j)=0 from (cost_c _ i (bar j)).trans (if_neg (by simpa only [bar,Sum.inr.injEq] using he))]; simp
    · simp
    rw [show Chill (K) (c i) (bar i)=1 from (cost_c _ i (bar i)).trans (if_pos rfl),one_mul, Complex.ofReal_mul]; rfl

lemma reflectChill (x y:Pos G n)(h : Chill (cov G n true) x y= Chill (induceK (mkPlug m b) (K)) x y):
     Chill (cov G n true) y x=Chill (induceK (mkPlug m b) (K)) y x:= by
   unfold cov at *; rw [traceS y x (h:=induce_symm (basisM G n) (basis_tie G n) _  (Near.paySym true)), h, ← traceS y x (h:= induce_symm (mkPlug m b) (lawful m b) _ (proper m hn))] -- orientation

private lemma kills_parity {p:Sector (Pos G n)} {A: Grain (Pos G n)} (hp:Clear p A)(i j: Pos G n)(h:p i≠p j): Chill A i j=0 := by by_cases h0:A i j=0; rw [Chill,h0,mul_zero]; exact (h (hp _ _ h0)).elim
lemma oppositeP (x y:Pos G n)(h : σbranch x≠ σbranch y):
     Chill (cov G n true) x y=Chill (induceK (mkPlug m b) (K)) x y:= by
   exact (kills_parity (A:=cov G n true) (induce_clear _ (basis_tie G n) _ (Near.zeroM true)) x y h).trans ( (kills_parity (induce_clear (mkPlug m b) (lawful m b) _ (order _)) x y h).symm )
lemma no_source (x:Site n)(a:G.ColorIndex)(p:Pos G n) :
     Chill (cov G n true) (Bfield a,x) p=Chill (induceK (mkPlug m b) (K)) (Bfield a,x) p := by
   have h (j:Slot U J): mkPlug m b j (Bfield a,x) = 0:= by rcases j with i|⟨j|k⟩ <;> exact Complex.ofReal_zero
   rcases p with ⟨⟨⟨_ | i, _ | _⟩,b'⟩,t⟩ <;> ( rw [cov_among _ _ _ _ _ (fun _ => rfl), induce_chill]; simp_rw [ h,zero_mul,mul_zero,Finset.sum_const_zero] )
private lemma zero_ghost (x y:Site n) (a a':G.ColorIndex) :
     Chill (induceK (mkPlug m b) (K)) (SiteC a,x) (SiteC a',y) = 0 := by rw [induce_chill]; simp_rw [Fintype.sum_sum_type]; simp [mkPlug,plugIn,Currency,Chill,major] -- handle III
private lemma zero_bar (x y:Site n) (a a':G.ColorIndex)(i j:Axis) :
     Chill (induceK (mkPlug m b) (K)) (KV i a,x) (KV j a',y) = 0 := by rw [induce_chill]; simp_rw [Fintype.sum_sum_type]; simp [mkPlug, plugIn, Currency,Chill,major]

theorem compress : cov G n true= induceK (mkPlug m b) (Currency m (J:=J) hn) := by
   funext x y; apply mul_left_cancel₀ (show (2:ℂ)≠0 from (by norm_num)); change Chill (cov G n true) x y= Chill (induceK _ _) x y
   rcases x with ⟨⟨⟨_|i, _|_⟩,a⟩,x⟩ <;> rcases y with ⟨⟨⟨_|j,_|_⟩,a'⟩,y⟩ 
   · exact (cov_among (SiteC a) (SiteC a') x y true (fun _ => rfl)).trans (zero_ghost m b hn x y a a').symm
   · exact reflectChill m b hn (Bfield a',y) (SiteC a,x) (no_source m b hn y a' (SiteC a,x))
   · exact oppositeP m b hn (SiteC a,x) (Bos j a',y) (fun h=>Bool.noConfusion h)
   · exact (paymentC m b hn x y j a a').symm
   · exact no_source m b hn x a (SiteC a',y)
   · exact no_source m b hn x a (Bfield a',y)
   · exact no_source m b hn x a (Bos j a',y)
   · exact no_source m b hn x a (KV j a',y)
   · exact oppositeP m b hn (Bos i a,x) (SiteC a',y) (fun h=>Bool.noConfusion h)
   · exact reflectChill m b hn (Bfield a',y) (Bos i a,x) (no_source m b hn y a' (Bos i a,x))
   · exact (paymentA m b hn x y i j a a').symm
   · exact oppositeP m b hn (Bos i a,x) (KV j a',y) (fun h=>Bool.noConfusion h)
   · exact reflectChill m b hn (SiteC a',y) (KV i a,x) (paymentC m b hn y x i a' a).symm
   · exact reflectChill m b hn (Bfield a',y) (KV i a,x) (no_source m b hn y a' (KV i a,x))
   · exact oppositeP m b hn (KV i a,x) (Bos j a',y) (fun h=>Bool.noConfusion h)
   · exact (cov_among (KV i a) (KV j a') x y true (fun _ => rfl)).trans (zero_bar m b hn x y a a' i j).symm
end PairCoords
end YM.FVA2
