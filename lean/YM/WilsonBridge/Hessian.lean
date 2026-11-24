import YM.WilsonBridge.OrbitWard

/-!
# Quadratic system on the actual quotient log links

Vertex rank conventions in the MS.Puff algebra (H positive sign of *energy*).
This is the full independent quotient-position matrix before gauge fixing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open PertExtension Orb
open MS Native Bare Focus Koszul Lattice Filter Function Finset
open MS.Book Book.Convolve Cylinder Cylinder.Taylor FreeBV
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
local notation "P"=> Position.Parity G n
local notation "ΠB" => Position.Bracket G n
local notation "L"=> Position.Letter G n
local notation "W"=> actionW G n
local notation "ν"=> Focus.launch (Position.glow G n) (colorTerm G (BasedSite n)) generator
local notation "S"=> mask 2 (actionW G n)

-- note not assuming even yet. k may denote root.
def chargeX (i:Gluon G n) (j:Ghost G n) : ℝ:= projector i (generator j 0)
def hessian (G:Gauge) (n:Side): E G n →L[ℝ] E G n →L[ℝ] ℝ:= - fderiv ℝ (fderiv ℝ (exponent G n)) 0
def costH (i j:Gluon G n) := hessian G n (priv i) (priv j)

lemma orbit_hessian (F H:E G n) : hessian G n F H=hessian G n H F := congr_arg Neg.neg ((expGerm G n).isSymmSndFDerivAt_of_omega F H)
lemma image_charge (A:E G n) : ∑ i:Gluon G n, projector i A • priv i=A := Native.frame _ -- for green
lemma stamp (j:Ghost G n): ∑ i:Gluon G n, chargeX i j • priv i=generator j 0:= Native.frame _
lemma gradient (j:Ghost G n) (e:OEdge n): generator j 0 e= siteField n G.Color (priv j) (Position.endAt e)-siteField n G.Color (priv j) e.val.1 := Maurer.volt_zero _

-- K gauge column has exactly one linear ghost term; includes tree and non-tree links.
lemma DK (j:Gluon G n) : D (k j) W=stone (Position.glow G n) generator j:= by
  unfold actionW Sourced
  have he : Bonded.Lifted (ΠB) ν:= Focus.lifting (Position.glow G n) _ generator (Position.winds.smooth)
  rw [map_add, ink_off (Position.glow G n).e0 (i:=k j) rfl]; change 0+D ((ΠB).dual (.inl j)) _= _
  rw [he.acted]; change 0+(1:ℂ) • _ = _; rw [one_smul,zero_add]; rfl
lemma D_B (j:Ghost G n) : D (b j) W=(-1:ℂ) • shadow (focus G n) (colorTerm G (BasedSite n)) j:= by
  unfold actionW Sourced
  have he : Bonded.Lifted (ΠB) ν:= Focus.lifting (Position.glow G n) _ generator (Position.winds.smooth)
  rw [map_add, ink_off (Position.glow G n).e0 (i:=b j) rfl]; change 0+D ((ΠB).dual (.inr j)) _ = _
  rw [he.acted,zero_add]; rfl

lemma product_one {V:Type} {p: Sector V} (i:V) (F H:Raw V ℂ) :
    product p F H [i]=F [i]*H [] + F []*H [i] := by
  rw [D_eval i (product p F H), D_product,Pi.add_apply,nil_product,nil_product]
  simp [at_D]
lemma hanging_two (i j:Gluon G n⊕Ghost G n) : Bonded.hung (ΠB) ν [(ΠB).plain i,(ΠB).plain j]=0:= by
  unfold Bonded.hung; rw [Finset.sum_apply]; apply Finset.sum_eq_zero; intro q _
  have z: D ((ΠB).plain i) (atLetter ((ΠB).dual q) (R:=ℂ))=0 := unheard _ ((ΠB).diff i q)
  rw [Pi.smul_apply, D_eval _ (product P _ _), D_product,z,map_zero,LinearMap.zero_apply, zero_add,
    product_one, Koszul.at_sign,Koszul.at_sign, notNamed _ ((ΠB).diff j q)]; change _ • (_ * 0 * _ + _*0*_) = _; ring -- smul?

lemma value_H (i j:Gluon G n) : W [a i,a j]= - (costH i j:ℂ) := by
    change ink _ _ _ + _= _
    rw [show (ΠB).hung ν [a i,a j]=0 from hanging_two (.inl i) (.inl j), add_zero]
    let f := exponent G n; change ((layer (priv j) (layer (priv i) f) 0:ℝ):ℂ)=-((-( fderiv ℝ (fderiv ℝ f) 0 _ _ ):ℝ):ℂ)
    unfold layer
    rw [((expGerm G n|>.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)|>.hasFDerivAt.clm_apply (hasFDerivAt_const (priv i) _) |>.fderiv)]; simp; exact neg_inj.mp (orbit_hessian (priv j) (priv i))
lemma spark_spec (i:Ghost G n) : spark (focus G n) i=atLetter (c i):= rfl
lemma value_X (i:Gluon G n) (x:Letter G n) : W [k i,x]= ∑ j:Ghost G n, (chargeX i j:ℂ) * atLetter (c j) [x] := by
    change D (k i) (actionW G n) [x]= _; rw [DK, stone, Finset.sum_apply]
    apply Finset.sum_congr rfl; intro j _; rw [product_one, spark_spec]
    change atLetter _ [x] * (chargeX i j:ℂ) + 0 * _ = _; ring
lemma value_L (i:Ghost G n)(x:Letter G n): W [b i,x]=0:= by
    change D (b i) W [x]=_; rw [D_B, shadow]; simp only [Pi.smul_apply,Finset.sum_apply, product_one, spark_spec]; simp [atLetter] -- consecutive sums

def kinetic (G:Gauge)(n:Side) : Kinetics (Gluon G n) (Ghost G n) where
    X:=fun i j => chargeX i j
    H:=fun i j=> costH i j
    sym i j:= congr_arg (fun x:ℝ=>(x:ℂ)) (orbit_hessian (priv i) (priv j))

lemma blocks : (kinetic G n).Blocks S := by
    let T:= kinetic G n; have hv x y : mask 2 (actionW G n) [x,y]=actionW G n [x,y] := enough _ (by simp)
    have hx (i:L) : D i S=∑ j:L, W [i,j] • atLetter j:= by rw [Swirl.playbill (rankMod _ 2)]; simp_rw [hv]
    have he (i:Gluon G n)(j:Ghost G n) : W [k i,c j]=(chargeX i j:ℂ) := by rw [value_X,Finset.sum_eq_single_of_mem j (mem_univ _)]; rw [speaks,mul_one]; exact fun i' _ ht=> by rw [notNamed _ (by simpa [c] using (Ne.symm ht)), mul_zero]
    have hn (i:Gluon G n)(j:L)(h:∀ j':Ghost G n,j≠ c j') : W [k i,j]=0 := by rw [value_X]; exact Finset.sum_eq_zero fun _ _=>by rw [notNamed _ (h _),mul_zero]
    have ht (i:Gluon G n⊕Ghost G n) (j:Ghost G n) : W [(ΠB).plain i,c j]=0 := by
        unfold actionW Sourced; change ink _ _ _+_=_
        rw [show (ΠB).hung ν [(ΠB).plain i,c j]=0 from hanging_two i (.inr j),add_zero]
        exact congr_fun (ink_off (glow G n).e0 (i:=c j) rfl (layer _ (exponent G n))) ([]:List L) -- annotation
    have hw (i j:L) : W [i,j]= cross (P i) (P j)*W [j,i] := master.smoothW [] i j _
    have A (i:L) : D i S=((∑ j:Gluon G n,W [i,a j] • atLetter (a j)) +(∑ j:Ghost G n,W [i,c j] • atLetter (c j))) + ((∑ j:Gluon G n,W [i,k j] • atLetter (k j)) +(∑ j:Ghost G n,W [i,b j] • atLetter (b j))) := by rw [hx]; change (∑ i:Letters _ _, _)=_; rw [Fintype.sum_sum_type]; simp only [Fintype.sum_sum_type]
    have ht' (i:Gluon G n)(j:Ghost G n): W [a i,c j]=0:= ht (.inl i) j
    refine ⟨fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_⟩
    · change _= ∑ j:Ghost G n,(chargeX i j:ℂ) • _; rw [A]
      have Za j: W [k i,a j]=0:= hn i _ (fun _=> by simp [a,c])
      have Zk j: W [k i,k j]=0:= hn i _ (fun _=> by simp [k,c])
      have Zb j: W [k i,b j]=0:= hn i _ (fun _=> by simp [b,c])
      simp_rw [he i, Za, Zk, Zb,zero_smul, Finset.sum_const_zero,add_zero,zero_add]
    · change _ = -(∑ j:Gluon G n,(costH i j:ℂ) • atLetter (a j)); rw [A]
      have HH j : W [a i,k j]=0 := by rw [hw _ _, hn j (a i) (fun _=> by simp [a,c]), mul_zero]
      simp_rw [ ht' i, value_H i, neg_smul, Finset.sum_neg_distrib, HH, hw (a i) (b _), value_L, mul_zero,zero_smul, Finset.sum_const_zero, add_zero ]
    · change _ = -(∑ j:Gluon G n,(chargeX j i:ℂ) • atLetter (k j)); rw [A]
      have hC (j:Ghost G n) : W [c i,c j]=0 := ht (.inr i) j
      simp_rw [hC,hw (c i) (a _),hw (c i) (b _),hw (c i) (k _), ht', value_L, he, show ∀ j:Gluon G n, cross (P (c i)) (P (k j))=-(1:ℂ) from fun _=>rfl, mul_zero, neg_one_mul,neg_smul, Finset.sum_neg_distrib,zero_smul, Finset.sum_const_zero, add_zero,zero_add]
    rw [hx]; simp_rw [value_L,zero_smul,Finset.sum_const_zero]
end YM.WilsonBridge.Based.Position
